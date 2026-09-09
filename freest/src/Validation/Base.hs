module Validation.Base
  ( ValidationState(..)
  , Validation
  , emptyValidationState
  , runValidation
  , incCounter
  , freshInternal
  , addKindConstraint
  , addKindBinding
  , addMultEquation
  , addBaseKindConstraint
  , addCondSeqMult
  , takeKindState
  , Ground(..)
  , Obligation
  , checkWhenSolved
  , setKindSolution
  , dischargeObligations
  , addUnDefault
  , unfold
  )
where

import Syntax.Base
import Data.Set qualified as Set
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Provenance ( Origin )
import Validation.LocalInference.BaseKinds ( BaseKindConstraint )
import Validation.LocalInference.Solution ( KindSolution, resolveKind, resolveMult, resolveType )
import Syntax.Declarations qualified as D
import Syntax.Type.Internal qualified as T
import Syntax.Type.Kinded qualified as TK
import UI.Error
import Validation.Substitution ( subs )
import Compiler.Bug ( internalError )

import Control.Monad.State ( State, MonadState, modify, gets, foldM, runState )
import Data.Map.Strict qualified as Map
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Data.Bifunctor ( second )
import Data.List.NonEmpty qualified as NE

-- | The validation state. Keeps track of errors. Also stores declarations
-- for easy lookup, but these are not supposed to change.
data ValidationState
  = ValidationState
    { errors  :: [Error]
    , counter :: Int
    -- | Subkinding constraints @(o, k1, k2)@ meaning @k1 <: k2@, gathered during
    -- kinding when a solvable variable is involved, and solved together.
    , kindConstraints :: [(Origin, K.Kind, K.Kind)]
    -- | Direct whole-kind-variable bindings (e.g. a variable operand resolved to
    -- a proper kind), seeding the unifier's substitution.
    , kindBindings :: Map.Map Variable K.Kind
    -- | Multiplicity equations @(o, m1, m2)@ meaning @m1 = m2@, emitted by
    -- multi-operand formers (e.g. the join of @;@).
    , multEquations :: [(Origin, K.Multiplicity, K.Multiplicity)]
    -- | BaseKind constraints (meet/join/sub) emitted by multi-operand formers.
    , baseKindConstraints :: [BaseKindConstraint]
    -- | Channel-conditional @;@ multiplicities @(o, υ₁, φ, m₁, m₂)@ meaning
    -- @φ = if υ₁ = Channel then m₁ else m₁ ⊔ m₂@, deferred when the left operand's
    -- baseKind υ₁ is still a variable; discharged once baseKinds are solved.
    , condSeqMults :: [(Origin, K.BaseKind, K.Multiplicity, K.Multiplicity, K.Multiplicity)]
    -- | Multiplicity variables that default to @*@ rather than the top when
    -- nothing constrains them: an output-polarity binder is covariant, so the
    -- most usable choice for its remote consumer is unrestricted.
    , unDefaults :: Set.Set Variable
    -- | Kind-reading checks recorded to run after the solve, most recent first.
    , obligations :: [Obligation]
    -- | The solution kinding computed, kept for 'dischargeObligations'.
    -- 'Nothing' until kinding has run.
    , kindSolution :: Maybe KindSolution
    }

-- | The empty validation state. No errors or declarations.
emptyValidationState :: ValidationState
emptyValidationState = ValidationState
  { errors  = []
  , counter = 0
  , kindConstraints = []
  , kindBindings = Map.empty
  , multEquations = []
  , baseKindConstraints = []
  , condSeqMults = []
  , unDefaults = Set.empty
  , obligations = []
  , kindSolution = Nothing
  }

-- | The validation monad. Combines exceptions of type 'Error' with state of 
-- type 'ValidationState'.
type Validation = ExceptT Error (State ValidationState)

-- | Increment the fresh internal variable name counter, returning the previous
-- value.
incCounter :: Validation Int
incCounter = do
  c <- gets counter
  modify (\s -> s{counter=succ (counter s)})
  return c

-- | Give a variable a fresh internal name, keeping its external name and span.
freshInternal :: Variable -> Validation Variable
freshInternal x = incCounter >>= \i -> return x{internal = i}

-- | Record a subkinding constraint @k1 <: k2@ to be solved later.
addKindConstraint :: Origin -> K.Kind -> K.Kind -> Validation ()
addKindConstraint o k1 k2 =
  modify \s -> s{kindConstraints = (o, k1, k2) : kindConstraints s}

-- | Bind a whole-kind variable directly (seeds the unifier's substitution).
addKindBinding :: Variable -> K.Kind -> Validation ()
addKindBinding a k =
  modify \s -> s{kindBindings = Map.insert a k (kindBindings s)}

-- | Record a multiplicity equation @m1 = m2@.
addMultEquation :: Origin -> K.Multiplicity -> K.Multiplicity -> Validation ()
addMultEquation o m1 m2 =
  modify \s -> s{multEquations = (o, m1, m2) : multEquations s}

-- | Record a baseKind constraint.
addBaseKindConstraint :: BaseKindConstraint -> Validation ()
addBaseKindConstraint c =
  modify \s -> s{baseKindConstraints = c : baseKindConstraints s}

-- | Record a multiplicity variable that defaults to @*@ (see 'unDefaults').
addUnDefault :: Variable -> Validation ()
addUnDefault φ = modify \s -> s{unDefaults = Set.insert φ (unDefaults s)}

-- | How a deferred check grounds the kinds it captured: the kind solution's
-- substitution, at each of the sorts a check may need to read.
data Ground = Ground
  { groundType :: TK.KindedType -> TK.KindedType
  , groundKind :: K.Kind -> K.Kind
  , groundMult :: K.Multiplicity -> K.Multiplicity
  -- | For a check that unfolds type declarations, as type equivalence does.
  , groundDecls :: D.KindedTypeDecls -> D.KindedTypeDecls
  }

-- | A check that reads kinds and only reports: it feeds nothing back into the
-- types being built, so it may be recorded now and run once kinds are ground.
-- The 'Ground' it is handed at discharge is what makes the kinds it captured
-- readable.
type Obligation = Ground -> Validation ()

-- | Record a kind-reading check to run once the solve is in, when the kinds it
-- would read are still variables. 'dischargeObligations' runs it.
checkWhenSolved :: Obligation -> Validation ()
checkWhenSolved chk = modify \s -> s{obligations = chk : obligations s}

-- | Record the solution kinding computed, for the deferred checks to read.
setKindSolution :: KindSolution -> Validation ()
setKindSolution sol = modify \s -> s{kindSolution = Just sol}

-- | Run every recorded check against the kind solution, in the order recorded,
-- and clear the queue.
dischargeObligations :: Validation ()
dischargeObligations = gets obligations >>= \case
  []  -> return ()
  obs -> gets kindSolution >>= \case
    Nothing  -> internalError "kind obligations recorded before the solve"
    Just sol -> do
      modify \s -> s{obligations = []}
      let g = Ground (resolveType sol) (resolveKind sol) (resolveMult sol)
                     (Map.map (second (resolveType sol)))
      mapM_ ($ g) (reverse obs)

-- | Record a channel-conditional @;@ multiplicity (see 'condSeqMults').
addCondSeqMult :: Origin -> K.BaseKind -> K.Multiplicity -> K.Multiplicity -> K.Multiplicity -> Validation ()
addCondSeqMult o bk φ m1 m2 =
  modify \s -> s{condSeqMults = (o, bk, φ, m1, m2) : condSeqMults s}

-- | Read and clear all accumulated kinding constraints and bindings.
takeKindState :: Validation
  ( Map.Map Variable K.Kind
  , [(Origin, K.Kind, K.Kind)]
  , [(Origin, K.Multiplicity, K.Multiplicity)]
  , [BaseKindConstraint]
  , [(Origin, K.BaseKind, K.Multiplicity, K.Multiplicity, K.Multiplicity)]
  , Set.Set Variable )
takeKindState = do
  s <- gets id
  modify \st -> st{kindConstraints = [], kindBindings = Map.empty, multEquations = [], baseKindConstraints = [], condSeqMults = [], unDefaults = Set.empty}
  return (kindBindings s, kindConstraints s, multEquations s, baseKindConstraints s, condSeqMults s, unDefaults s)

-- | Run a validation procedure from an initial state, returning either:
-- 
--     * a list of errors, if any was encountered;
--     * the result of the validation procedure, otherwise.
runValidation :: ValidationState -> Validation t -> Either [Error] t
runValidation s v =
  let (x, ValidationState{errors}) = runState (runExceptT v) s
  in case x of
    Left e -> Left (errors ++ [e])
    Right x' | null errors -> Right x'
             | otherwise   -> Left errors

unfold :: D.KindedTypeDecls -> Identifier -> TK.KindedType
unfold tdecls i =
  case tdecls Map.!? i of
    Just (_, u)  -> u
    Nothing -> internalError $ "name " ++ show i ++ " not in type declaration map"

-- getKind :: M.KindedModule -> Identifier -> K.Kind
-- getKind mod i =
--   case M.kindSigs mod Map.!? i of
--     Just k  -> k
--     Nothing -> internalError $ "RenameValidation.Base..getKind: name " ++ show i ++ " not in kind signature map"
  
