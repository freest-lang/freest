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
  , addUnDefault
  , unfold
  , Staging(..)
  )
where

import Syntax.Base
import Data.Set qualified as Set
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Provenance ( Origin )
import Validation.LocalInference.BaseKinds ( BaseKindConstraint )
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

-- | When the kind solution is applied to the module.
--
-- 'SolveDuringKinding' is today's pipeline: kinding solves and zonks, so typing
-- only ever sees ground kinds. 'SolveAfterTyping' is where the fused pass has to
-- get to, and every check that demands a ground kind fails under it — which is
-- what makes it a measurement (see @test\/prog\/DeferredSpec.hs@) rather than a
-- mode anyone should run.
data Staging = SolveDuringKinding | SolveAfterTyping
  deriving Eq

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
    -- | Whether kinding applies its solution to the module it returns. See
    -- 'Staging'; everything but the deferred-solve harness leaves this alone.
    , staging :: Staging
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
  , staging = SolveDuringKinding
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
  
