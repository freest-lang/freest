module Validation.Base
  ( ValidationState(..)
  , Validation
  , emptyValidationState
  , runValidation
  , incCounter
  , addKindConstraint
  , addKindBinding
  , addMultEquation
  , addPrekindConstraint
  , addCondSeqMult
  , takeKindState
  , unfold
  )
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Provenance ( Origin )
import Validation.LocalInference.Prekinds ( PrekindConstraint )
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
    -- | Prekind constraints (meet/join/sub) emitted by multi-operand formers.
    , prekindConstraints :: [PrekindConstraint]
    -- | Channel-conditional @;@ multiplicities @(o, υ₁, φ, m₁, m₂)@ meaning
    -- @φ = if υ₁ = Channel then m₁ else m₁ ⊔ m₂@, deferred when the left operand's
    -- prekind υ₁ is still a variable; discharged once prekinds are solved.
    , condSeqMults :: [(Origin, K.Prekind, K.Multiplicity, K.Multiplicity, K.Multiplicity)]
    }

-- | The empty validation state. No errors or declarations.
emptyValidationState :: ValidationState
emptyValidationState = ValidationState
  { errors  = []
  , counter = 0
  , kindConstraints = []
  , kindBindings = Map.empty
  , multEquations = []
  , prekindConstraints = []
  , condSeqMults = []
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

-- | Record a prekind constraint.
addPrekindConstraint :: PrekindConstraint -> Validation ()
addPrekindConstraint c =
  modify \s -> s{prekindConstraints = c : prekindConstraints s}

-- | Record a channel-conditional @;@ multiplicity (see 'condSeqMults').
addCondSeqMult :: Origin -> K.Prekind -> K.Multiplicity -> K.Multiplicity -> K.Multiplicity -> Validation ()
addCondSeqMult o pk φ m1 m2 =
  modify \s -> s{condSeqMults = (o, pk, φ, m1, m2) : condSeqMults s}

-- | Read and clear all accumulated kinding constraints and bindings.
takeKindState :: Validation
  ( Map.Map Variable K.Kind
  , [(Origin, K.Kind, K.Kind)]
  , [(Origin, K.Multiplicity, K.Multiplicity)]
  , [PrekindConstraint]
  , [(Origin, K.Prekind, K.Multiplicity, K.Multiplicity, K.Multiplicity)] )
takeKindState = do
  s <- gets id
  modify \st -> st{kindConstraints = [], kindBindings = Map.empty, multEquations = [], prekindConstraints = [], condSeqMults = []}
  return (kindBindings s, kindConstraints s, multEquations s, prekindConstraints s, condSeqMults s)

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
  
