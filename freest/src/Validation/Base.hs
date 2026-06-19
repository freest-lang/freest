{- |
Module      :  Validation.Base
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Building blocks shared by the validation phases: the 'Validation' monad
(@ExceptT 'Error' (State 'ValidationState')@), its state and runner,
a fresh-name counter, and the 'unfold' lookup that resolves a 'TName' to
its kinded body via the current module's @typeDecls@ map.
-}
module Validation.Base
  ( ValidationState(..)
  , Validation
  , emptyValidationState
  , runValidation
  , incCounter
  , unfold
  , emit
  , freshMultVar
  , freshPrekindVar
  , freshMult
  , freshPrekind
  , freshKind
  )
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Internal qualified as T
import Syntax.Type.Kinded qualified as TK
import UI.Error
import Validation.Constraint ( Constraint, Constraints )
import Validation.Substitution ( subs )
import Compiler.Bug ( internalError )

import Control.Monad.State ( State, MonadState, modify, gets, foldM, runState )
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Data.Bifunctor ( second )
import Data.List.NonEmpty qualified as NE

-- | The validation state. Keeps errors, a fresh-name counter, and the
-- 'Constraints' gathered during kind inference.
data ValidationState = ValidationState
  { errors      :: [Error]
  , counter     :: Int
  , constraints :: Constraints
  }

-- | The empty validation state. No errors, fresh counter at 0, no constraints.
emptyValidationState :: ValidationState
emptyValidationState = ValidationState
  { errors      = []
  , counter     = 0
  , constraints = Set.empty
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

unfold :: M.KindedModule -> Identifier -> TK.KindedType
unfold mod i =
  case M.typeDecls mod Map.!? i of
    Just (_, u)  -> u
    Nothing -> internalError $ "name " ++ show i ++ " not in type declaration map"

-- | Add a constraint to the validation state.
emit :: Constraint -> Validation ()
emit c = modify $ \s -> s { constraints = Set.insert c (constraints s) }

-- | A fresh multiplicity variable @φₙ@: a 'Variable' named @"φ"@ with a fresh
-- internal index. Use this when you need the raw variable (e.g. on the LHS of
-- a 'JoinMult' constraint); use 'freshMult' when you need it wrapped.
freshMultVar :: Span -> Validation Variable
freshMultVar s = Variable s "φ" <$> incCounter

-- | A fresh prekind variable @ψₙ@: a 'Variable' named @"ψ"@ with a fresh
-- internal index. Use this when you need the raw variable (e.g. on the LHS of
-- a 'MeetPrekind' / 'JoinPrekind' constraint); use 'freshPrekind' when you
-- need it wrapped.
freshPrekindVar :: Span -> Validation Variable
freshPrekindVar s = Variable s "ψ" <$> incCounter

-- | A fresh multiplicity, wrapping a 'freshMultVar' as @Sup s [(ObjLv, φₙ)]@.
freshMult :: Span -> Validation K.Multiplicity
freshMult s = (\v -> K.Sup s [(ObjLv, v)]) <$> freshMultVar s

-- | A fresh prekind, wrapping a 'freshPrekindVar' as @VarPK ψₙ@.
freshPrekind :: Span -> Validation K.Prekind
freshPrekind s = K.VarPK <$> freshPrekindVar s

-- | A fresh proper kind @φₙψₙ@: combines 'freshMult' and 'freshPrekind'.
-- Used to replace a 'K.Var' returned by 'synth' with a proper kind containing
-- fresh multiplicity and prekind variables.
freshKind :: Span -> Validation K.Kind
freshKind s = K.Proper s <$> freshMult s <*> freshPrekind s

-- getKind :: M.KindedModule -> Identifier -> K.Kind
-- getKind mod i =
--   case M.kindSigs mod Map.!? i of
--     Just k  -> k
--     Nothing -> internalError $ "RenameValidation.Base..getKind: name " ++ show i ++ " not in kind signature map"
  
