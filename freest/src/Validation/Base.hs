module Validation.Base
  -- TODO: explicit export list
where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import UI.Error

import Control.Monad.State ( State, gets, runState )
import Data.Map.Strict qualified as Map
import Control.Monad.Trans.Except
import Data.Bifunctor ( second )


-- | Maps @type@ names to their declarations.
type TypeDeclMap x = Map.Map Identifier (T.Type x)
type KindedTypeDeclMap = TypeDeclMap Kinded

-- | Maps @data@ names to their declarations.
type DataDeclMap x = Map.Map Identifier ([(Variable, K.Kind)], ConsDeclMap x)

-- | Maps @data@ constructor names to their declarations.
type ConsDeclMap x = Map.Map Identifier [T.Type x]

-- | The validation state. Keeps track of errors. Also stores declarations
-- for easy lookup, but these are not supposed to change.
data ValidationState x
  = ValidationState
    { errors    :: [Error x]
    , kindSigs  :: Map.Map Identifier K.Kind
    , typeDecls :: TypeDeclMap x
    , dataDecls :: DataDeclMap x 
    , consDecls :: Map.Map Identifier (Identifier, [(Variable, K.Kind)], [T.Type x])
    }

-- | The empty validation state. No errors or declarations.
emptyValidationState :: ValidationState x
emptyValidationState = ValidationState 
  { errors    = []
  , kindSigs  = Map.empty
  , typeDecls = Map.empty
  , dataDecls = Map.empty
  , consDecls = Map.empty
  }

-- | Build an initial validation state from a module, storing its declarations
-- for easy lookup. The resulting state contains no errors.
buildValidationState :: M.Module x -> ValidationState x
buildValidationState m = ValidationState -- TODO: traverse module once.
  { errors    = []
  , kindSigs  = Map.fromList (concatMap (\(is, k) -> map (, k) is) $ M.kindSigs m)
  , typeDecls = Map.fromList (M.typeDecls m)
  , dataDecls = Map.fromList (map (\(i, aks, cds) -> (i, (aks, Map.fromList cds))) $ M.dataDecls m)
  , consDecls = Map.fromList (concatMap (\(i, aks, cds) -> map (second (i, aks, )) cds) $ M.dataDecls m)
  }

-- | The validation monad. Combines exceptions of type 'Error' with state of 
-- type 'ValidationState'.
type Validation x = ExceptT (Error x) (State (ValidationState x))

-- | Run a validation procedure from an initial state, returning either:
-- 
--     * a list of errors, if any was encountered;
--     * the result of the validation procedure, otherwise.
runValidation :: ValidationState x -> Validation x t -> Either [Error x] t
runValidation s v =
  let (x, ValidationState{errors}) = runState (runExceptT v) s
  in case x of
    Left e -> Left (errors ++ [e])
    Right x' | null errors -> Right x'
             | otherwise   -> Left errors

-- | Look up the kind of a @type@ or @data@ name in the validation state.
lookupKind :: Identifier -> Validation x K.Kind
lookupKind i = do 
  ctx <- gets kindSigs
  case ctx Map.!? i of
    Just k  -> return k
    Nothing -> throwE (TypeConsOutOfScope (getSpan i) i)

