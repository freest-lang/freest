module Validation.Base
  -- TODO: explicit export list
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import UI.Error
import Validation.Substitution ( subs )
import Utils ( internalError )

import Control.Monad.State ( State, MonadState, modify, gets, foldM, runState )
import Data.Map.Strict qualified as Map
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Data.Bifunctor ( second )
import Data.List.NonEmpty qualified as NE

-- | Mapsg @type@ names to their declarations.
type TypeDeclMap = Map.Map Identifier T.Type

-- | Maps @type@ names to their kinds.
type KindSigMap = Map.Map Identifier K.Kind

-- | Maps @data@ names to their declarations.
type DataDeclMap = Map.Map Identifier ([(Variable, K.Kind)], ConsDeclMap)

-- | Maps @data@ constructor names to their declarations.
type ConsDeclMap = Map.Map Identifier [T.Type]

-- | The validation state. Keeps track of errors. Also stores declarations
-- for easy lookup, but these are not supposed to change.
data ValidationState
  = ValidationState
    { errors    :: [Error]
    , kindSigs  :: KindSigMap
    , typeDecls :: TypeDeclMap
    , dataDecls :: DataDeclMap
    , consDecls :: Map.Map Identifier (Identifier, [(Variable, K.Kind)], [T.Type])
    }

-- | The empty validation state. No errors or declarations.
emptyValidationState :: ValidationState
emptyValidationState = ValidationState 
  { errors    = []
  , kindSigs  = Map.empty
  , typeDecls = Map.empty
  , dataDecls = Map.empty
  , consDecls = Map.empty
  }

-- | Build an initial validation state from a module, storing its declarations
-- for easy lookup. The resulting state contains no errors.
buildValidationState :: M.Module -> ValidationState
buildValidationState m = ValidationState -- TODO: traverse module once.
  { errors    = []
  , kindSigs  = Map.fromList (concatMap (\(is, k) -> map (, k) is) $ M.kindSigs m)
  , typeDecls = Map.fromList (M.typeDecls m)
  , dataDecls = Map.fromList (map (\(i, aks, cds) -> (i, (aks, Map.fromList cds))) $ M.dataDecls m)
  , consDecls = Map.fromList (concatMap (\(i, aks, cds) -> map (second (i, aks, )) cds) $ M.dataDecls m)
  }

-- | The validation monad. Combines exceptions of type 'Error' with state of 
-- type 'ValidationState'.
type Validation = ExceptT Error (State ValidationState)

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

-- | Look up the kind of a @type@ or @data@ name in the validation state.
lookupKind :: Identifier -> Validation K.Kind
lookupKind i = do 
  ctx <- gets kindSigs
  case ctx Map.!? i of
    Just k  -> return k
    Nothing -> throwE (TypeConsOutOfScope (getSpan i) i)

getType :: ValidationState -> Identifier -> T.Type
getType vs = unfold $ typeDecls vs

unfold :: TypeDeclMap -> Identifier -> T.Type
unfold td name =
  case td Map.!? name of
    Just u  -> u
    Nothing -> internalError $ "Validation.Base.unfold: name " ++ show name ++ " not in type declaration map"

getKind :: ValidationState -> Identifier -> K.Kind
getKind vs name =
  case kindSigs vs Map.!? name of
    Just k  -> k
    Nothing -> internalError $ "RenameValidation.Base..getKind: name " ++ show name ++ " not in kind signature map"
  
