module Validation.Base where

import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import qualified Syntax.Module as M
import qualified Syntax.Type as T
import UI.Error

import Control.Monad.State (State, MonadState, modify, gets, foldM, runState)
import qualified Data.Map.Strict as Map
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Control.Arrow ((>>>))
import Data.Bifunctor (second)
import Syntax.Substitution (subs)
import qualified Data.List.NonEmpty as NE

type Lambda t = ([Variable], t)
type TypeDeclMap = Map.Map Identifier (Lambda T.Type)
type ConsDeclMap = Map.Map Identifier [T.Type]
type DataDeclMap = Map.Map Identifier (Lambda ConsDeclMap)

data ValidationState
  = ValidationState
    { errors    :: [Error]
    , kindCtx   :: Map.Map Identifier K.Kind
    , typeDecls :: TypeDeclMap
    , dataDecls :: DataDeclMap
    , consDecls :: Map.Map Identifier (Identifier, [Variable], [T.Type])
    }
  
emptyValidationState :: ValidationState
emptyValidationState = ValidationState 
  { errors    = []
  , kindCtx   = Map.empty
  , typeDecls = Map.empty
  , dataDecls = Map.empty
  , consDecls = Map.empty
  }

buildValidationState :: M.Module -> ValidationState
buildValidationState m = ValidationState -- TODO: traverse module once.
  { errors    = []
  , kindCtx   = Map.fromList (M.kindSigs m)
  , typeDecls = Map.fromList (M.typeDecls m)
  , dataDecls = Map.fromList (map (\(i,(aks,cds)) -> (i,(aks,Map.fromList cds))) $ M.dataDecls m)
  , consDecls = Map.fromList (concatMap (\(i,(as,cds)) -> map (second (i,as,)) cds) $ M.dataDecls m)
  }

type Validation = ExceptT Error (State ValidationState)

runValidation :: ValidationState -> Validation t -> Either [Error] t
runValidation s v =
  let (x, ValidationState{errors}) = runState (runExceptT v) s
  in case x of
    Left e -> Left (errors ++ [e])
    Right x' | null errors -> Right x'
             | otherwise   -> Left errors

putError :: MonadState ValidationState m => a -> Error -> m a
putError x e = do
  modify \s -> s{errors=errors s++[e]}
  return x

putError_ :: MonadState ValidationState m => Error -> m ()
putError_ = putError ()

lookupKind :: Identifier -> Validation K.Kind
lookupKind i = do 
  ctx <- gets kindCtx
  case ctx Map.!? i of
    Just k  -> return k
    Nothing -> throwE (TypeOutOfScope (getSpan i) i)

lookupTName :: Identifier -> [T.Type] -> Validation T.Type
lookupTName i ts =
  gets (Map.lookup i . typeDecls) >>= \case 
    Nothing    -> throwE (TypeOutOfScope (getSpan i) i)
    Just (aks, t) 
      | n >  m -> pure $ T.AppTName (getSpan i) i ts
      | n == m -> pure t'
      | n <  m -> pure $ T.smartApp s t' (drop n ts)
      where n  = length aks
            m  = length ts
            t' = foldr (uncurry subs) t (zip (take m aks) ts)
            -- TODO: Can we have? (zip takes the length of the shorter list)
            -- t' = foldr (uncurry subs) t (zip aks ts)
            -- TODO: if yes, then we may as well write (with a proper import)
            -- t' = subsAll aks ts t
            s  = spanFromTo i (last ts)
