{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
module Validation.Base where

import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import qualified Syntax.Type as T
import UI.Error

import Control.Monad.State (State, MonadState, modify, gets)
import qualified Data.Map.Strict as Map
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Control.Arrow ((>>>))
import Syntax.Substitution (subs)
import qualified Data.List.NonEmpty as NE

type Lambda t = ([(Variable, K.Kind)], t)
type TypeDeclMap = Map.Map Identifier (Lambda T.Type)
type ConsDeclMap = Map.Map Identifier [T.Type]
type DataDeclMap = Map.Map Identifier (Lambda ConsDeclMap)

data ValidationState
  = ValidationState
    { errors    :: [Error]
    , kindCtx   :: Map.Map Identifier K.Kind
    , typeDecls :: TypeDeclMap
    , dataDecls :: DataDeclMap
    , consDecls :: ConsDeclMap
    }

type Validation = ExceptT Error (State ValidationState)

putError :: MonadState ValidationState m => a -> Error -> m a
putError x e = do
  modify \s -> s{errors=errors s++[e]}
  return x

putError_ :: MonadState ValidationState m => Error -> m ()
putError_ = putError ()

lookupDKind :: Identifier -> [T.Type] -> Validation K.Kind
lookupDKind i ts = undefined

lookupTName :: Identifier -> [T.Type] -> Validation T.Type
lookupTName i ts =
  gets (Map.lookup i . typeDecls) >>= \case 
    Nothing    -> throwE (TypeOutOfScope (getSpan i) i)
    Just (aks, t) 
      | n >  m -> pure $ T.TName (getSpan i) i ts
      | n == m -> pure t'
      | n <  m -> pure $ T.sApp s t' (NE.fromList $ drop n ts)
      where n  = length aks
            m  = length ts
            t' = foldr (uncurry subs) t (zip (map fst (take m aks)) ts)
            s  = spanFromTo i (last ts)
