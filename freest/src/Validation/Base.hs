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
import qualified Data.Map as Map
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Control.Arrow ((>>>))
import Syntax.Substitution (subs)
import qualified Data.List.NonEmpty as NE

data ValidationState
  = ValidationState
    { errors       :: [Error]
    , kindCtx      :: Map.Map Identifier K.Kind
    , typeEqs      :: Map.Map Identifier ([(Variable, K.Kind)], T.Type)
    }

type Validation = ExceptT Error (State ValidationState)

putError :: MonadState ValidationState m => a -> Error -> m a
putError x e = do
  modify \s -> s{errors=errors s++[e]}
  return x

putError_ :: MonadState ValidationState m => Error -> m ()
putError_ = putError ()

lookupKind :: Identifier -> Validation K.Kind
lookupKind i =
  gets (Map.lookup i . kindCtx)
  >>= maybe (throwE (TypeOutOfScope (getSpan i) i)) pure

lookupType :: Identifier -> [T.Type] -> Validation T.Type
lookupType i ts =
  gets (Map.lookup i . typeEqs) >>= \case 
    Nothing    -> throwE (TypeOutOfScope (getSpan i) i)
    Just (aks, t) 
      | n >  m -> pure $ T.App s (T.Name (getSpan i) i) (NE.fromList ts)
      | n == m -> pure t'
      | n <  m -> pure $ T.App s t' (NE.fromList $ drop n ts)
      where n  = length aks
            m  = length ts
            t' = foldr (uncurry subs) t (zip (map fst (take m aks)) ts)
            s  = spanFromTo i (last ts)
