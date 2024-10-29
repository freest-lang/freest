{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
module Typing.Base where

import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import qualified Syntax.Type as T
import IO.Error

import Control.Monad.State (State, MonadState, modify, gets)
import qualified Data.Map as Map
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except

data TypingState 
  = TypingState
    { errors       :: [Error]
    , types        :: Map.Map Identifier (K.Kind, T.Type)
    }

type Typing = State TypingState

type TypingExcept = ExceptT Error Typing

putError :: MonadState TypingState m => a -> Error -> m a
putError x e = do
  modify \s -> s{errors=errors s++[e]}
  return x

putError_ :: MonadState TypingState m => Error -> m ()
putError_ = putError ()

lookupType :: Identifier -> TypingExcept (K.Kind, T.Type)
lookupType i =
  Map.lookup i <$> gets types >>= \case
    Just kt -> pure kt
    Nothing -> throwE (TypeOutOfScope (getSpan i) i)

type KindCtx = Map.Map Variable K.Kind
type TypeCtx = Map.Map Variable T.Type
