{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
module Typing.Base where

import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import qualified Syntax.Type as T
import IO.Error

import Control.Monad.State (State, MonadState, modify)
import qualified Data.Map as Map
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except

data TypingState 
  = TypingState{errors :: [Error]}

type Typing = State TypingState

type TypingExcept = ExceptT Error Typing

putError :: MonadState TypingState m => Error -> m ()
putError e = modify \s -> s{errors=errors s++[e]}

type KindCtx = Map.Map Variable K.Kind
type TypeCtx = Map.Map Variable T.Type
