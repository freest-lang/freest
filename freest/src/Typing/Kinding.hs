{- |
Module      :  Typing.Kinding
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional kinding algorithm.
-}
{-# LANGUAGE FlexibleContexts #-}

module Typing.Kinding 
  ( synth
  , check
  , KindingCtx
  )
where

import Syntax.Base 
import Syntax.Kind as Kind
import Syntax.Type as Type
import Typing.Base

import Data.Map as Map
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State
import Control.Monad.State (MonadState)

type KindingCtx = Map Variable Kind

synth :: KindingCtx -> Type -> TypingExcept Kind
synth = undefined

check :: MonadState TypingState m => KindingCtx -> Type -> Kind -> m ()
check = undefined