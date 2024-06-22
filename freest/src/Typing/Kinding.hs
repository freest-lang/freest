{- |
Module      :  Typing.Kinding
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional kinding algorithm.
-}

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


type KindingCtx = Map Variable Kind

synth :: KindingCtx -> Type -> Typing Kind
synth = undefined

check :: KindingCtx -> Type -> Kind -> Typing ()
check = undefined