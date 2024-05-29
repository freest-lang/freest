{- |
Module      :  Kinding.Kinding
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional kinding algorithm.
-}

module Kinding.Kinding 
  ( synth
  , KindingCtx
  )
where

import Syntax.Base 
import Syntax.Kind as Kind
import Syntax.Type as Type

import Data.Map as Map


type KindingCtx = Map Variable Kind

synth :: KindingCtx -> Type -> Maybe Kind
synth = undefined