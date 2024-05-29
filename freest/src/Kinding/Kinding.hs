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