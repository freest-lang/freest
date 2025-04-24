module Validation.Expose 
  ( kindArrow
  , typeArrow
  , internalChoice
  )
where

import UI.Error
import Validation.Base
import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Type qualified as T
import Validation.Normalisation ( normalise )

import Data.Functor
import Data.Bifunctor
import Data.Map qualified as Map
import Control.Applicative
import Control.Monad.Trans.Except
import Control.Monad.State ( gets )

kindArrow :: K.Kind -> ([K.Kind], K.Kind)
kindArrow (K.Arrow _ k1 k2) = first (k1:) (kindArrow k2)
kindArrow k = ([], k)

typeArrow :: E.Exp -> T.Type -> Validation T.Type
typeArrow e t = do
  ds <- gets typeDecls
  case normalise ds t of
    t'@T.AppArrow{} -> pure t'
    t'@T.AppForall{} -> pure t' -- TODO: Why T.AppForall only?
    _ -> throwE (ExposeError (getSpan e) "a function" (Left e) t)

internalChoice :: E.Exp -> T.Type -> Identifier -> Validation T.Type
internalChoice e t i = do
  ds <- gets typeDecls
  case normalise ds t of
    T.AppLinChoice s T.Out ts -> 
        case lookup i ts of
            Just t' -> return t'
            Nothing -> throwE (IllegalChoice s i t)
    _ -> throwE (ExposeError (getSpan e) "an internal choice" (Left e) t)
