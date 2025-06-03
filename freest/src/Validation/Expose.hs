module Validation.Expose 
  ( kindArrow
  , typeArrow
  , function
  , internalChoice
  , output
  , input
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

function :: E.Exp -> T.Type -> Validation (K.Multiplicity, T.Type, T.Type)
function e t = do
  ds <- gets typeDecls
  case normalise ds t of
    T.AppArrow _ m t1 t2 -> pure (m, t1, t2)
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

output :: E.Exp -> T.Type -> Validation (T.Type, T.Type)
output = message T.Out

input :: E.Exp -> T.Type -> Validation (T.Type, T.Type)
input = message T.In

message :: T.Polarity -> E.Exp -> T.Type -> Validation (T.Type, T.Type)
message p e t = do
  ds <- gets typeDecls
  case normalise ds t of
    T.AppMessage s _ p' u                 | p == p' -> return (u, T.Skip s)
    T.AppSemi _ (T.AppMessage _ _ p' u) v | p == p' -> return (u, v)
    _ -> throwE (ExposeError (getSpan e) "an output" (Left e) t)