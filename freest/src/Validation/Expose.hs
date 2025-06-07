module Validation.Expose 
  ( kindArrow
  , functionOrPolyExp
  , function
  , polyExp
  , internalChoice
  , output
  , input
  , onExpression
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

functionOrPolyExp :: Located e => e -> T.Type -> Validation T.Type
functionOrPolyExp e t = do
  ds <- gets typeDecls
  case normalise ds t of
    t'@(T.AppArrow s m u v) -> pure t'
    t'@(T.AppForall s aks u) -> pure t'
    _ -> throwE (ExposeError (getSpan e) "a function or polymorphic expression" t)

function :: Located e => e -> T.Type -> Validation (K.Multiplicity, T.Type, T.Type)
function e t = do
  ds <- gets typeDecls
  case normalise ds t of
    t'@(T.AppArrow s m u v) -> pure (m, u, v)
    _ -> throwE (ExposeError (getSpan e) "a function" t)

polyExp :: Located e => e -> T.Type -> Validation ([(Variable, K.Kind)], T.Type)
polyExp e t = do -- named it `polyExp` because `forall` is a keyword (and aligns better with error)
  ds <- gets typeDecls
  case normalise ds t of
    t'@(T.AppForall s aks u) -> pure (aks, u)
    _ -> throwE (ExposeError (getSpan e) "a polymorphic expression" t)

internalChoice :: Located e => e -> T.Type -> Identifier -> Validation T.Type
internalChoice e t i = do
  ds <- gets typeDecls
  case normalise ds t of
    T.AppLinChoice s T.Out ts -> 
        case lookup i ts of
            Just t' -> return t'
            Nothing -> throwE (IllegalChoice s i t)
    _ -> throwE (ExposeError (getSpan e) "an internal choice" t)

output :: Located e => e -> T.Type -> Validation (T.Type, T.Type)
output = message T.Out

input :: Located e => e -> T.Type -> Validation (T.Type, T.Type)
input = message T.In

message :: Located e => T.Polarity -> e -> T.Type -> Validation (T.Type, T.Type)
message p e t = do
  ds <- gets typeDecls
  case normalise ds t of
    T.AppMessage s _ p' u                 | p == p' -> return (u, T.Skip s)
    T.AppSemi _ (T.AppMessage _ _ p' u) v | p == p' -> return (u, v)
    _ -> throwE (ExposeError (getSpan e) "an output type" t)

onExpression :: Validation a -> E.Exp -> Validation a
onExpression v e = catchE v $ \case 
  (ExposeError s msg t) -> 
    throwE (ExposeError (getSpan e) (msg ++ " for expression `"++ show e++"`") t)
  e -> throwE e
