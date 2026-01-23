module Validation.Expose
  ( kindArrow
  , function
  , arrow
  , internalChoice
  , output
  , input
  )
where

import UI.Error
import Validation.Base
import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Type qualified as T
import Validation.Normalisation ( normalise )

import Data.Bifunctor
import Control.Monad.Trans.Except
import Control.Monad.State ( gets )

kindArrow :: K.Kind -> ([K.Kind], K.Kind)
kindArrow (K.Arrow _ k1 k2) = first (k1:) (kindArrow k2)
kindArrow k = ([], k)

function :: Located e => e -> T.KindedType -> Validation Kinded T.KindedType
function e t = do
  ds <- gets typeDecls
  case normalise ds t of
    t'@T.AppArrow{} -> pure t'
    t'@T.AppForall{} -> pure t'
    _ -> throwE (ExposeError (getSpan e) "a function" t)

arrow :: Located e => e -> T.KindedType -> Validation Kinded (K.Multiplicity, T.KindedType, T.KindedType)
arrow e t = do
  ds <- gets typeDecls
  case normalise ds t of
    T.AppArrow _ _ _ m u v -> pure (m, u, v)
    _ -> throwE (ExposeError (getSpan e) "a monomorphic function" t)

internalChoice :: Located e => e -> T.KindedType -> Identifier -> Validation Kinded T.KindedType
internalChoice e t i = do
  ds <- gets typeDecls
  case normalise ds t of
    T.AppLinChoice s _ _ T.Out its -> 
      case lookup i its of
        Just t' -> return t'
        Nothing -> throwE (IllegalChoice s i t)
    t'@(T.SharedChoice s _ T.Out its)
      | i `elem` its -> return t'
      | otherwise    -> throwE (IllegalChoice s i t)
    _ -> throwE (ExposeError (getSpan e) "an internal choice" t)

output :: Located e => e -> T.KindedType -> Validation Kinded (T.KindedType, T.KindedType)
output = message T.Out

input :: Located e => e -> T.KindedType -> Validation Kinded (T.KindedType, T.KindedType)
input = message T.In

message :: Located e => T.Polarity -> e -> T.KindedType -> Validation Kinded (T.KindedType, T.KindedType)
message p e t = do
  ds <- gets typeDecls
  case normalise ds t of
    T.AppMessage s _ x2 K.Lin p' u                    | p == p' -> return (u, T.Skip s x2)
    t'@(T.AppMessage _ _ _ K.Un  p' u)               | p == p' -> return (u, t')
    T.AppSemi _ _  (T.AppMessage _ _ _ K.Lin p' u) v | p == p' -> return (u, v)
    T.AppSemi _ _ t'@(T.AppMessage _ _ _ K.Un  p' u) _ | p == p' -> return (u, t')
    _ -> throwE (ExposeError (getSpan e) msg t)
  where msg = "an " ++ (case p of T.In -> "input"; T.Out -> "output") ++ " type"
