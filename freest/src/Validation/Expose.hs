module Validation.Expose
  ( kindArrow
  , function
  , arrow
  , internalChoice
  , output
  , input
  , outputType
  , inputType
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
import Control.Monad.State ( get, gets )

kindArrow :: K.Kind -> ([K.Kind], K.Kind)
kindArrow (K.Arrow _ k1 k2) = first (k1:) (kindArrow k2)
kindArrow k = ([], k)

function :: Located e => e -> T.Type -> Validation T.Type
function e t = do
  vs <- get
  case normalise vs t of
    t'@(T.AppArrow s m u v) -> pure t'
    t'@(T.AppForall s aks u) -> pure t'
    _ -> throwE (ExposeError (getSpan e) "a function" t)

arrow :: Located e => e -> T.Type -> Validation (K.Multiplicity, T.Type, T.Type)
arrow e t = do
  vs <- get
  case normalise vs t of
    t'@(T.AppArrow s m u v) -> pure (m, u, v)
    _ -> throwE (ExposeError (getSpan e) "a monomorphic function" t)

exists :: Either E.Pat E.Exp -> T.Type -> Validation ([(Variable, K.Kind)], T.Type)
exists poe t = do
  vs <- get
  case normalise vs t of
    t'@(T.AppExists s aks u) -> pure (aks, u)
    _ -> throwE (TypeMismatchExists (getSpan poe) t poe) 

internalChoice :: Located e => e -> T.Type -> Identifier -> Validation T.Type
internalChoice e t i = do
  vs <- get
  case normalise vs t of
    T.AppLinChoice s T.Out its -> 
      case lookup i its of
        Just t' -> return t'
        Nothing -> throwE (IllegalChoice s i t)
    t'@(T.SharedChoice s T.Out its)
      | i `elem` its -> return t'
      | otherwise    -> throwE (IllegalChoice s i t)
    _ -> throwE (ExposeError (getSpan e) "an internal choice channel" t)

output :: Located e => e -> T.Type -> Validation (T.Type, T.Type)
output = message T.Out

input :: Located e => e -> T.Type -> Validation (T.Type, T.Type)
input = message T.In

message :: Located e => T.Polarity -> e -> T.Type -> Validation (T.Type, T.Type)
message p e t = do
  vs <- get
  case normalise vs t of
    T.AppMessage s K.Lin p' u                    | p == p' -> return (u, T.Skip s)
    t'@(T.AppMessage s K.Un  p' u)               | p == p' -> return (u, t')
    T.AppSemi _    (T.AppMessage _ K.Lin p' u) v | p == p' -> return (u, v)
    T.AppSemi _ t'@(T.AppMessage _ K.Un  p' u) v | p == p' -> return (u, t')
    _ -> throwE (ExposeError (getSpan e) msg t)
  where msg = "an " ++ (case p of T.In -> "input"; T.Out -> "output") ++ " channel"

outputType :: Located e => e -> T.Type -> Validation (Variable, K.Kind, T.Type)
outputType = typeMessage T.Out

inputType :: Located e => e -> T.Type -> Validation (Variable, K.Kind, T.Type)
inputType = typeMessage T.In

typeMessage :: Located e => T.Polarity -> e -> T.Type -> Validation (Variable, K.Kind, T.Type)
typeMessage p e t = do
  vs <- get
  case normalise vs t of
    T.AppTypeMsg _ p' a k t' | p == p' -> return (a, k, t')
    _ -> throwE (ExposeError (getSpan e) msg t)
  where msg = "a type-" ++ (case p of T.In -> "input"; T.Out -> "output") ++ " channel"