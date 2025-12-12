module Validation.Expose
  ( kindArrow
  , function
  , arrow
  , externalChoice
  , internalChoice
  , output
  , input
  , typeOutput
  , typeInput
  , wait
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

function :: E.Exp -> T.Type -> Validation T.Type
function e t = do
  vs <- get
  case normalise vs t of
    t'@(T.AppArrow s m u v) -> pure t'
    t'@(T.AppForall s aks u) -> pure t'
    _ -> throwE (ExposeError (getSpan e) (Right e) "a function" t)

arrow :: E.Exp -> T.Type -> Validation (K.Multiplicity, T.Type, T.Type)
arrow e t = do
  vs <- get
  case normalise vs t of
    t'@(T.AppArrow s m u v) -> pure (m, u, v)
    _ -> throwE (ExposeError (getSpan e) (Right e) "a monomorphic function" t)

exists :: Either E.Pat E.Exp -> T.Type -> Validation ([(Variable, K.Kind)], T.Type)
exists pe t = do
  vs <- get
  case normalise vs t of
    t'@(T.AppExists s aks u) -> pure (aks, u)
    _ -> throwE (TypeMismatchExists (getSpan pe) t pe) 

externalChoice :: E.Pat -> T.Type -> Identifier -> Validation T.Type
externalChoice p t i = do
  vs <- get
  case normalise vs t of
    T.AppLinChoice _ T.In lts -> case lookup i lts of
      Just ti -> return ti
      Nothing -> throwE (IllegalChoice (getSpan i) i t)
    t'@(T.SharedChoice _ T.In ls)
      | i `elem` ls -> return t'
      | otherwise   -> throwE (IllegalChoice (getSpan i) i t)
    (T.AppSemi _ t'@(T.SharedChoice _ T.In ls) u)
      | i `elem` ls -> return t'
      | otherwise   -> throwE (IllegalChoice (getSpan i) i t)
    _ -> throwE (ExposeError (getSpan p) (Left p) "an external choice channel" t)

internalChoice :: E.Exp -> T.Type -> Identifier -> Validation T.Type
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
    _ -> throwE (ExposeError (getSpan e) (Right e) "an internal choice channel" t)

output :: E.Exp -> T.Type -> Validation (T.Type, T.Type)
output = message T.Out . Right

input :: (Either E.Pat E.Exp) -> T.Type -> Validation (T.Type, T.Type)
input = message T.In

message :: T.Polarity -> (Either E.Pat E.Exp) -> T.Type -> Validation (T.Type, T.Type)
message p pe t = do
  vs <- get
  case normalise vs t of
    T.AppMessage s K.Lin p' u                    | p == p' -> return (u, T.Skip s)
    t'@(T.AppMessage s K.Un  p' u)               | p == p' -> return (u, t')
    T.AppSemi _    (T.AppMessage _ K.Lin p' u) v | p == p' -> return (u, v)
    T.AppSemi _ t'@(T.AppMessage _ K.Un  p' u) v | p == p' -> return (u, t')
    _ -> throwE (ExposeError (getSpan pe) pe msg t)
  where msg = "an " ++ (case p of T.In -> "input"; T.Out -> "output") ++ " channel"

typeOutput :: E.Exp -> T.Type -> Validation (Variable, K.Kind, T.Type)
typeOutput = typeMessage T.Out . Right

typeInput :: Either E.Pat E.Exp -> T.Type -> Validation (Variable, K.Kind, T.Type)
typeInput = typeMessage T.In

typeMessage :: T.Polarity -> (Either E.Pat E.Exp) -> T.Type -> Validation (Variable, K.Kind, T.Type)
typeMessage p pe t = do
  vs <- get
  case normalise vs t of
    T.AppTypeMsg _ p' a k t' | p == p' -> return (a, k, t')
    _ -> throwE (ExposeError (getSpan pe) pe msg t)
  where msg = "a type-" ++ (case p of T.In -> "input"; T.Out -> "output") ++ " channel"

wait :: E.Pat -> T.Type -> Validation ()
wait p t = do
  vs <- get
  case normalise vs t of
    T.End _ T.In -> return ()
    _ -> throwE (ExposeError (getSpan p) (Left p) "a `Wait` channel" t)