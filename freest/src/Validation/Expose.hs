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
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as T
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

function :: M.KindedModule -> E.KindedExp -> T.KindedType -> Validation T.KindedType
function mod e t = do
  case normalise mod t of
    t'@(T.AppArrow s m u v) -> pure t'
    t'@(T.AppForall s aks u) -> pure t'
    _ -> throwE (ExposeError (getSpan e) (Right e) "a function" t)

arrow :: M.KindedModule -> E.KindedExp -> T.KindedType -> Validation (K.Multiplicity, T.KindedType, T.KindedType)
arrow mod e t = do
  case normalise mod t of
    t'@(T.AppArrow s m u v) -> pure (m, u, v)
    _ -> throwE (ExposeError (getSpan e) (Right e) "a monomorphic function" t)

exists :: M.KindedModule
       -> Either E.Pat E.KindedExp
       -> T.KindedType 
       -> Validation ([(Variable, K.Kind)], T.KindedType)
exists mod pe t = do
  case normalise mod t of
    t'@(T.AppExists s aks u) -> pure (aks, u)
    _ -> throwE (TypeMismatchExists (getSpan pe) t pe) 

externalChoice :: M.KindedModule -> E.Pat -> T.KindedType -> Identifier -> Validation T.KindedType
externalChoice mod p t i = do
  case normalise mod t of
    T.AppLinChoice _ T.In lts -> case lookup i lts of
      Just ti -> return ti
      Nothing -> throwE (IllegalChoice (getSpan i) i t)
    t'@(T.UnChoice _ T.In ls)
      | i `elem` ls -> return t'
      | otherwise   -> throwE (IllegalChoice (getSpan i) i t)
    (T.AppSemi _ t'@(T.UnChoice _ T.In ls) u)
      | i `elem` ls -> return t'
      | otherwise   -> throwE (IllegalChoice (getSpan i) i t)
    _ -> throwE (ExposeError (getSpan p) (Left p) "an external choice channel" t)

internalChoice :: M.KindedModule -> E.KindedExp -> T.KindedType -> Identifier -> Validation T.KindedType
internalChoice mod e t i = do
  case normalise mod t of
    T.AppLinChoice s T.Out its -> 
      case lookup i its of
        Just t' -> return t'
        Nothing -> throwE (IllegalChoice s i t)
    t'@(T.UnChoice s T.Out its)
      | i `elem` its -> return t'
      | otherwise    -> throwE (IllegalChoice s i t)
    _ -> throwE (ExposeError (getSpan e) (Right e) "an internal choice channel" t)

output :: M.KindedModule -> E.KindedExp -> T.KindedType -> Validation (T.KindedType, T.KindedType)
output mod = message mod T.Out . Right

input :: M.KindedModule -> Either E.Pat E.KindedExp -> T.KindedType -> Validation (T.KindedType, T.KindedType)
input mod = message mod T.In

message :: M.KindedModule -> T.Polarity -> Either E.Pat E.KindedExp -> T.KindedType 
        -> Validation (T.KindedType, T.KindedType)
message mod p pe t = do
  case normalise mod t of
    T.AppMessage s K.Lin p' u                    | p == p' -> return (u, T.Skip s)
    t'@(T.AppMessage s K.Un  p' u)               | p == p' -> return (u, t')
    T.AppSemi _    (T.AppMessage _ K.Lin p' u) v | p == p' -> return (u, v)
    T.AppSemi _ t'@(T.AppMessage _ K.Un  p' u) v | p == p' -> return (u, t')
    _ -> throwE (ExposeError (getSpan pe) pe msg t)
  where msg = "an " ++ (case p of T.In -> "input"; T.Out -> "output") ++ " channel"

typeOutput :: M.KindedModule -> E.KindedExp -> T.KindedType 
           -> Validation (Variable, K.Kind, T.KindedType)
typeOutput mod = typeMsg mod T.Out . Right

typeInput :: M.KindedModule -> Either E.Pat E.KindedExp -> T.KindedType 
          -> Validation (Variable, K.Kind, T.KindedType)
typeInput mod = typeMsg mod T.In

typeMsg :: M.KindedModule -> T.Polarity -> Either E.Pat E.KindedExp -> T.KindedType
            -> Validation (Variable, K.Kind, T.KindedType)
typeMsg mod p pe t = do
  case normalise mod t of
    T.AppQuantS _ p' a k t' | p == p' -> return (a, k, t')
    _ -> throwE (ExposeError (getSpan pe) pe msg t)
  where msg = "a type-" ++ (case p of T.In -> "input"; T.Out -> "output") ++ " channel"

wait :: M.KindedModule -> E.Pat -> T.KindedType -> Validation ()
wait mod p t = do
  case normalise mod t of
    T.End _ T.In -> return ()
    T.AppSemi _ (T.End _ T.In) _ -> return ()
    _ -> throwE (ExposeError (getSpan p) (Left p) "a `Wait` channel" t)
