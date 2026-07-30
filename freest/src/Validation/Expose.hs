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
import Syntax.Declarations qualified as D
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

function :: D.KindedTypeDecls -> E.KindedExp -> T.KindedType -> Validation T.KindedType
function tdecls e t = do
  case normalise tdecls t of
    t'@(T.AppArrow s m u v) -> pure t'
    t'@(T.AppForall s m aks u) -> pure t'
    _ -> throwE (ExposeError (getSpan e) (Right e) "a function" t)

arrow :: D.KindedTypeDecls -> E.KindedExp -> T.KindedType -> Validation (K.Multiplicity, T.KindedType, T.KindedType)
arrow tdecls e t = do
  case normalise tdecls t of
    t'@(T.AppArrow s m u v) -> pure (m, u, v)
    _ -> throwE (ExposeError (getSpan e) (Right e) "a monomorphic function" t)

exists :: D.KindedTypeDecls
       -> Either E.KindedPat E.KindedExp
       -> T.KindedType 
       -> Validation ([(Variable, K.Kind)], T.KindedType)
exists tdecls pe t = do
  case normalise tdecls t of
    t'@(T.AppExists s aks u) -> pure (aks, u)
    _ -> throwE (TypeMismatchExists (getSpan pe) t pe) 

-- | Expose the continuation of an external choice matched by a @&l p@ pattern
-- (linear) or a @*&l p@ pattern (unrestricted). An unrestricted choice makes no
-- progress, so its continuation is the channel itself.
externalChoice :: D.KindedTypeDecls -> K.Multiplicity -> E.KindedPat -> T.KindedType -> Identifier
               -> Validation T.KindedType
externalChoice tdecls m p t i
  | K.isUn m = case normalise tdecls t of
      t'@(T.UnChoice _ T.In ls)               -> pick t' ls
      T.AppSemi _ t'@(T.UnChoice _ T.In ls) _ -> pick t' ls
      _ -> throwE (ExposeError (getSpan p) (Left p) "an unrestricted (`*&`) external choice channel" t)
  | otherwise = case normalise tdecls t of
      T.AppLinChoice _ T.In lts -> case lookup i lts of
        Just ti -> return ti
        Nothing -> throwE (IllegalChoice (getSpan i) i t)
      _ -> throwE (ExposeError (getSpan p) (Left p) "a linear external choice channel" t)
  where
    pick t' ls | i `elem` ls = return t'
               | otherwise   = throwE (IllegalChoice (getSpan i) i t)

-- | Expose the continuation of an internal choice selected by @select l@
-- (linear) or @select_ l@ (unrestricted).
internalChoice :: D.KindedTypeDecls -> K.Multiplicity -> E.KindedExp -> T.KindedType -> Identifier
               -> Validation T.KindedType
internalChoice tdecls m e t i
  | K.isUn m = case normalise tdecls t of
      t'@(T.UnChoice s T.Out ls)               -> pick s t' ls
      T.AppSemi _ t'@(T.UnChoice s T.Out ls) _ -> pick s t' ls
      _ -> throwE (ExposeError (getSpan e) (Right e) "an unrestricted (`*+`) internal choice channel" t)
  | otherwise = case normalise tdecls t of
      T.AppLinChoice s T.Out its ->
        case lookup i its of
          Just t' -> return t'
          Nothing -> throwE (IllegalChoice s i t)
      _ -> throwE (ExposeError (getSpan e) (Right e) "a linear internal choice channel" t)
  where
    pick s t' ls | i `elem` ls = return t'
                 | otherwise   = throwE (IllegalChoice s i t)

-- | Expose the payload and continuation of an input matched by a @?p; q@
-- pattern (linear) or a @*?p; q@ pattern (unrestricted). An unrestricted input
-- makes no progress, so its continuation is the channel itself.
input :: D.KindedTypeDecls -> K.Multiplicity -> Either E.KindedPat E.KindedExp -> T.KindedType
      -> Validation (T.KindedType, T.KindedType)
input tdecls = message tdecls T.In

output :: D.KindedTypeDecls -> K.Multiplicity -> E.KindedExp -> T.KindedType -> Validation (T.KindedType, T.KindedType)
output tdecls m = message tdecls T.Out m . Right

message :: D.KindedTypeDecls -> T.Polarity -> K.Multiplicity -> Either E.KindedPat E.KindedExp -> T.KindedType
        -> Validation (T.KindedType, T.KindedType)
message tdecls p m pe t
  | K.isUn m = case normalise tdecls t of
      t'@(T.AppMessage _ K.Un{} p' u)                | p == p' -> return (u, t')
      T.AppSemi _ t'@(T.AppMessage _ K.Un{} p' u) _  | p == p' -> return (u, t')
      _ -> throwE (ExposeError (getSpan pe) pe (msg ("an unrestricted (`*" ++ sigil ++ "`) ")) t)
  | otherwise = case normalise tdecls t of
      T.AppMessage s K.Lin{} p' u                    | p == p' -> return (u, T.Skip s)
      T.AppSemi _    (T.AppMessage _ K.Lin{} p' u) v | p == p' -> return (u, v)
      _ -> throwE (ExposeError (getSpan pe) pe (msg "a linear ") t)
  where
    msg q = q ++ (case p of T.In -> "input"; T.Out -> "output") ++ " channel"
    sigil = case p of T.In -> "?"; T.Out -> "!"

typeOutput :: D.KindedTypeDecls -> E.KindedExp -> T.KindedType 
           -> Validation (Variable, K.Kind, T.KindedType)
typeOutput tdecls = typeMsg tdecls T.Out . Right

typeInput :: D.KindedTypeDecls -> Either E.KindedPat E.KindedExp -> T.KindedType 
          -> Validation (Variable, K.Kind, T.KindedType)
typeInput tdecls = typeMsg tdecls T.In

typeMsg :: D.KindedTypeDecls -> T.Polarity -> Either E.KindedPat E.KindedExp -> T.KindedType
            -> Validation (Variable, K.Kind, T.KindedType)
typeMsg tdecls p pe t = do
  case normalise tdecls t of
    T.AppQuantS _ p' a k t' | p == p' -> return (a, k, t')
    _ -> throwE (ExposeError (getSpan pe) pe msg t)
  where msg = "a type-" ++ (case p of T.In -> "input"; T.Out -> "output") ++ " channel"

wait :: D.KindedTypeDecls -> E.KindedPat -> T.KindedType -> Validation ()
wait tdecls p t = do
  case normalise tdecls t of
    T.End _ T.In -> return ()
    T.AppSemi _ (T.End _ T.In) _ -> return ()
    _ -> throwE (ExposeError (getSpan p) (Left p) "a `Wait` channel" t)
