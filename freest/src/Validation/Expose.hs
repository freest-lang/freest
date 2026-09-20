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
  , externalChoice'
  , message'
  , typeMsg'
  , wait
  )
where

import UI.Error
import Validation.Base
import Syntax.Base
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

function :: D.KindedTypeDecls -> ErrorSite -> T.KindedType -> Validation T.KindedType
function tdecls site t = do
  case normalise tdecls t of
    t'@(T.AppArrow s m u v) -> pure t'
    t'@(T.AppForall s m aks u) -> pure t'
    t' -> throwE (ExposeError site "a function" t t')

arrow :: D.KindedTypeDecls -> ErrorSite -> T.KindedType -> Validation (K.Multiplicity, T.KindedType, T.KindedType)
arrow tdecls site t = do
  case normalise tdecls t of
    t'@(T.AppArrow s m u v) -> pure (m, u, v)
    t' -> throwE (ExposeError site "a monomorphic function" t t')

exists :: D.KindedTypeDecls
       -> ErrorSite
       -> T.KindedType 
       -> Validation ([(Variable, K.Kind)], T.KindedType)
exists tdecls site t = do
  case normalise tdecls t of
    t'@(T.AppExists s aks u) -> pure (aks, u)
    _ -> throwE (TypeMismatchExists (getSpan site) t site) 

-- | Expose the continuation of an external choice matched by a @&l p@ pattern
-- (linear) or a @*&l p@ pattern (unrestricted). An unrestricted choice makes no
-- progress, so its continuation is the channel itself.
externalChoice :: D.KindedTypeDecls -> K.Multiplicity -> ErrorSite -> T.KindedType -> Identifier
               -> Validation T.KindedType
externalChoice tdecls m site t i = case externalChoice' tdecls m t i of
  Just (Just ti) -> return ti
  Just Nothing   -> throwE (IllegalChoice (getSpan i) i t)
  Nothing        -> throwE (ExposeError site msg t (normalise tdecls t))
  where msg | K.isUn m  = "an unrestricted (`*&`) external choice channel"
            | otherwise = "a linear external choice channel"

-- | 'externalChoice' without the failure: 'Nothing' when the type is no such
-- channel, @Just Nothing@ when it is one but offers no such label.
externalChoice' :: D.KindedTypeDecls -> K.Multiplicity -> T.KindedType -> Identifier
                -> Maybe (Maybe T.KindedType)
externalChoice' tdecls m t i
  | K.isUn m = case normalise tdecls t of
      t'@(T.UnChoice _ Neg ls)               -> Just (pick t' ls)
      T.AppSemi _ t'@(T.UnChoice _ Neg ls) _ -> Just (pick t' ls)
      _ -> Nothing
  | otherwise = case normalise tdecls t of
      T.AppLinChoice _ Neg lts -> Just (lookup i lts)
      _ -> Nothing
  where pick t' ls | i `elem` ls = Just t'
                   | otherwise   = Nothing

-- | Expose the continuation of an internal choice selected by @select l@
-- (linear) or @select_ l@ (unrestricted).
internalChoice :: D.KindedTypeDecls -> K.Multiplicity -> ErrorSite -> T.KindedType -> Identifier
               -> Validation T.KindedType
internalChoice tdecls m site t i
  | K.isUn m = case normalise tdecls t of
      t'@(T.UnChoice s Pos ls)               -> pick s t' ls
      T.AppSemi _ t'@(T.UnChoice s Pos ls) _ -> pick s t' ls
      t' -> throwE (ExposeError site "an unrestricted (`*+`) internal choice channel" t t')
  | otherwise = case normalise tdecls t of
      T.AppLinChoice s Pos its ->
        case lookup i its of
          Just t' -> return t'
          Nothing -> throwE (IllegalChoice s i t)
      t' -> throwE (ExposeError site "a linear internal choice channel" t t')
  where
    pick s t' ls | i `elem` ls = return t'
                 | otherwise   = throwE (IllegalChoice s i t)

-- | Expose the payload and continuation of an input matched by a @?p; q@
-- pattern (linear) or a @*?p; q@ pattern (unrestricted). An unrestricted input
-- makes no progress, so its continuation is the channel itself.
input :: D.KindedTypeDecls -> K.Multiplicity -> ErrorSite -> T.KindedType
      -> Validation (T.KindedType, T.KindedType)
input tdecls = message tdecls Neg

output :: D.KindedTypeDecls -> K.Multiplicity -> ErrorSite -> T.KindedType -> Validation (T.KindedType, T.KindedType)
output tdecls = message tdecls Pos

message :: D.KindedTypeDecls -> Polarity -> K.Multiplicity -> ErrorSite -> T.KindedType
        -> Validation (T.KindedType, T.KindedType)
message tdecls p m site t = case message' tdecls p m t of
  Just uv -> return uv
  Nothing -> throwE (ExposeError site expected t (normalise tdecls t))
  where
    expected | K.isUn m  = msg ("an unrestricted (`*" ++ sigil ++ "`) ")
             | otherwise = msg "a linear "
    msg q = q ++ (case p of Neg -> "input"; Pos -> "output") ++ " channel"
    sigil = case p of Neg -> "?"; Pos -> "!"

-- | 'message' without the failure.
message' :: D.KindedTypeDecls -> Polarity -> K.Multiplicity -> T.KindedType
         -> Maybe (T.KindedType, T.KindedType)
message' tdecls p m t
  | K.isUn m = case normalise tdecls t of
      t'@(T.AppMessage _ K.Un{} p' u)                | p == p' -> Just (u, t')
      T.AppSemi _ t'@(T.AppMessage _ K.Un{} p' u) _  | p == p' -> Just (u, t')
      _ -> Nothing
  | otherwise = case normalise tdecls t of
      T.AppMessage s K.Lin{} p' u                    | p == p' -> Just (u, T.Skip s)
      T.AppSemi _    (T.AppMessage _ K.Lin{} p' u) v | p == p' -> Just (u, v)
      _ -> Nothing

typeOutput :: D.KindedTypeDecls -> ErrorSite -> T.KindedType 
           -> Validation (Variable, K.Kind, T.KindedType)
typeOutput tdecls = typeMsg tdecls Pos

typeInput :: D.KindedTypeDecls -> ErrorSite -> T.KindedType 
          -> Validation (Variable, K.Kind, T.KindedType)
typeInput tdecls = typeMsg tdecls Neg

typeMsg :: D.KindedTypeDecls -> Polarity -> ErrorSite -> T.KindedType
            -> Validation (Variable, K.Kind, T.KindedType)
typeMsg tdecls p site t = case typeMsg' tdecls p t of
  Just akt -> return akt
  Nothing  -> throwE (ExposeError site msg t (normalise tdecls t))
  where msg = "a type-" ++ (case p of Neg -> "input"; Pos -> "output") ++ " channel"

-- | 'typeMsg' without the failure.
typeMsg' :: D.KindedTypeDecls -> Polarity -> T.KindedType
         -> Maybe (Variable, K.Kind, T.KindedType)
typeMsg' tdecls p t = case normalise tdecls t of
  T.AppQuantS _ p' a k t' | p == p' -> Just (a, k, t')
  _ -> Nothing

wait :: D.KindedTypeDecls -> ErrorSite -> T.KindedType -> Validation ()
wait tdecls site t = do
  case normalise tdecls t of
    T.End _ Neg -> return ()
    T.AppSemi _ (T.End _ Neg) _ -> return ()
    t' -> throwE (ExposeError site "a `Wait` channel" t t')
