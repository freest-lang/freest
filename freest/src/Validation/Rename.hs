{- |
Module      :  SimpleGrammar.Rename
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Absorbing - non-normed types == types w/ infinite norm
-}

module Validation.Rename
  ( first
  , reachable
  , absorbing -- for testing purposes only
  )
where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap, ValidationState, typeDecls, kindSigs, getType, getKind )
import Validation.Substitution ( subs, subsAll )
import Validation.Normalisation ( reduce, betaRule, isWhnf, tNameRedex )
import Validation.Kinding ( runSynth' )
import Utils ( internalError )

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Maybe ( isNothing )

-- | (first s t) is be the smallest variable in set B \ (s union reach t)
first :: ValidationState -> Set.Set Variable -> T.Type -> Variable
first vs s t = firstVar var (s `Set.union` reachable vs t)
  where var = Variable (getSpan t) "α" defaultInternal

-- | The set of free variables reachable in a type.
reachable :: ValidationState -> T.Type -> Set.Set Variable
reachable vs = \case
  -- C-Const
  t | T.isConstant t -> Set.empty
  -- C-Var
  T.Var _ a -> Set.singleton a
  -- C-Abs
  T.Abs _ aks t -> reachable vs t Set.\\ Set.fromList (map fst aks)
  -- C-Semi1, C-Semi2
  T.AppSemi _ t u | absorbing vs t -> reachable vs t
                  | otherwise -> reachable vs t `Set.union` reachable vs u
  -- C-Dual
  T.AppDual _ t -> reachable vs t
  -- C-µ1, C-µ2
  T.AppTName s name ts | absorbing vs u -> Set.unions (map (reachable vs') ts)
                       | otherwise -> Set.unions (map (reachable vs') ts)
    where u = getType vs name
          k = getKind vs name
          vs' = vs {typeDecls = Map.insert name (T.Void s k) (typeDecls vs)}
  -- C-App1, C-App2
  t@(T.App _ u us) | isWhnf t -> Set.unions (map (reachable vs) (u:us))
  -- t@(T.App _ u us) | not (T.isSemi u) && isWhnf t -> Set.unions (map (reachable vs) (u:us))
                   | otherwise -> reachable vs (reduce (typeDecls vs) t)
                   -- | isNothing (tNameRedex t) -> reachable vs (reduce (typeDecls vs) t)
  t -> internalError $ "reachable: non-exhaustive pattern: " ++ show t

  -- | Is a given type absorbing?
absorbing :: ValidationState -> T.Type -> Bool
absorbing vs = \case
  T.End{} -> True
  T.Void _ k | K.isSession k -> True
  T.AppSemi _ t u -> absorbing vs t || absorbing vs u
  T.SharedChoice{}        -> True -- Unrestricted choice
  T.AppMessage _ K.Un _ _ -> True -- Unrestricted message
  T.App _ T.Choice{} ts -> all (absorbing vs) ts
  T.AppDual _ t -> absorbing vs t
  -- forall F _ Using instead forall lambda a.T
  T.AppTypeMsg _ _ _ _ t -> absorbing vs t
  -- µ_κ F absorbing if F Void_κ absorbing
  t@(T.AppTName s name ts) -> absorbing (vs {typeDecls = Map.insert name (T.Void s k) (typeDecls vs)}) (if null ts then u else T.App s u ts)
    where
      k = getKind vs name
      u = getType vs name
  t -> case betaReduces t of
    Just u -> absorbing vs u
    Nothing -> False

betaReduces :: T.Type -> Maybe T.Type
betaReduces = \case
  -- R-β
  T.App _ t@T.Abs{} us -> Just $ betaRule t us
  -- R-VoidApp
  T.App s (T.Void _ (K.Arrow _ _ k)) [_] -> Just $ T.Void s k
  -- R-TAppL
  T.App s t us -> do
    t' <- betaReduces t
    Just $ T.App s t' us
  _ -> Nothing
