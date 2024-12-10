{- |
Module      :  Syntax.Normalisation
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Checking whether types normalise; obtaining the weak head normal form of a type.
-}
module Syntax.Normalisation
  ( normalise
  , normalises
  )
where

import Syntax.Base
import Syntax.Substitution (subs)
import qualified Syntax.Type as T
import Validation.Base

import Control.Applicative ((<|>))
import Data.Bifunctor (second)
import Data.Functor ((<&>))
import qualified Data.List.NonEmpty as NE
import Data.Maybe (isJust)
import qualified Data.Set as Set

normalises :: T.Type -> Validation Bool
normalises = fmap isJust . normalise

-- Reduction by rules
-- B (R-β),
-- S, Semicolon (R-Seq-1, R-Seq2 and R-Assoc)
-- D, Dual (R-D;, R-DSkip, R-DEnd, R-D?, R-D!, R-D&, R-D+, R-DCtx, R-DDVar) and
-- Application (R-TAppL)
reduceBSD :: T.Type -> Maybe T.Type
reduceBSD = \case
  -- R-Seq1
  T.AppSemi _ T.Skip{} t  -> Just t
  -- R-DSkip
  T.AppDual _ t@T.Skip{}  -> Just t
  -- R-DEnd
  T.AppDual _ (T.End s p) -> Just (T.End s (T.dual p))
  -- R-D♯
  T.AppDual _ (T.App s1 (T.Message s2 m p) t) ->
    Just (T.App s1 (T.Message s2 m (T.dual p)) t)
  -- T.Dual _ (T.Quantifier _ p aks t) -> ...
  -- R-DDVar
  T.AppDual _ (T.AppDual _ w@(T.App _ (T.Var _ _) _)) -> Just w
  -- R-β _ No such thing
  -- R-D⊙
  T.AppDual s1 (T.Choice s2 m p lts) ->
    Just (T.Choice s2 m (T.dual p) (map (second (T.AppDual s1)) lts))
  -- R-Assoc
  T.AppSemi s1 (T.AppSemi s2 t u) v ->
    Just (T.AppSemi (spanFromTo t v) t (T.AppSemi (spanFromTo u v) u v))
  -- R-Seq2
  T.AppSemi s t u ->
    reduceBSD t >>= Just . flip (T.AppSemi s) u
  -- R-D;
  T.AppDual _ (T.AppSemi s t u) ->
    Just (T.AppSemi s (T.AppDual (getSpan t) t) (T.AppDual (getSpan u) u))
  -- R-DCtx
  T.AppDual s t ->
    reduceBSD t >>= Just . T.AppDual s
  -- R-TAppL
  T.App s t v ->
    reduceBSD t >>= Just . flip (T.App s) v
  _ -> Nothing

normalise :: T.Type -> Validation (Maybe T.Type)
normalise = normalise' Set.empty
  where
    normalise' is = \case
      (reduceBSD -> Just t) -> 
        normalise' is t
      T.AppTName _ i ts -> 
        visit is i ts
      T.AppSemi s (T.AppTName _ i ts) u ->
        visit is i ts -- <&> fmap (\t' -> T.AppSemi s t' u)
      T.AppDual s (T.AppTName _ i ts) ->
        visit is i ts -- <&> fmap (T.AppDual s)
      T.AppSemi s1 (T.AppDual s2 (T.AppTName _ i ts)) u ->
        visit is i ts -- <&> fmap (\t' -> T.AppSemi s1 (T.AppDual s2 t') u)
      t -> return  (Just t)
    visit :: Set.Set (Identifier, [T.Type]) -> Identifier -> [T.Type] -> Validation (Maybe T.Type)
    visit is i ts
      | Set.member (i, ts) is = pure Nothing
      | otherwise = lookupTName i ts >>= normalise' (Set.insert (i, ts) is)
