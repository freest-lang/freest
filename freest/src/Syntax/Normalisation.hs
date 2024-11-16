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
  T.AppSemi _ T.Skip{} t  -> Just t                                -- R-Seq1
  T.AppDual _ t@T.Skip{}  -> Just t                                -- R-DSkip
  T.AppDual _ (T.End s p) -> Just (T.End s (T.dual p))             -- R-DEnd
  T.AppDual _ (T.App s1 (T.Message s2 m p) t) ->                   -- R-D♯
    Just (T.App s1 (T.Message s2 m (T.dual p)) t)
  -- T.Dual _ (T.Quantifier _ p aks t) -> ...
  T.AppDual _ (T.AppDual _ w@(T.App _ (T.Var _ _) _)) -> Just w    -- R-DDVar
  -- T.App  s1 (T.Abs s2 aks t) us                                 -- R-β+
  --   | n == m    -> Just t'
  --   | n <  m    -> Just (T.App s1 t' (drop n us))
  --   | otherwise -> Just (T.Abs s2 (drop m aks) t')
  --   where
  --     n  = length aks
  --     m  = length us
  --     t' = foldr (uncurry subs) t (zip (map fst (take m aks)) us)
  T.AppDual s1 (T.Labelled s2 (T.Choice m p) lts) ->               -- R-D⊙
    Just (T.Labelled s2 (T.Choice m (T.dual p)) (map (second (T.AppDual s1)) lts))
  T.AppSemi s1 (T.AppSemi s2 t u) v ->                             -- R-Assoc
    Just (T.AppSemi (spanFromTo t v) t (T.AppSemi (spanFromTo u v) u v))
  T.AppSemi s t u ->                                               -- R-Seq2
    reduceBSD t >>= Just . flip (T.AppSemi s) u
  T.AppDual _ (T.AppSemi s t u) ->                                 -- R-D;
    Just (T.AppSemi s (T.AppDual (getSpan t) t) (T.AppDual (getSpan u) u))
  T.AppDual s t ->                                                 -- R-DCtx
    reduceBSD t >>= Just . T.AppDual s
  T.App s t v ->                                                   -- R-TAppL
    reduceBSD t >>= Just . flip (T.App s) v
  _ -> Nothing

normalise :: T.Type -> Validation (Maybe T.Type)
normalise = normalise' Set.empty
  where
    normalise' is = \case
      (reduceBSD -> Just t) -> 
        normalise' is t
      T.Name _ i -> 
        visit is i []
      t@(T.App  _ (T.Name _ i) _) -> visit is i []
      T.AppSemi s (T.Name _ i) u ->
        visit is i [] -- <&> fmap (\t' -> T.AppSemi s t' u)
      T.AppSemi s (T.App _ (T.Name _ i) ts) u ->
        visit is i (NE.toList ts) -- <&> fmap (\t' ->T.AppSemi s t' u)
      T.AppDual s (T.Name _ i) ->
        visit is i [] -- <&> fmap (T.AppDual s)
      T.AppDual s (T.App _ (T.Name _ i) ts) ->
        visit is i (NE.toList ts) -- <&> fmap (T.AppDual s)
      T.AppSemi s1 (T.AppDual s2 (T.Name _ i)) u -> do
        visit is i [] -- <&> fmap (\t' -> T.AppSemi s1 (T.AppDual s2 t') u)
      T.AppSemi s1 (T.AppDual s2 t@(T.App _ (T.Name _ i) ts)) u ->
        visit is i (NE.toList ts) -- <&> fmap (\t' -> T.AppSemi s1 (T.AppDual s2 t') u)
      t -> return  (Just t)
    visit :: Set.Set (Identifier, [T.Type]) -> Identifier -> [T.Type] -> Validation (Maybe T.Type)
    visit is i ts
      | Set.member (i, ts) is = pure Nothing
      | otherwise = lookupType i ts >>= normalise' (Set.insert (i, ts) is)
