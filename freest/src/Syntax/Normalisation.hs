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
import Data.Maybe (isJust)
import qualified Data.Set as Set
import Data.Functor ((<&>))

normalises :: T.Type -> Validation Bool
normalises = fmap isJust . normalise

reduceBSD :: T.Type -> Maybe T.Type
reduceBSD = \case
  T.Semi _ T.Skip{} t  -> Just t                                -- R-Seq1
  T.Dual _ t@T.Skip{}  -> Just t                                -- R-DSkip
  T.Dual _ (T.End s p) -> Just (T.End s (T.dual p))             -- R-DEnd
  T.Dual _ (T.App s1 (T.Message s2 m p) t) ->                   -- R-D♯
    Just (T.App s1 (T.Message s2 m (T.dual p)) t)
  -- T.Dual _ (T.Quantifier _ p aks t) -> ...
  T.Dual _ (T.Dual _ w@(T.App _ (T.Var _ _) _)) -> Just w       -- R-DDVar
  T.App  s1 (T.Abs s2 aks t) us                                 -- R-β+
    | n == m    -> Just t'
    | n <  m    -> Just (T.App s1 t' (drop n us))
    | otherwise -> Just (T.Abs s2 (drop m aks) t')
    where
      n  = length aks
      m  = length us
      t' = foldr (uncurry subs) t (zip (map fst (take m aks)) us)
  T.Dual s1 (T.Labelled s2 (T.Choice m p) lts) ->               -- R-D⊙
    Just (T.Labelled s2 (T.Choice m (T.dual p)) (map (second (T.Dual s1)) lts))
  T.Semi s1 (T.Semi s2 t u) v ->                                -- R-Assoc
    Just (T.Semi (spanFromTo t v) t (T.Semi (spanFromTo u v) u v))
  T.Semi s t u ->                                               -- R-Seq2
    reduceBSD t >>= Just . flip (T.Semi s) u
  T.Dual _ (T.Semi s t u) ->                                    -- R-D;
    Just (T.Semi s (T.Dual (getSpan t) t) (T.Dual (getSpan u) u))
  T.Dual s t ->                                                 -- R-DCtx
    reduceBSD t >>= Just . T.Dual s
  T.App s t v ->                                                -- R-TAppL
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
      T.Semi s (T.Name _ i) u ->
        visit is i [] -- <&> fmap (\t' -> T.Semi s t' u)
      T.Semi s (T.App _ (T.Name _ i) ts) u ->
        visit is i ts -- <&> fmap (\t' ->T.Semi s t' u)
      T.Dual s (T.Name _ i) ->
        visit is i [] -- <&> fmap (T.Dual s)
      T.Dual s (T.App _ (T.Name _ i) ts) ->
        visit is i ts -- <&> fmap (T.Dual s)
      T.Semi s1 (T.Dual s2 (T.Name _ i)) u -> do
        visit is i [] -- <&> fmap (\t' -> T.Semi s1 (T.Dual s2 t') u)
      T.Semi s1 (T.Dual s2 t@(T.App _ (T.Name _ i) ts)) u ->
        visit is i ts -- <&> fmap (\t' -> T.Semi s1 (T.Dual s2 t') u)
      t -> return  (Just t)
    visit is i ts
      | Set.member (i, ts) is = pure Nothing
      | otherwise = lookupType i ts >>= normalise' (Set.insert (i, ts) is)
