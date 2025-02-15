{- |
Module      :  SimpleGrammar.Rename
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Minimal (or canonical) type renaming

Absorbing - non-normed types == types w/ infinite norm
-}

module Validation.Rename
  ( rename
  -- , bounded -- use absorbing, if needed
  )
where

import           Syntax.Base
import qualified Syntax.Kind                   as K
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Substitution       ( subs, freeVars )

import qualified Data.Map.Strict               as M
import qualified Data.Set                      as S
import           Data.Bifunctor                ( second )

rename :: TypeDeclMap -> T.Type -> T.Type
rename td = \case
  t | T.isConstant t -> t
  t@T.Var{} -> t
  t@T.TName{} -> t
  T.App s t us -> T.App s (rename td t) (map (rename td) us)
  t@(T.Quant s p a k u) -> T.Quant s p b k (rename td (subs a (T.fromVariable b) u))
    where freet = freeReachable t
          freeu = freeReachable u
          b = if a `elem` freeu then firstVar a freet else nullVar a

freeReachable :: T.Type -> S.Set Variable
freeReachable = freeReach S.empty
  where
    freeReach :: S.Set Variable -> T.Type -> S.Set Variable
    freeReach v = \case
      t | T.isConstant t -> S.empty
      T.Var _ a | a `S.member` v -> S.empty
                | otherwise -> S.singleton a
      T.Quant _ _ a _ t -> freeReach (S.delete a v) t
      T.App _ t us | absorbing M.empty t -> freeReach v t
                   | otherwise -> freeReach v t `S.union` S.unions (map (freeReach v) us)
      T.TName{} -> S.empty

-- Requires: the type is in whnf (i.e., normalised)
-- otherwise the function may diverge on non-contractive types
absorbing :: TypeDeclMap -> T.Type -> Bool
absorbing td = absorb S.empty
  where
    absorb :: S.Set Variable -> T.Type -> Bool
    absorb v = \case
      -- Session types
      T.End{} -> True
      T.Var _ a -> a `elem` v
      T.AppSemi _ t u -> absorb v t || absorb v u
      T.AppDual _ t -> absorb v t
      T.SharedChoice{} -> True -- Unrestricted type
      T.AppMessage _ K.Un _ _ -> True -- Unrestricted type
      T.App _ T.Choice{} ts -> all (absorb v) ts
      T.Quant _ _ a _ t -> absorb (S.delete a v) t
      -- -- Equations
      -- T.AppTName _ id ts
      --   | id `S.member` v -> True
      --   | otherwise -> absorb (S.insert id v) (snd (td M.! id)) -- TODO: Check
      -- -- Higher-order, including AppDual
      -- T.App _ t ts -> all (absorb v) (t:ts)
      -- -- Functional types, Skip, Message, DName, Var
      _ -> False
