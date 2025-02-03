{- |
Module      :  SimpleGrammar.Rename
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Minimal (or canonical) type renaming

Absorbing - non-normed types == types w/ infinite norm
-}

module Validation.Rename
  ( rename
  , bounded -- for testing purposes
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

type Visited = S.Set Identifier

rename :: TypeDeclMap -> T.Type -> T.Type
rename td = \case
  t | T.isConstant t -> t
  t@T.Var{} -> t
  t@T.TName{} -> t
  T.Choice s m p lts -> T.Choice s m p (map (second (rename td)) lts)
  T.App s t us -> T.App s (rename td t) (map (rename td) us)
  t@(T.Quant s p a k u) -> T.Quant s p b k (rename td (subs a (T.fromVariable b) u))
    where freet = freeReachable t
          freeu = freeReachable u
          b = if a `elem` freeu then firstVar a freet else nullVar a

freeReachable :: T.Type -> S.Set Variable
freeReachable = freeVars
-- freeReachable = freeReach S.empty
--   where freeReach :: S.Set Variable -> Variable -> S.Set Variable
--         freeReach _ a = S.singleton a

bounded = absorbing

-- Requires: the type is normalised,
-- otherwise the function may diverge on non-contractive types
absorbing :: TypeDeclMap -> T.Type -> Bool
absorbing td = absorb S.empty
  where
    absorb :: Visited -> T.Type -> Bool
    absorb v = \case
      -- Session types
      T.End{} -> True
      T.AppSemi _ t u -> absorb v t || absorb v u
      T.AppMessage _ K.Un _ _ -> True -- Unrestricted type
      T.Choice _ K.Un _ _ -> True -- Unrestricted type
      T.Choice _ _ _ its -> all (absorb v . snd) its
      -- Polymorphism
      T.Quant _ _ _ _ t -> absorb v t
      -- Equations
      T.AppTName _ id ts
        | id `S.member` v -> True
        | otherwise -> absorb (S.insert id v) (snd (td M.! id)) -- TODO: Check
      -- Higher-order, including AppDual
      T.App _ t ts -> all (absorb v) (t:ts)
      -- Functional types, Skip, Message, DName, Var
      _ -> False

