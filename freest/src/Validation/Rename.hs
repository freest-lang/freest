{- |
Module      :  SimpleGrammar.Rename
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Minimal (or canonical) type renaming

Absorbing - non-normed types == types w/ infinite normed
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

import qualified Data.Map.Strict               as M
import qualified Data.Set                      as S

type Visited = S.Set Identifier

rename :: TypeDeclMap -> T.Type -> T.Type
rename td = ren S.empty
  where
    ren :: Visited -> T.Type -> T.Type
    ren _ = id

reachable :: Visited -> T.Type -> S.Set Identifier
reachable = undefined

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

-- first :: S.Set Variable -> Variable -> Variable
-- first s a = head $ filter (\n -> `S.notMember` s)) [-1, -2 ..]
