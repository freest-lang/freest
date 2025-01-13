{- |
Module      :  SimpleGrammar.Rename
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Minimal (or canonical) type renaming
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
rename = ren S.empty
  where
    ren :: Visited -> TypeDeclMap -> T.Type -> T.Type
    ren = undefined

reachable :: Visited -> T.Type -> S.Set Identifier
reachable = undefined

-- Requires: the type is normalised,
-- otherwise the function may diverge on non-contractive types
bounded :: TypeDeclMap -> T.Type -> Bool
bounded = bound S.empty

bound :: Visited -> TypeDeclMap -> T.Type -> Bool
bound v td = \case
  -- Session types
  T.End{} -> True
  T.AppMessage _ K.Un _ _ -> True -- Unrestricted type - Temporary?
  T.AppSemi _ t u -> bound v td t || bound v td u
  T.Choice _ _ _ its -> all (bound v td . snd) its
  -- Polymorphism
  T.Quant _ _ _ _ t -> bound v td t
  -- Equations
  T.AppTName _ id ts
    | id `S.member` v -> True
    | otherwise -> bound (S.insert id v) td (snd (td M.! id)) -- TODO: Check
  -- Higher-order, including AppDual
  T.App _ t ts -> all (bound v td) (t:ts)
  -- Functional types, Skip, Message, DName, Var
  _ -> False
