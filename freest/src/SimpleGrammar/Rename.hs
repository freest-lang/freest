{- |
Module      :  SimpleGrammar.Rename
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Minimal (or canonical) type renaming
-}

module SimpleGrammar.Rename
  ( rename
  )
where

import           Syntax.Base
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

bounded :: Visited -> TypeDeclMap -> T.Type -> Bool
bounded v td = \case
  -- Session types
  T.End{} -> True
  T.AppSemi _ t u -> bounded v td t || bounded v td u
  T.Choice _ _ _ its -> any (bounded v td . snd) its
  T.AppDual _ t -> bounded v td t
  -- Polymorphism
  T.AppQuant _ _ _ _ t -> bounded v td t
  -- Equations
  T.AppTName _ id ts
    | id `S.member` v -> True
    | otherwise -> bounded v td (snd (td M.! id)) -- TODO: Check
  -- Higher-order
  T.Var _ var -> undefined
  T.App _ t ts -> undefined
  -- Functional types, Skip, Message, DName
  _ -> False
