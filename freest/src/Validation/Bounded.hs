{- |
Module      :  Validation.Bounded
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Is a given type bounded? Can it be used to create a new channel?

Intuitively, bounded types are types whose finite traces terminate with Close or
Wait. In particular, types with infinite traces only are bounded. Functional
types are not bounded.

Some bounded types:

  ?Int ; Wait
  type MathServer = +{Neg: !Int ; MathServer, Done: Skip}; Close
  type Stream a = !a ; Stream a

Some unbounded types:

  Skip
  !Int ; ?Bool
  type U = +{Neg: !Int ; U, Done: Skip}

-}

module Validation.Bounded
  ( bounded
  )
where

import           Syntax.Base                   ( Identifier )
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )

import qualified Data.Map.Strict               as M
import qualified Data.Set                      as S

type Visited = S.Set Identifier

bounded :: Visited -> TypeDeclMap -> T.Type -> Bool
bounded v td = \case
  -- Session types
  T.End{} -> True
  T.AppSemi _ t u -> bounded v td t || bounded v td u
  T.Choice _ _ _ its -> all (bounded v td . snd) its
  T.AppDual _ t -> bounded v td t
  -- Polymorphism
  T.Quant _ _ _ _ t -> bounded v td t
  -- Equations
  T.AppTName _ id ts
    | id `S.member` v -> True
    | otherwise -> bounded v td (snd (td M.! id)) -- TODO: Check
  -- Higher-order
  T.Var _ var -> undefined
  T.App _ t ts -> undefined
  -- Functional types, Skip, Message, DName
  _ -> False
