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
import qualified Syntax.Kind                   as K
import           Validation.Base               ( TypeDeclMap )

import qualified Data.Map.Strict               as M
import qualified Data.Set                      as S

type Visited = S.Set Identifier

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
