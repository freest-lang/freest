{- |
Module      :  Validation.Escape
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Instantiation variables that outlive the application that made them.

A polymorphic argument passed by name leaves its type argument open at the call;
if a binder receives it, the variable escapes into the binder's scope and must be
bound to one monotype for the rest of the program. The store records the binder,
the type variables in scope there, and the monotype once it is fixed.
-}
module Validation.Escape
  ( escapeTypeVar
  , escapedTypeVar
  , bindEscapedTypeVar
  , escapedTypeArgFixedAt
  , resolveEscaped
  )
where

import Syntax.Base
import Syntax.Type.Kinded qualified as TK
import Validation.Base ( Validation, ValidationState(..) )

import Control.Monad.State ( modify, gets )
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

escapeTypeVar :: Variable -> Variable -> Set.Set Variable -> Validation ()
escapeTypeVar iv x scope =
  modify \s -> s{typeStore = Map.insertWith (\_ old -> old) iv (x, scope, Nothing) (typeStore s)}

escapedTypeVar :: Variable -> Validation (Maybe (Variable, Set.Set Variable, Maybe (TK.KindedType, Span)))
escapedTypeVar iv = gets (Map.lookup iv . typeStore)

-- | Bind an escaped type argument, keeping the span of the expression that fixed
-- it for 'escapedTypeArgFixedAt'.
bindEscapedTypeVar :: Variable -> TK.KindedType -> Span -> Validation ()
bindEscapedTypeVar iv t sp =
  modify \s -> s{typeStore = Map.adjust (\(x, scope, _) -> (x, scope, Just (t, sp))) iv (typeStore s)}

-- | The variable whose escaped type argument was bound to a type at one of the
-- given spans, and where it was fixed. Error messages add that site: a type read
-- off the store is otherwise reported at the span it was declared at.
escapedTypeArgFixedAt :: [Span] -> Validation (Maybe (Variable, Span))
escapedTypeArgFixedAt sps = gets \s ->
  case [ (x, sp) | (x, _, Just (u, sp)) <- Map.elems (typeStore s), getSpan u `elem` sps ] of
    (r : _) -> Just r
    []      -> Nothing

-- | Replace each escaped variable by the monotype it was bound to, to a
-- fixpoint. A check that reads a type after the solve sees what the store fixed,
-- not the variable the application left behind.
resolveEscaped :: Map.Map Variable (Variable, Set.Set Variable, Maybe (TK.KindedType, Span))
               -> TK.KindedType -> TK.KindedType
resolveEscaped store = go Set.empty
  where
    go seen = \case
      TK.Var _ _ InstLv iv | iv `Set.notMember` seen, Just (_, _, Just (u, _)) <- Map.lookup iv store -> go (Set.insert iv seen) u
      TK.Abs s aks u -> TK.Abs s aks (go seen u)
      TK.App s u us  -> TK.App s (go seen u) (map (go seen) us)
      t -> t
