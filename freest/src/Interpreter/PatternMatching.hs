{- |
Module      :  Interpreter.PatternMatching
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's runtime pattern matching: a value-directed
matcher that matches runtime 'Value's against surface 'Pat'terns, producing
variable bindings.

Session patterns perform communication, which is irreversible — so a channel
matched by a session pattern must be received from *once*, with the result then
selecting a clause (it must not be re-received as we try later clauses). We
therefore split matching into two passes:

  1. 'forceColumns' performs the session effects demanded by the clauses
     (receive a choice label, receive a value, wait), turning the channels into
     ordinary data values. Because the type system makes the session structure
     of a column the same across all clauses, this can be done once, up front,
     even when the session pattern is nested inside a data pattern (e.g. a
     tuple).

  2. 'matchClause' / 'matchPat' then match the clauses against those forced
     values *purely*, with ordinary backtracking and guard fall-through.
-}
module Interpreter.PatternMatching
  ( matchPat
  , matchClause
  , forceColumns
  , mkClosure
  ) where

import Control.Monad (zipWithM)
import Data.List (transpose)
import Data.Map (empty, singleton, union, insert)

import Interpreter.Value (Value(..), Env, Clause)
import Interpreter.Builtin (asString, receive, receiveLabel)
import qualified Syntax.Base as B
import qualified Syntax.Expression as E

-- == Pure matching (run after 'forceColumns') ==============================

-- | Match a single pattern (one column) against a value, producing bindings on
-- success or 'Nothing' on failure. Session patterns are matched against the
-- *forced* representations produced by 'forceColumns'.
matchPat :: Value -> E.Pat -> IO (Maybe Env)
matchPat v = \case
  E.IntPat _ i   -> pure $ case v of VInt   i' | i == i' -> Just empty ; _ -> Nothing
  E.FloatPat _ f -> pure $ case v of VFloat f' | f == f' -> Just empty ; _ -> Nothing
  E.CharPat _ c  -> pure $ case v of VChar  c' | c == c' -> Just empty ; _ -> Nothing
  E.StringPat _ s -> pure $ case asString v of Just s' | s == s' -> Just empty ; _ -> Nothing
  E.WildPat _ _  -> pure (Just empty)
  E.VarPat _ x   -> pure (Just (singleton x v))
  E.AsPat _ x p  -> fmap (insert x v) <$> matchPat v p
  E.PackPat _ _ p ->
    case v of
      VPack _ inner -> matchPat inner p
      _             -> pure Nothing
  E.DConsPat _ (B.Identifier _ con) ps ->
    case v of
      VCons con' vs | con == con' && length ps == length vs -> matchClause ps vs
      _                                                      -> pure Nothing
  -- Session patterns, matched against the forced representations:
  --   a chosen branch  &l   →  VCons l [continuation]
  --   a received value ?p;q →  VCons "(,)" [forced p, forced q]
  --   a closed channel Wait →  any (the wait was performed)
  E.ChoicePat _ (B.Identifier _ label) q ->
    case v of
      VCons label' [cont] | label == label' -> matchPat cont q
      _                                     -> pure Nothing
  E.InPat _ p1 p2 ->
    case v of
      VCons "(,)" [v1, v2] -> matchClause [p1, p2] [v1, v2]
      _                    -> pure Nothing
  E.TypeInPat _ _ p -> matchPat v p   -- the type input was already consumed
  E.WaitPat _       -> pure (Just empty)

-- | Match a column of patterns left-to-right against a list of values, failing
-- fast and unioning the bindings.
matchClause :: [E.Pat] -> [Value] -> IO (Maybe Env)
matchClause []       []       = pure (Just empty)
matchClause (p : ps) (v : vs) = do
  mb <- matchPat v p
  case mb of
    Nothing -> pure Nothing
    Just b  -> fmap (union b) <$> matchClause ps vs
matchClause _ _ = pure Nothing   -- arity mismatch

-- == Session forcing pass ==================================================

-- | Perform, once, the session effects the clauses demand on the argument
-- values, turning channels into ordinary data values. The patterns of all the
-- clauses (one column list per clause) guide which effect to perform; by the
-- type system they agree on the session structure of every position.
forceColumns :: [Clause] -> [Value] -> IO [Value]
forceColumns clauses vals = zipWithM forceCol (transpose (map fst clauses)) vals

-- | Force one position, given the patterns the clauses use there.
forceCol :: [E.Pat] -> Value -> IO Value
forceCol pats val = case val of
  -- a channel reached by a session pattern: perform its effect (once)
  VChan _ ->
    case filter isSessionPat (map stripAs pats) of
      (E.ChoicePat{} : _) -> forceChoice pats val   -- needs the whole column (see below)
      (sp : _)            -> performEffect sp val
      []                  -> pure val               -- only bound (var pattern): no effect
  -- recurse into data, using the sub-patterns of the clauses that match `con`
  VCons con vs ->
    let subColumns = transpose [ ps | E.DConsPat _ (B.Identifier _ con') ps <- map stripAs pats
                                    , con' == con, length ps == length vs ]
    in if null subColumns then pure val
       else VCons con <$> zipWithM forceCol subColumns vs
  _ -> pure val

-- | Force an external choice: receive the label, then force the continuation
-- using the continuation patterns of the clauses that selected *this* label —
-- so a session pattern nested in the continuation (e.g. @&Bid (?x;c)@) is forced
-- too. (Mirrors the @VCons@ recursion in 'forceCol': commit to the branch the
-- peer actually chose, then recurse into it. The type system guarantees the
-- selected clauses agree on the continuation's session structure.)
forceChoice :: [E.Pat] -> Value -> IO Value
forceChoice pats (VChan c) = do
  (label, c') <- receiveLabel c
  let conts = [ q | E.ChoicePat _ (B.Identifier _ l) q <- map stripAs pats, l == label ]
  forced <- forceCol conts (VChan c')
  pure (VCons label [forced])
forceChoice _ v = pure v

-- | Perform a session pattern's effect on a channel, producing the forced value
-- that 'matchPat' then matches purely. (External choice is handled by
-- 'forceChoice', which needs the whole pattern column.)
performEffect :: E.Pat -> Value -> IO Value
performEffect (E.InPat _ p1 p2) (VChan c) = do
  (v, c') <- receive c
  v'  <- forceCol [p1] v
  c'' <- forceCol [p2] (VChan c')
  pure (VCons "(,)" [v', c''])
performEffect (E.TypeInPat _ _ p) (VChan c) = do
  (_, c') <- receive c                  -- consume the (erased) type message
  forceCol [p] (VChan c')
performEffect (E.WaitPat _) (VChan c) = do
  _ <- receive c                        -- wait for the peer to close
  pure VUnit
performEffect _ v = pure v

isSessionPat :: E.Pat -> Bool
isSessionPat = \case
  E.ChoicePat{} -> True
  E.InPat{}     -> True
  E.TypeInPat{} -> True
  E.WaitPat{}   -> True
  _             -> False

-- | 'AsPat' is transparent for the purpose of finding the session structure.
stripAs :: E.Pat -> E.Pat
stripAs = \case
  E.AsPat _ _ p -> stripAs p
  p             -> p

-- == Function values =======================================================

-- | Build a function value from its clauses, capturing the environment. The
-- environment is captured lazily, so a self- or mutually-recursive binding can
-- include the closure(s) being defined (tied with an ordinary recursive @let@).
mkClosure :: Env -> [Clause] -> Value
mkClosure env clauses = VClosure (length (fst (head clauses))) [] clauses env
