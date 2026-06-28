-- Kind-level unification for inference.
--
-- Decomposes a subkinding goal @K1 <: K2@ by unifying the arrow structure and
-- whole-kind variables, binding the latter, and reducing the proper leaves to
-- multiplicity and prekind constraints solved by the sibling modules
-- (Multiplicities, Prekinds). Subkinding is the primitive: arrows are
-- contravariant in the domain and covariant in the codomain.
module Validation.LocalInference.Kinds
  ( KindUnifier(..)
  , UnifyError(..)
  , unifyKindSub
  , unifyKindSubs
  ) where

import Syntax.Base
import Syntax.Kind (Kind(..), Multiplicity(..), Prekind(..), pattern VarM)
import Syntax.Kind qualified as K
import Syntax.Provenance (Origin)
import Validation.LocalInference.Multiplicities (MultConstraints, MultEquation, kindEq)
import Validation.LocalInference.Prekinds (PrekindConstraints, PrekindConstraint(..))

import Control.Monad.State (StateT, runStateT, gets, modify)
import Control.Monad.Trans.Class (lift)
import Data.Map.Strict qualified as Map

-- | The result of unifying two kinds: the whole-kind variable bindings, and the
-- leaf constraints to hand to the multiplicity and prekind solvers.
data KindUnifier = KindUnifier
  { kindSubst          :: Map.Map Variable Kind
  , multConstraints    :: MultConstraints
  , prekindConstraints :: PrekindConstraints
  }

-- | Why unification failed.
data UnifyError
  = Mismatch Kind Kind        -- ^ incompatible kind structure (e.g. proper vs. arrow)
  | Occurs Variable Kind      -- ^ a variable would be bound to a kind that mentions it

-- The solver threads a fresh-variable counter (decreasing negative internal IDs,
-- assumed disjoint from the input) and the accumulating result.
data Acc = Acc
  { counter :: !Int
  , kSub    :: Map.Map Variable Kind
  , mCs     :: MultConstraints
  , pCs     :: PrekindConstraints
  }

type U = StateT Acc (Either UnifyError)

-- | Unify two kinds related by @<:@, producing the whole-kind bindings and the
-- residual multiplicity/prekind leaf constraints, or a 'UnifyError'.
unifyKindSub :: Origin -> Kind -> Kind -> Either UnifyError KindUnifier
unifyKindSub o k1 k2 = unifyKindSubs Map.empty [(o, k1, k2)]

-- | Unify a set of subkinding constraints together, threading one substitution
-- and fresh-variable counter, so bindings from one constraint inform the next.
-- The substitution is seeded with @binds@ (e.g. whole-kind bindings established
-- elsewhere during kinding).
unifyKindSubs :: Map.Map Variable Kind -> [(Origin, Kind, Kind)] -> Either UnifyError KindUnifier
unifyKindSubs binds cs =
  case runStateT (mapM_ (\(o, k1, k2) -> go o k1 k2) cs) (Acc (-2) binds [] []) of
    Left e         -> Left e
    Right (_, acc) -> Right (KindUnifier (kSub acc) (mCs acc) (pCs acc))

go :: Origin -> Kind -> Kind -> U ()
go o k1 k2 = do
  k1' <- chase k1
  k2' <- chase k2
  case (k1', k2') of
    (Var _ l1 a, Var _ l2 b)
      | a == b      -> pure ()
      | solvable l1 -> bind a k2'
      | solvable l2 -> bind b k1'
      | otherwise   -> lift (Left (Mismatch k1' k2'))
    (Var s l a, _) | solvable l -> do k <- instLike s k2'; bind a k; go o k k2'
    (_, Var s l a) | solvable l -> do k <- instLike s k1'; bind a k; go o k1' k
    (Arrow _ d1 c1, Arrow _ d2 c2) -> go o d2 d1 >> go o c1 c2  -- contravariant / covariant
    (Proper _ m1 p1, Proper _ m2 p2) -> do
      emitMult (kindEq (K.join m1 m2) m2)  -- m1 <: m2, as the ACUI encoding
      emitPre  (SubPrekind o p1 p2)
    _ -> lift (Left (Mismatch k1' k2'))

-- | A fresh kind of the same structure as the argument, with fresh leaf/whole-
-- kind variables — so a whole-kind variable resolves to a /shape/, keeping its
-- leaves solvable rather than freezing them to the matched kind's scalars.
instLike :: Span -> Kind -> U Kind
instLike s = \case
  Proper{} -> Proper s <$> freshMult s <*> freshPrekind s
  Arrow{}  -> Arrow s <$> freshKind s <*> freshKind s
  Var{}    -> freshKind s

fresh :: U Int
fresh = gets counter <* modify \a -> a { counter = counter a - 1 }

freshKind :: Span -> U Kind
freshKind s = fresh >>= \i -> pure (Var s UnifLv (Variable s ("κ" ++ show i) i))

freshMult :: Span -> U Multiplicity
freshMult s = fresh >>= \i -> pure (VarM s UnifLv (Variable s ("φ" ++ show i) i))

freshPrekind :: Span -> U Prekind
freshPrekind s = fresh >>= \i -> pure (VarPK UnifLv (Variable s ("ψ" ++ show i) i))

-- | Resolve a whole-kind variable through the current bindings.
chase :: Kind -> U Kind
chase k = gets kSub >>= \s -> case k of
  Var _ l a | solvable l, Just k' <- Map.lookup a s -> chase k'
  _                                                  -> pure k

bind :: Variable -> Kind -> U ()
bind a k = do
  occ <- occurs a k
  if occ then lift (Left (Occurs a k))
         else modify \acc -> acc { kSub = Map.insert a k (kSub acc) }

occurs :: Variable -> Kind -> U Bool
occurs a = \case
  Var _ l b | solvable l ->
    if a == b then pure True
              else gets kSub >>= maybe (pure False) (occurs a) . Map.lookup b
  Arrow _ d c -> (||) <$> occurs a d <*> occurs a c
  _           -> pure False

emitMult :: MultEquation -> U ()
emitMult c = modify \acc -> acc { mCs = c : mCs acc }

emitPre :: PrekindConstraint -> U ()
emitPre c = modify \acc -> acc { pCs = c : pCs acc }
