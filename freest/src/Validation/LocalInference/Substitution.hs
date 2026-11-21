-- Substitution for local type inference. 

module Validation.LocalInference.Substitution where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Type.Kinded qualified as T
import Validation.Base
import Compiler.Bug (internalError)

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

-- | Instantiation-level substitution of types; multiplicities are left to the
-- global solve.
newtype Substitution = Θ (Map.Map Variable T.KindedType)
  deriving Show

-- | Composition for substitutions; where both bind a variable, the right one's
-- binding is kept.
instance Semigroup Substitution where
  Θ ivts1 <> Θ ivts2 = Θ (Map.union ivts2 ivts1)

-- | The empty substitution.
instance Monoid Substitution where
  mempty = Θ Map.empty

-- | Alias for the empty substitution.
emptySubs :: Substitution
emptySubs = Θ Map.empty

-- | Make a type substitution.
subsType :: Variable -> T.KindedType -> Substitution
subsType iv t = Θ (Map.singleton iv t)

-- | What a type stands for at its head: a bound variable is replaced by its
-- binding, in turn, until the head is not one. The dual of a variable does not
-- reduce, so it is a head too, and the variable under it is walked.
walk :: Substitution -> T.KindedType -> T.KindedType
walk θ@(Θ ivts) = \case
  T.Var _ _ InstLv iv | Just t <- Map.lookup iv ivts -> walk θ t
  T.AppDual s u -> T.AppDual s (walk θ u)
  t -> t

-- | Apply a substitution. A binding may mention variables bound elsewhere in
-- it, so the type a variable is bound to is resolved in turn; one already being
-- resolved is left alone, so that a cyclic binding cannot loop.
applySubs :: Substitution -> T.KindedType -> T.KindedType
applySubs (Θ bound) = go Set.empty
  where
    go seen = \case
      T.Var _ _ InstLv iv
        | iv `Set.notMember` seen, Just t <- Map.lookup iv bound -> go (Set.insert iv seen) t
      T.Abs s aks u -> T.Abs s aks (go seen u)
      T.App s u us -> T.App s (go seen u) (map (go seen) us)
      t -> t

-- | Make a fresh type instantiation variable. Its kind carries a fresh,
-- multiplicity rather than the one provided in the kind, so that
-- its multiplicity can be refined.
freshInstVarT :: Span -> K.Kind -> Validation T.KindedType
freshInstVarT s k = do
  i <- incCounter
  let v = Variable s ("ạ" ++ show i) i
  case k of
    K.Proper ks _ bk -> do
      m <- freshInstVarM s
      return (T.Var s (K.Proper ks m bk) InstLv v)
    _ -> internalError "non-proper instantiation kind"

-- | Make a fresh multiplicity instantiation variable.
freshInstVarM :: Span -> Validation K.Multiplicity
freshInstVarM s = do
  i <- incCounter 
  return $ K.VarM s InstLv (Variable s ("ṃ" ++ show i) i)
