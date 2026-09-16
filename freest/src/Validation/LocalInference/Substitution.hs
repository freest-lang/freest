-- Substitution for local type inference. 

module Validation.LocalInference.Substitution where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Type.Kinded qualified as T
import Validation.Base
import Compiler.Bug (internalError)

-- | Instantiation-level substitution of types; multiplicities are left to the
-- global solve.
newtype Substitution = Θ [(Variable, T.KindedType)]
  deriving Show

-- | Composition for substitutions.
instance Semigroup Substitution where
  Θ ivtms1 <> Θ ivtms2 = Θ (ivtms1 ++ ivtms2)

-- | The empty substitution.
instance Monoid Substitution where
  mempty = Θ []

-- | Alias for the empty substitution.
emptySubs :: Substitution
emptySubs = Θ []

-- | Make a type substitution.
subsType :: Variable -> T.KindedType -> Substitution
subsType iv t = Θ [(iv, t)]

-- | Apply a substitution.
applySubs :: Substitution -> T.KindedType -> T.KindedType
applySubs (Θ ivts) t = foldr (uncurry subst) t ivts
  where
    subst iv t = \case
      T.Var _ _ InstLv iv' | iv == iv' -> t
      T.Abs s aks u -> T.Abs s aks (subst iv t u)
      T.App s u us -> T.App s (subst iv t u) (map (subst iv t) us)
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
