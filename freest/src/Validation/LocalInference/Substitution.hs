-- Substitution for local type inference. 

module Validation.LocalInference.Substitution where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Type.Kinded qualified as T
import Validation.Base
import Validation.Substitution (subsMultType, subsMultMult)
import Utils (internalError)

-- | Instantiation-level substitution. Instantiation variables may occur as
-- types or as multiplicities.
newtype Substitution = Θ [(Variable, Either T.KindedType K.Multiplicity)]
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

-- | Make a multiplicity substitution.
subsMult :: Variable -> K.Multiplicity -> Substitution
subsMult iv m = Θ [(iv, Right m)]

-- | Make a type substitution.
subsType :: Variable -> T.KindedType -> Substitution
subsType iv t = Θ [(iv, Left t)]

-- | Apply a substitution.
applySubs :: Substitution -> T.KindedType -> T.KindedType
applySubs (Θ ivtms) t = 
  foldr (\(ivi, tmi) ti -> either (subst ivi) (subsm ivi) tmi ti) t ivtms
  where
    subst iv t = \case
      T.Var _ _ InstLv iv' | iv == iv' -> t
      T.Abs s aks u -> T.Abs s aks (subst iv t u)
      T.App s u us -> T.App s (subst iv t u) (map (subst iv t) us)
      t -> t

    subsm = subsMultType InstLv

applySubsMult :: Substitution -> K.Multiplicity -> K.Multiplicity
applySubsMult (Θ ivtms) m =
  foldr (\(ivi, tmi) mi -> either (\_ m -> m) (subsMultMult InstLv ivi) tmi mi) m ivtms

-- | Make a fresh type instantiation variable. Its kind carries a fresh,
-- multiplicity rather than the one provided in the kind, so that
-- its multiplicity can be refined.
freshInstVarT :: Span -> K.Kind -> Validation T.KindedType
freshInstVarT s k = do
  i <- incCounter
  let v = Variable s ("ạ" ++ show i) i
  case k of
    K.Proper ks _ pk -> do
      m <- freshInstVarM s
      return (T.Var s (K.Proper ks m pk) InstLv v)
    _ -> internalError "non-proper instantiation kind"

-- | Make a fresh multiplicity instantiation variable.
freshInstVarM :: Span -> Validation K.Multiplicity
freshInstVarM s = do
  i <- incCounter 
  return $ K.VarM s InstLv (Variable s ("ṃ" ++ show i) i)
