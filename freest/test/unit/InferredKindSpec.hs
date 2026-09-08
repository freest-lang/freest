{- |
Annotation erasure, after the paper's evaluation method: strip a well-formed
type of its written binder kinds and require what is synthesised to still
satisfy the kind the corpus declares. A failure means inference has become less
precise than annotation — the property the kind-inference work exists to hold.
-}
module InferredKindSpec (spec) where

import Syntax.Kind qualified as K
import Syntax.Type.Kinded qualified as TK
import Syntax.Type.Unkinded qualified as TU
import UI.Error (showErrors)
import UnitSpecUtils
import Validation.Kinding (runKindModule, runSynth)

import Control.Monad (unless)
import Test.Hspec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"]
  "Inferred kind of an annotation-erased type still satisfies the declared kind"
  errorsAreFailures
  \src -> \case
    (t, Just k, m) ->
      case runKindModule m >>= \(kctx, _) -> runSynth kctx (eraseBinderKinds t) of
        Left es -> expectationFailure (showErrors src es)
        Right t' -> do
          -- the corpus declares a kind the type has, not its minimal one — so
          -- this is subsumption, and erasure must not push the synthesised kind
          -- above the declared bound. (Not the paper's Fig. 15 metric, which
          -- asks the opposite of a *binder's* annotation.)
          let k' = TK.kindOf t'
          unless (k' K.<: k) $ expectationFailure
            ("erased type synthesised `" ++ show k' ++ "`, which no longer "
              ++ "satisfies the declared `" ++ show k ++ "`")
    (_, Nothing, _) -> expectationFailure "test case is missing its expected kind"

-- | A quantifier's binder kind removed wherever inference is meant to supply
-- it. Absence, not a fresh variable: a placeholder is what the representation
-- is meant to be rid of.
--
-- Two binders are kept, both the same open face — an arrow kind has no
-- component the body constrains, so erasing one measures the default and
-- nothing else. A type operator's domain is one (@\\(a : *T) -> a@), and so is
-- a higher-kinded quantifier binder (@forall (t : *T -> *T) -> …@). Widen this
-- when arrow-kind components are inferred.
eraseBinderKinds :: TU.ScopedType -> TU.ScopedType
eraseBinderKinds = \case
  TU.AppQuant s p bk m aks t ->
    TU.AppQuant s p bk m (map eraseProper aks) (eraseBinderKinds t)
  TU.Abs s aks t      -> TU.Abs s aks (eraseBinderKinds t)
  TU.App s t ts       -> TU.App s (eraseBinderKinds t) (map eraseBinderKinds ts)
  TU.ForallM s m φs t -> TU.ForallM s m φs (eraseBinderKinds t)
  t                   -> t
  where
    eraseProper ak@(_, Just K.Arrow{}) = ak
    eraseProper (a, _)                 = (a, Nothing)
