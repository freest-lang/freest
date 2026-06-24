module InferredKindSubkindSpec (spec) where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Unkinded qualified as TU
import Syntax.Type.Kinded qualified as TK
import UI.Error (showErrors)
import UnitSpecUtils (mkTypeSpec, errorsAreFailures)
import Validation.Kinding (runKindModule, runSynth)

import Control.Monad (unless)
import Test.Hspec (Spec, expectationFailure, hspec)

main :: IO ()
main = hspec spec

-- | For each well-formed type @T@ annotated with a declared kind @K@:
--
--     1. replace every concrete kind annotation (a 'K.Proper' or 'K.Arrow')
--        occurring in @T@ by a fresh kind variable ('K.Var');
--     2. run kind synthesis on the resulting type;
--     3. the synthesised kind must be a subkind of the declared kind @K@.
--
-- Erasing the annotations to variables turns each binder into an unannotated
-- one, so synthesis must recover a kind at least as precise as the one the
-- programmer wrote down.
--
-- NOTE: this is a /target/ specification for the kind-inference work, not a
-- currently-passing test. 'runSynth' gathers constraints but does not solve
-- them, and 'K.Var' is rigid under '(K.<:)' (it relates only to itself), so an
-- erased variable is never resolved back to a concrete kind. Two families of
-- cases therefore fail today and should pass once inference resolves the
-- variables:
--
--     * 'TU.Void' @\@κ@: @kindOf (Void κ) = κ@, so the synthesised kind is the
--       bare variable, and e.g. @κ \<: *C@ is 'False'.
--     * an erased binder variable applied in a concrete-kind position, e.g.
--       @forall (a : κ) -> Alpha a@ with @Alpha : 1S -> 1T@, forces
--       @check a 1S@, i.e. @κ \<: 1S = False@.
spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"]
  "If T : K then the inferred kind of the annotation-erased T is a subkind of K"
  errorsAreFailures
  \src -> \case
    (_, Nothing, _) ->
      expectationFailure "Ill formed test case: missing kind annotation"
    (t, Just k, m) ->
      case runKindModule m >>= \(kctx, _) -> runSynth kctx (eraseKinds t) of
        Left es  -> expectationFailure (showErrors src es)
        Right kt ->
          let k' = TK.kindOf kt in
          unless (k' K.<: k) $ expectationFailure $
            "inferred kind `" ++ show k' ++ "` is not a subkind of the declared kind `"
            ++ show k ++ "`"

-- | Replace every concrete kind annotation in a type by a fresh kind variable.
-- Annotations occur on 'TU.Abs' binders and on 'TU.Void'.
eraseKinds :: TU.ScopedType -> TU.ScopedType
eraseKinds = fst . erase 0
  where
    erase :: Int -> TU.ScopedType -> (TU.ScopedType, Int)
    erase n = \case
      TU.Void s k         -> let (k', n')   = variseKind n k
                             in (TU.Void s k', n')
      TU.Abs s aks t      -> let (aks', n')  = variseBinders n aks
                                 (t', n'')   = erase n' t
                             in (TU.Abs s aks' t', n'')
      TU.App s t ts       -> let (t', n')    = erase n t
                                 (ts', n'')  = eraseAll n' ts
                             in (TU.App s t' ts', n'')
      TU.ForallM s m φs t -> let (t', n')    = erase n t
                             in (TU.ForallM s m φs t', n')
      t                   -> (t, n)

    eraseAll :: Int -> [TU.ScopedType] -> ([TU.ScopedType], Int)
    eraseAll n []       = ([], n)
    eraseAll n (t : ts) = let (t', n')   = erase n t
                              (ts', n'')  = eraseAll n' ts
                          in (t' : ts', n'')

    variseBinders :: Int -> [(Variable, K.Kind)] -> ([(Variable, K.Kind)], Int)
    variseBinders n []             = ([], n)
    variseBinders n ((a, k) : aks) = let (k', n')    = variseKind n k
                                         (aks', n'')  = variseBinders n' aks
                                     in ((a, k') : aks', n'')

    -- A 'K.Proper' or 'K.Arrow' annotation becomes a fresh kind variable; an
    -- annotation that is already a 'K.Var' is left untouched.
    variseKind :: Int -> K.Kind -> (K.Kind, Int)
    variseKind n = \case
      k@K.Var{} -> (k, n)
      k         -> (K.Var (getSpan k) (Variable (getSpan k) "κ" n), n + 1)
