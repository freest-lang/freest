module NormalisationPreservesReachableSpec (spec) where

import Syntax.Base ( getSpan )
import Syntax.Kind
import Syntax.Module qualified as M
import Validation.Base ( TypeDeclMap )
import Validation.Rename
import Validation.Normalisation
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
import Debug.Trace ( trace )

main :: IO ()
main = hspec spec

-- This test should be called with well-formed types only

-- If T normalises to U, then reach(T) = reach(U).

spec :: Spec
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test" ]
  "Normalisation preserves free reachable variables"
  \case
    (t, Just k, m) ->
      trace ("\n" ++ show t ++ show tReachable ++ " and " ++ show u  ++ show uReachable)
      tReachable == uReachable `shouldBe` True
      where
        td = buildTypeDecls m
        tReachable = reachable td t
        u = normalise td t
        uReachable = reachable td u
    _ -> expectationFailure "Ill formed test case: kind annotation absent"

-- Warning: code also in from Validation.Base
buildTypeDecls :: M.Module -> TypeDeclMap
buildTypeDecls = Map.fromList . M.typeDecls
