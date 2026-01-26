module RenamePreservesReductionSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Kinding ( runKindModule )
import Validation.Rename
import Validation.Normalisation ( reduce, isWhnf )
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec

-- Requires: This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "If T reduces to U, then rename T reduces to rename U"
  errorsAreFailures
  \_ (t, mk, m) -> case (,) <$> runKindModule m <*> runSynthOrCheck m t mk of
    Left _ -> expectationFailure "Kinding error"
    Right (m', t') -> renamePreservesReduction `shouldBe` True
      where
        td = M.typeDecls m'
        renamePreservesReduction = isWhnf t' || u == u'
          where u  = reduce td t'
                u' = reduce td (rename td t')

