module RenamePreservesWhnfSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Kinding ( runKindModule )
import Validation.Rename
import Validation.Normalisation ( isWhnf )
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec

-- Requires: This test should be called with well-formed types only

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "T is a whnf iff rename T is a whnf"
  errorsAreFailures
  \_ (t, mk, m) -> case (,) <$> runKindModule m <*> runSynthOrCheck m t mk of
    Left _ -> expectationFailure "Kinding error"
    Right (m', t') -> isWhnf t' == isWhnf (rename (M.typeDecls m') t') `shouldBe` True

