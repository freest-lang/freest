module WhnfOrReducesSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
import Validation.Normalisation ( isWhnf, reduce )

import Data.Map.Strict qualified as Map
import Test.Hspec
import UnitSpecUtils

-- This test should be called with well-formed types only

-- A given type T is either a WHNF or reduces

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkTypeSpec
  ["test/unit/WellFormedTypes.test"] 
  "A given type T is either a whnf or reduces"
  errorsAreFailures
  \(t, _, m) -> whnfOrReduces m t `shouldBe` True

whnfOrReduces :: M.Module -> T.Type -> Bool
whnfOrReduces m t = isWhnf t || let !_ = reduce (buildDataDecls m) t in True

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
