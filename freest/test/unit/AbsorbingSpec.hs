module AbsorbingSpec (spec) where

import qualified Syntax.Kind                   as K
-- import qualified Validation.Rename             as A
import qualified Validation.Kinding            as A
import           UnitSpecUtils

import           Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/KindingValid.test" 
  "Absorbing types" 
  \case
    (t, Just k, m) | K.isStrictlyAbsorbing k -> A.isAbsorbing m t `shouldBe` True
    _ -> error "Ill formed test case: missing kind annotation"
