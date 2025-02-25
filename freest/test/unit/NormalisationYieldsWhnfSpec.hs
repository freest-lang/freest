module NormalisationYieldsWhnfSpec (spec) where

import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
import Validation.Normalisation ( normalise, isWhnf )
import UnitSpecUtils

import Data.Map.Strict qualified as Map
import Test.Hspec
-- import           Debug.Trace

-- This test should be called with well-formed types only

-- Note: this spec tests very little. As it is, the normalise function returns a
-- whnf, if it returns at all.

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test"] 
  "If T normalises to U, then U is a whnf" 
  \(t, _, m) -> normYieldsWhnf (buildDataDecls m) t `shouldBe` True

normYieldsWhnf :: TypeDeclMap -> T.Type -> Bool
normYieldsWhnf td t = isWhnf {-$ trace (show $ normalise td t)-} (normalise td t)

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
