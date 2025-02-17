module NormalisationYieldsWhnfSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Normalisation      ( normalise, isWhnf )
import           UnitSpecUtils

import qualified Data.Map.Strict               as Map
import           Test.Hspec
-- import           Debug.Trace

-- This test should be called with well-formed types only

-- Note: this spec tests very little. As it is, the normalise function returns a
-- whnf, if it returns at all.

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/WellFormedTypes.test" 
  "If T normalises to U, then U is a whnf" 
  \(t, _, m) -> normYieldsWhnf (buildDataDecls m) t `shouldBe` True

normYieldsWhnf :: TypeDeclMap -> T.Type -> Bool
normYieldsWhnf td t = isWhnf {-$ trace (show $ normalise td t)-} (normalise td t)

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
