module NormalisationYieldsWhnfSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           SimpleGrammar.Normalisation   ( normalise, isWhnf )

import qualified Data.Map.Strict               as Map
import           Test.Hspec
import           UnitSpecUtils

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/KindingValid.test" 
  "Normalisation yields WHNF tests" 
  \(t,m) -> normYieldsWnnf m t `shouldBe` True

normYieldsWnnf :: M.Module -> T.Type -> Bool
normYieldsWnnf m t = isWhnf $ normalise (buildDataDecls m) t

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls m = Map.fromList (M.typeDecls m)
