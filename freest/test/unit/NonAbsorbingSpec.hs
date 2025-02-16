module NonAbsorbingSpec (spec) where

import qualified Syntax.Kind                   as K
import qualified Validation.Rename             as R
import           Validation.Base               ( TypeDeclMap )
import qualified Syntax.Module                 as M
import           UnitSpecUtils

import qualified Data.Map.Strict               as Map
import           Test.Hspec


main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/KindingValid.test" 
  "Non absorbing types"
  \case
    (t, Just k, m) | K.isStrictlySession k && R.isAbsorbing (buildDataDecls m) t -> K.isStrictlyAbsorbing k `shouldBe` True
    _ -> return ()

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
