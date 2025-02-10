module WhnfOrReducesSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Normalisation      ( isWhnf, reduce )

import qualified Data.Map.Strict               as Map
import           Test.Hspec
import           UnitSpecUtils

-- This test should be called with well-formed types only

-- A given type T is either a WHNF or reduces

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/KindingValid.test"] 
  "A given type T is either a whnf or reduces" 
  \(t, _, m) -> whnfOrReduces m t `shouldBe` True

whnfOrReduces :: M.Module -> T.Type -> Bool
whnfOrReduces m t = isWhnf t || let !_ = reduce (buildDataDecls m) t in True

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
