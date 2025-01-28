module RenameIsIdempotentSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Rename
import qualified Data.Map.Strict               as Map
import           Test.Hspec
import           UnitSpecUtils

-- This test should be called with well-formed types only

-- Note: this spec tests very little. As it is, the normalise function returns a
-- whnf, if it returns at all.

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/KindingValid.test" 
  "Rename is idempontent tests" 
  \(t,_,m) -> normYieldsWnnf m t `shouldBe` True

normYieldsWnnf :: M.Module -> T.Type -> Bool
normYieldsWnnf m t = rename dd t == rename dd (rename dd t)
  where dd = buildDataDecls m

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
