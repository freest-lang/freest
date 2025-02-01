module ReducesImpliesNotWhnfSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Normalisation      ( isWhnf, reduce )
import           UnitSpecUtils

import qualified Data.Map.Strict               as Map
import           Test.Hspec
import           Control.Exception             ( catch, ErrorCall )

-- This test should be called with well-formed types only

-- Type T reduces implies T is not q whnf. Equivalently, T does not reduce or T
-- is a whnf.

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/KindingValid.test" 
  "If T reduces, then T is not a whnf" 
  \(t, _, m) -> reducesImpliesNotWhnf (buildDataDecls m) t >>= (`shouldBe` True)

reducesImpliesNotWhnf :: TypeDeclMap -> T.Type -> IO Bool
reducesImpliesNotWhnf m t =
  catch
    (let !_ = reduce m t in pure (not (isWhnf t)))
    (\(x::ErrorCall) -> pure True)

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
