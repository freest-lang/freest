module ReduceImpliesNotWhnfSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Normalisation      ( isWhnf, reduce )
import           UnitSpecUtils

import qualified Data.Map.Strict               as Map
import           Test.Hspec
import           Control.Exception             ( catch, ErrorCall )

-- This test should be called with well-formed types only

-- Type T reduces implies T is not a whnf.

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/WellFormedTypes.test"] 
  "If T reduces then T is not a whnf" 
  \(t, _, m) -> whnfImpliesNotReduces (buildDataDecls m) t >>= (`shouldBe` True)
  -- \(t, _, m) -> reducesImpliesNotWhnf (buildDataDecls m) t >>= (`shouldBe` True)

reducesImpliesNotWhnf :: TypeDeclMap -> T.Type -> IO Bool
reducesImpliesNotWhnf m t =
  catch
    (let !_ = reduce m t in pure (not (isWhnf t))) -- t reduces and is not in whnf
    (\(x::ErrorCall) -> pure True) -- t does not reduce

whnfImpliesNotReduces :: TypeDeclMap -> T.Type -> IO Bool
whnfImpliesNotReduces m t
  | isWhnf t = catch
      (let !_ = reduce m t in pure False)
      (\(x::ErrorCall) -> pure True)
  | otherwise = pure True

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
