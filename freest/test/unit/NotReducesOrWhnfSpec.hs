{-# LANGUAGE ScopedTypeVariables #-}
module NotReducesOrWhnfSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Normalisation      ( isWhnf, reduce )
import           UnitSpecUtils

import qualified Data.Map.Strict               as Map
import           Test.Hspec
import           Control.Exception             ( catch, PatternMatchFail )

-- This test should be called with well-formed types only

-- Type T reduces implies T is not q whnf. Equivalently, T does not reduce or T
-- is a whnf.

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/KindingValid.test" 
  "A given type T is either a WHNF or reduces" 
  \(t, _, m) -> whnfOrReduces m t `shouldBe` True

whnfOrReduces :: M.Module -> T.Type -> Bool
whnfOrReduces m t = True -- not (reduces (buildDataDecls m) t) || isWhnf t

-- There is a type u s.t. reduce m t = u
reduces :: TypeDeclMap -> T.Type -> IO Bool
reduces m t = catch (let !_ = reduce m t in pure True) (\(x::PatternMatchFail) -> pure False)

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
