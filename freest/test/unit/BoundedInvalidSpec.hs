module BoundedInvalidSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Rename            ( bounded )
import           Validation.Normalisation   ( normalise )
import           UnitSpecUtils

import qualified Data.Map.Strict               as Map
import           Test.Hspec

-- This test should be called with well-formed types only

-- Note: this spec tests very little. As it is, the normalise function returns a
-- whnf, if it returns at all.

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  "test/unit/BoundedInvalid.test" 
  "Unbounded types" 
  \(t,m) -> isBounded m t `shouldBe` False

isBounded :: M.Module -> T.Type -> Bool
isBounded m t = bounded dd $ normalise dd t
  where dd = buildDataDecls m

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls
