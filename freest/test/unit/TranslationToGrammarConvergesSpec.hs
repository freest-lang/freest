module TranslationToGrammarConvergesSpec (spec) where

import qualified Syntax.Module                 as M
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.TypeEquivalence.FromType ( fromType )
import           Validation.TypeEquivalence.Grammar
import           UnitSpecUtils

import qualified Data.Map.Strict               as Map
import           Test.Hspec
import           Debug.Trace

-- Requires: This test should be called with well-formed types only

-- Test success is simply termination

main :: IO ()
main = hspec spec

spec :: Spec
spec = mkKindingSpec
  ["test/unit/KindingValid.test"] 
  "Type translation to grammar converges" 
  \(t,_,m) -> translateToGrammar (buildDataDecls m) t `shouldBe` True

translateToGrammar :: TypeDeclMap -> T.Type -> Bool
translateToGrammar td t = let !_ = trace ("\n" ++ show (fromType td [t])) () in True

-- Warning: code also in from Validation.Base
buildDataDecls :: M.Module -> TypeDeclMap
buildDataDecls = Map.fromList . M.typeDecls

