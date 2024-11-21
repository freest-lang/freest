module EquivalenceInvalidSpec (spec) where

import           Parser.LexerUtils (runLexer)
import           Parser.Parser
import qualified Syntax.Type as T
import qualified Syntax.Module as M
import           TypeEquivalence.TypeEquivalence (equivalent)

import           Control.Monad (forM_)
import           Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  let testPath = "test/unit/EquivalenceInvalid.test"
  source <- runIO $ readFile testPath
  case runLexer parseTypeCmpTests testPath source of
    Left es  -> runIO $ mapM_ print es
    Right ts -> describe "Invalid equivalence tests" $ 
      -- TODO: kinding, duality, etc.
      forM_ ts \(t,u,m) -> it
        (show t ++ " ~ " ++ show u)
        (equivalent m t u `shouldBe` False)