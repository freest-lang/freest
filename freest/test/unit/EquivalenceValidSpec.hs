module EquivalenceValidSpec (spec) where

import           Parser.LexerUtils (runLexer)
import           Parser.Parser
import           Parser.Scoping
import qualified Syntax.Type as T
import qualified Syntax.Module as M
import           TypeEquivalence.TypeEquivalence (equivalent)

import           Control.Monad (forM, forM_)
import qualified Data.Map as Map
import           Test.Hspec

main :: IO ()
main = hspec spec

scopeTypeCmpTests :: ScopingCtx -> [(T.Type, T.Type, M.Module)] -> Scoping [(T.Type, T.Type, M.Module)]
scopeTypeCmpTests ctx ts =
  forM ts (scopeTypeCmpTest ctx)
  where
    scopeTypeCmpTest ctx (t,u,m) = do
      (ctx,m') <- scopeModule ctx m
      t' <- scopeType ctx t
      u' <- scopeType ctx u
      return (t',u',m')

spec :: Spec
spec = do
  let testPath = "test/unit/EquivalenceValid.test"
  source <- runIO $ readFile testPath
  case runLexer parseTypeCmpTests testPath source 
       >>= runScoping scopeTypeCmpTests of
    Left es  -> runIO $ mapM_ print es
    Right ts -> describe "Valid equivalence tests" $ 
      -- TODO: kinding, duality, etc.
      forM_ ts \(t,u,m) -> it
        (show t ++ " ~ " ++ show u)
        (equivalent m t u `shouldBe` True)