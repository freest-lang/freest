module UnitSpecUtils where

import           Parser.LexerUtils (runLexer)
import           Parser.Parser
import           Parser.Scoping
import qualified Syntax.Module as M
import qualified Syntax.Type as T

import           Control.Monad (forM, forM_)
import qualified Data.Map as Map
import           Test.Hspec

mkSpec :: FilePath -> String -> ((T.Type, T.Type, M.Module) -> Spec) -> Spec
mkSpec testPath testDesc testFun = do
  source <- runIO $ readFile testPath
  case runLexer parseTypeCmpTests testPath source 
       >>= runScoping scopeTypeCmpTests of
    Left es  -> runIO $ mapM_ print es
    Right ts -> describe testDesc $ 
      -- TODO: kinding, duality, etc.
      forM_ ts testFun

scopeTypeCmpTests :: ScopingCtx -> [(T.Type, T.Type, M.Module)] -> Scoping [(T.Type, T.Type, M.Module)]
scopeTypeCmpTests ctx ts =
  forM ts (scopeTypeCmpTest ctx)
  where
    scopeTypeCmpTest ctx (t,u,m) = do
      (ctx,m') <- scopeModule ctx m
      t' <- scopeType ctx t
      u' <- scopeType ctx u
      return (t',u',m')