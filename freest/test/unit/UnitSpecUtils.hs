module UnitSpecUtils where

import           Parser.LexerUtils (runLexer)
import           Parser.Parser
import           Parser.Scoping
import qualified Syntax.Kind as K
import qualified Syntax.Module as M
import qualified Syntax.Type as T

import           Control.Monad (forM, forM_)
import qualified Data.Map as Map
import           Test.Hspec
import           Validation.Kinding (runKindModule)
import Syntax.Base
import System.Directory.Internal.Prelude (exitFailure)

mkKindingSpec :: FilePath -> String -> ((T.Type, Maybe K.Kind, M.Module) -> Expectation) -> Spec
mkKindingSpec testPath testDesc testFun = do
  source <- runIO $ readFile testPath
  case runLexer parseKindingTests testPath source of
    Left es  -> runIO $ mapM_ print es >> exitFailure
    Right ts -> describe testDesc $ 
      forM_ ts \((t, k), m) -> it
        (show (getSpan t))
        case do (t', k', m') <- runScoping scopeKindingTest (t, k, m) 
                runKindModule m'
                return (t', k', m') of
          Left es      -> expectationFailure (unlines $ map show es)
          Right (t, k, m)  -> testFun (t, k, m) 
  where 
    scopeKindingTest ctx (t, k, m) = do
      (ctx,m') <- scopeModule ctx m
      t' <- scopeType ctx t
      k' <- mapM scopeKind k
      return (t', k', m')

mkEquivalenceSpec :: FilePath -> String -> ((T.Type, T.Type, M.Module) -> Expectation) -> Spec
mkEquivalenceSpec testPath testDesc testFun = do
  source <- runIO $ readFile testPath
  case runLexer parseEquivalenceTests testPath source of
    Left es  -> runIO $ mapM_ print es
    Right ts -> describe testDesc $ 
      forM_ ts \((t, u), m) -> it
        (show t ++ " ~ " ++ show u)
        case do (t', u', m') <- runScoping scopeEquivalenceTest (t, u, m)
                runKindModule m'
                return (t', u', m') of
          Left es      -> expectationFailure (unlines $ map show es)
          Right (t, u, m) -> testFun (t, u, m)
  where
    scopeEquivalenceTest ctx (t, u, m) = do
      (ctx,m') <- scopeModule ctx m
      t' <- scopeType ctx t
      u' <- scopeType ctx u
      return (t',u',m')
