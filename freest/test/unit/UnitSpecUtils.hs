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
import Data.Foldable (foldlM)
import Control.Monad.Extra (concatMapM)

mkKindingSpec :: [FilePath] -> String -> ((T.Type, Maybe K.Kind, M.Module) -> Expectation) -> Spec
mkKindingSpec testPaths testDesc testFun = do
  sources <- zip testPaths <$> runIO (mapM readFile testPaths)
  case concatMapM (uncurry $ runLexer parseKindingTests) sources of
    Left es  -> runIO $ mapM_ print es >> exitFailure
    Right ts -> describe testDesc $ 
      forM_ ts \((t, k), m) -> it
        (show (getSpan t))
        case runScoping scopeKindingTest (t, k, m) of
          Left es      -> expectationFailure (unlines $ map show es)
          Right (t, k, m)  -> testFun (t, k, m) 
  where
    scopeKindingTest ctx (t, k, m) = do
      (ctx,m') <- scopeModule' ctx m
      t' <- scopeType ctx t
      k' <- mapM scopeKind k
      return (t', k', m')

mkEquivalenceSpec :: [FilePath] -> String -> ((T.Type, T.Type, K.Kind, M.Module) -> Expectation) -> Spec
mkEquivalenceSpec testPaths testDesc testFun = do
  sources <- zip testPaths <$> runIO (mapM readFile testPaths)
  case concatMapM (uncurry $ runLexer parseEquivalenceTests) sources of
    Left es  -> runIO $ mapM_ print es
    Right ts -> describe testDesc $ 
      forM_ ts \((t, u, k), m) -> it (show (spanFromTo t u))
        case do (t', u', k', m') <- runScoping scopeEquivalenceTest (t, u, k, m)
                runKindModule m'
                return (t', u',k', m') of
          Left es      -> expectationFailure (unlines $ map show es)
          Right (t', u', k', m') -> testFun (t', u', k', m')
  where
    scopeEquivalenceTest ctx (t, u, k, m) = do
      (ctx',m') <- scopeModule' ctx m
      t' <- scopeType ctx' t
      u' <- scopeType ctx' u
      k' <- scopeKind k
      return (t', u', k', m')
