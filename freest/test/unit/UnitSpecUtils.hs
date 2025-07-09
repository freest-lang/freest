module UnitSpecUtils where

import Parser.LexerUtils ( runLexer )
import Parser.Parser
import Parser.Scoping
import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import UI.Error (Error)
import Validation.Kinding ( runKindModule )

import Control.Monad ( forM, forM_ )
import Control.Monad.Extra ( concatMapM )
import Data.Foldable ( foldlM )
import Data.Map qualified as Map
import System.Directory.Internal.Prelude ( exitFailure )
import Test.Hspec

mkTypeSpec :: [FilePath] 
              -> String 
              -> ([Error]                          -> Expectation) 
              -> ((T.Type, Maybe K.Kind, M.Module) -> Expectation) 
              -> Spec
mkTypeSpec testPaths testDesc failHandler testHandler = do
  sources <- zip testPaths <$> runIO (mapM readFile testPaths)
  case concatMapM (uncurry $ runLexer parseKindingTests) sources of
    Left es  -> runIO $ mapM_ print es >> exitFailure
    Right ts -> describe testDesc $ 
      forM_ ts \((t, k), m) -> it
        (show (getSpan t))
        case runScoping scopeKindingTest (t, k, m) >>= kindKindingTest of
          Left es          -> failHandler es
          Right (t, k, m)  -> testHandler (t, k, m) 
  where
    scopeKindingTest ctx (t, k, m) = do
      (ctx,m') <- scopeModule' ctx m
      t' <- scopeType ctx t
      k' <- mapM scopeKind k
      return (t', k', m')
    kindKindingTest (t, k, m) = (t, k,) <$> runKindModule m

errorsAreFailures, errorsAreSuccesses :: [Error] -> Expectation
errorsAreFailures  es = expectationFailure (unlines $ map show es)
errorsAreSuccesses _  = return ()

mkEquivalenceSpec :: [FilePath] -> String -> ((T.Type, T.Type, K.Kind, M.Module) -> Expectation) -> Spec
mkEquivalenceSpec testPaths testDesc testFun = do
  sources <- zip testPaths <$> runIO (mapM readFile testPaths)
  case concatMapM (uncurry $ runLexer parseEquivalenceTests) sources of
    Left es  -> runIO $ mapM_ print es
    Right ts -> describe testDesc $ 
      forM_ ts \((t, u, k), m) -> it (show (spanFromTo t u))
        case do (t', u', k', m') <- runScoping scopeEquivalenceTest (t, u, k, m)
                (t', u', k',) <$> runKindModule m' of
          Left es      -> expectationFailure (unlines $ map show es)
          Right (t', u', k', m'') -> testFun (t', u', k', m'')
  where
    scopeEquivalenceTest ctx (t, u, k, m) = do
      (ctx',m') <- scopeModule' ctx m
      t' <- scopeType ctx' t
      u' <- scopeType ctx' u
      k' <- scopeKind k
      return (t', u', k', m')
