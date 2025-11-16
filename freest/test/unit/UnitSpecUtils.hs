module UnitSpecUtils where

import Parser.LexerUtils ( runLexer )
import Parser.Parser
import Parser.Scoping
import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import UI.Error (Error, Source, showErrors, printErrors)
import Validation.Kinding ( runKindModule )

import Control.Monad ( forM, forM_ )
import Control.Monad.Extra ( concatMapM )
import Data.Foldable ( foldlM )
import Data.Map qualified as Map
import System.Directory.Internal.Prelude ( exitFailure )
import Test.Hspec

mkTypeSpec :: [FilePath] 
              -> String 
              -> (Source -> [Error]                          -> Expectation) 
              -> (Source -> (T.Type, Maybe K.Kind, M.Module) -> Expectation) 
              -> Spec
mkTypeSpec testPaths testDesc failHandler testHandler = do
  src <- zip testPaths <$> runIO (mapM readFile testPaths)
  let src' = lines <$> Map.fromList src
  case concatMapM (uncurry $ runLexer parseKindingTests) src of
    Left es  -> runIO $ printErrors src' es >> exitFailure
    Right ts -> describe testDesc $ 
      forM_ ts \((t, k), m) -> it
        (show (getSpan t))
        case runScoping scopeKindingTest (t, k, m) >>= kindKindingTest of
          Left es          -> failHandler src' es
          Right (t, k, m)  -> testHandler src' (t, k, m) 
  where
    scopeKindingTest ctx (t, k, m) = do
      (ctx,m') <- scopeModule' ctx m
      t' <- scopeType ctx t
      k' <- mapM scopeKind k
      return (t', k', m')
    kindKindingTest (t, k, m) = (t, k,) <$> runKindModule m

errorsAreFailures, errorsAreSuccesses :: Source -> [Error] -> Expectation
errorsAreFailures  src es = expectationFailure (showErrors src es)
errorsAreSuccesses _   _  = return ()

mkEquivalenceSpec :: [FilePath] 
                  -> String 
                  -> (Source -> (T.Type, T.Type, K.Kind, M.Module) -> Expectation) 
                  -> Spec
mkEquivalenceSpec testPaths testDesc testFun = do
  src <- zip testPaths <$> runIO (mapM readFile testPaths)
  let src' = lines <$> Map.fromList src
  case concatMapM (uncurry $ runLexer parseEquivalenceTests) src of
    Left es  -> runIO $ printErrors src' es
    Right ts -> describe testDesc $ 
      forM_ ts \((t, u, k), m) -> it (show (spanFromTo t u))
        case do (t', u', k', m') <- runScoping scopeEquivalenceTest (t, u, k, m)
                (t', u', k',) <$> runKindModule m' of
          Left es      -> expectationFailure (showErrors src' es)
          Right (t', u', k', m'') -> testFun src' (t', u', k', m'')
  where
    scopeEquivalenceTest ctx (t, u, k, m) = do
      (ctx',m') <- scopeModule' ctx m
      t' <- scopeType ctx' t
      u' <- scopeType ctx' u
      k' <- scopeKind k
      return (t', u', k', m')
