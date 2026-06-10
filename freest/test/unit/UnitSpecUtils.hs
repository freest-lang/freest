module UnitSpecUtils where

import Parser.LexerUtils ( runLexer )
import Parser.Parser
import Parser.Scoping
import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as TK
import Syntax.Type.Unkinded qualified as TU
import UI.Error (Error, Source, showErrors, printErrors)
import Validation.Kinding ( KindCtx, runKindModule, runSynth, runCheck )

import Control.Monad ( forM, forM_ )
import Control.Monad.Extra ( concatMapM )
import Data.Foldable ( foldlM )
import Data.Map qualified as Map
import System.Directory.Internal.Prelude ( exitFailure )
import Test.Hspec

mkTypeSpec :: [FilePath] 
              -> String 
              -> (Source -> [Error]                                       -> Expectation) 
              -> (Source -> (TU.ScopedType, Maybe K.Kind, M.ScopedModule) -> Expectation) 
              -> Spec
mkTypeSpec testPaths testDesc failHandler testHandler = do
  src <- zip testPaths <$> runIO (mapM readFile testPaths)
  let src' = lines <$> Map.fromList src
  case concatMapM (uncurry $ runLexer parseKindingTests) src of
    Left es  -> runIO $ printErrors src' es >> exitFailure
    Right ts -> describe testDesc $ 
      forM_ ts \((t, k), m) -> it
        (show (getSpan t))
        case runScoping scopeKindingTest (t, k, m) of
          Left es          -> failHandler src' es
          Right (t, k, m)  -> testHandler src' (t, k, m) 
  where
    scopeKindingTest ctx (t, k, m) = do
      (ctx,m') <- scopeModule' ctx m
      t' <- scopeType ctx t
      k' <- mapM (scopeKind ctx) k
      return (t', k', m')

errorsAreFailures, errorsAreSuccesses :: Source -> [Error] -> Expectation
errorsAreFailures  src es = expectationFailure (showErrors src es)
errorsAreSuccesses _   _  = return ()

mkEquivalenceSpec :: [FilePath] 
                  -> String 
                  -> (Source -> (TK.KindedType, TK.KindedType, K.Kind, M.KindedModule) -> Expectation) 
                  -> Spec
mkEquivalenceSpec testPaths testDesc testFun = do
  src <- zip testPaths <$> runIO (mapM readFile testPaths)
  let src' = lines <$> Map.fromList src
  case concatMapM (uncurry $ runLexer parseEquivalenceTests) src of
    Left es  -> runIO $ printErrors src' es
    Right ts -> describe testDesc $ 
      forM_ ts \((t, u, k), m) -> it (show (spanFromTo t u))
        case do (t', u', k', m') <- runScoping scopeEquivalenceTest (t, u, k, m)
                (kctx, m'') <- runKindModule m'
                t'' <- runCheck kctx t' k'
                u'' <- runCheck kctx u' k'
                return (t'', u'', k', m'') of
          Left es      -> expectationFailure (showErrors src' es)
          Right (t', u', k', m'') -> testFun src' (t', u', k', m'')
  where
    scopeEquivalenceTest ctx (t, u, k, m) = do
      (ctx',m') <- scopeModule' ctx m
      t' <- scopeType ctx' t
      u' <- scopeType ctx' u
      k' <- scopeKind ctx' k
      return (t', u', k', m')

runSynthOrCheck :: KindCtx -> TU.ScopedType -> Maybe K.Kind -> Either [Error] TK.KindedType
runSynthOrCheck kctx t = \case
  Nothing -> runSynth kctx t
  Just k  -> runCheck kctx t k