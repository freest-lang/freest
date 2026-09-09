{- |
The fused pass has to typecheck with kinds it has not yet solved, so this runs
every valid program with the solution computed but not applied
('SolveAfterTyping') and records which ones survive.

Nothing here is a mode to ship. It is the measurement §5 of the fusion notes ran
once by hand, kept live. Almost nothing survives it yet — 10 of 279 — so the list
runs the other way from "ErasedSpec"'s: 'carried' names the programs the deferred
solve already carries, and a program leaving it is a regression. Grow it; the
staging can be flipped by default when it holds everything.
-}
module DeferredSpec (spec) where

import Compiler.Include (resolveIncludes)
import Compiler.Pipeline (validateModule)
import Parser.Parser (runParseModule)
import Parser.Scoping (emptyScopingCtx)
import ProgSpecUtils (specTest')
import Syntax.Declarations qualified as D
import Syntax.Module qualified as M
import UI.CLI (preludePath)
import UI.Error (Error, Source, showErrors)
import Validation.Base
  (Staging(..), emptyValidationState, runValidation, staging)
import Validation.Kinding (emptyKindCtx)
import Validation.Typing (emptyTypeCtx)

import Control.Exception (SomeException, displayException, evaluate, try)
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Paths_freest (getDataFileName)
import System.FilePath (takeFileName)
import Test.Hspec

spec :: Spec
spec = do
  prelude <- runIO (getDataFileName preludePath)
  specTest' "deferred" "/test/prog/Valid/" \_ (testFile, _) -> do
    -- as in "ErasedSpec": a program rejected either way says nothing about
    -- staging, so the eagerly-solved run is the control
    intact   <- accepts SolveDuringKinding prelude testFile
    deferred <- accepts SolveAfterTyping   prelude testFile
    case (intact, deferred) of
      (Right (), Left (_, errs))
        | takeFileName testFile `elem` carried -> expectationFailure
            ("the deferred solve used to carry this program and no longer "
              ++ "does:\n" ++ unlines errs)
        | otherwise -> pendingWith
            ("not yet carried by the deferred solve ("
              ++ show (length errs) ++ " error(s))")
      _ -> return ()

-- | The programs the deferred solve already carries. Every check that demands a
-- ground kind keeps one out; the clusters are catalogued in §5 of the fusion
-- notes. Grow this list; do not shrink it.
carried :: [FilePath]
carried =
  [ "A.fst", "B.fst", "Base.fst", "Compose.fst", "DagstuhlFeb2026.fst"
  , "Helper.fst", "ImplicitForall.fst", "MemoryCell.fst", "Pmap.fst"
  , "TypeVarNotShadowed.fst"
  ]

-- | Under the deferred staging a check that reads an unsolved kind does not
-- always fail politely: 'Compiler.Bug.internalError' and the irrefutable
-- patterns in the kinded smart constructors throw, so the result is forced
-- inside a handler and an exception counts as not carrying the program.
accepts :: Staging -> FilePath -> FilePath -> IO (Either (Source, [String]) ())
accepts stg prelude root = resolveIncludes [prelude, root] >>= \case
  Left _       -> pure (Right ())  -- an unreadable root is not this spec's business
  Right inputs -> do
    let outcome = first (map (showErrors (src inputs) . pure)) do
          modules <- mapM (uncurry runParseModule) inputs
          runValidation emptyValidationState{staging = stg} do
            _ <- validateModule emptyScopingCtx emptyKindCtx emptyTypeCtx
                   Map.empty D.emptyDataDecls
                   (M.insertBuiltinLists (mconcat modules))
            pure ()
    try (evaluate (either (foldr (seq . length) ()) (const ()) outcome) >> pure outcome) >>= \case
      Right r -> pure (first (src inputs,) r)
      Left  e -> pure (Left (src inputs, [displayException (e :: SomeException)]))
  where
    src inputs = Map.fromList [(p, lines t) | (p, t) <- inputs]
