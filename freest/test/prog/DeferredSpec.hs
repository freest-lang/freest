{- |
The fused pass has to typecheck with kinds it has not yet solved, so this runs
every valid program with the solution computed but not applied
('SolveAfterTyping') and records which ones survive.

Nothing here is a mode to ship. It is the measurement §5 of the fusion notes ran
once by hand, kept live. Most of the corpus survives it — 176 of the 272 programs
that compile at all — so the list runs the other way from "ErasedSpec"'s:
'carried' names the programs the deferred solve already carries, and a program
leaving it is a regression. Grow it; the staging can be flipped by default when
it holds everything.
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
import System.FilePath (splitDirectories, takeFileName, (</>))
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
        | testId testFile `elem` carried -> expectationFailure
            ("the deferred solve used to carry this program and no longer "
              ++ "does:\n" ++ unlines errs)
        | otherwise -> pendingWith
            ("not yet carried by the deferred solve ("
              ++ show (length errs) ++ " error(s))")
      _ -> return ()

-- | A program's key in 'carried': its group and file name, as hspec names it.
-- The file name alone is not unique — @PartialFork.fst@ and @Shape.fst@ each
-- occur in two groups, one carried and one not.
testId :: FilePath -> FilePath
testId p = case reverse (splitDirectories p) of
  file : _ : group : _ -> group </> file
  _                    -> takeFileName p

-- | The programs the deferred solve already carries. Every check that demands a
-- ground kind keeps one out; the clusters are catalogued in §5 of the fusion
-- notes. Grow this list; do not shrink it.
carried :: [FilePath]
carried =
  ["Applications/MovingAverage.fst", "Applications/OddEvenSort.fst"
  , "Applications/Tabuada.fst", "Existentials/Counter.fst"
  , "Existentials/FlipFlop.fst", "Existentials/MCounter.fst"
  , "Functional/ArrowLinType.fst", "Functional/ArrowType.fst"
  , "Functional/ArrowWithDataWithinType.fst", "Functional/Average.fst"
  , "Functional/BlockCommentInSig.fst", "Functional/BoolEq.fst"
  , "Functional/CaseRHS.fst", "Functional/CharBin.fst"
  , "Functional/CharEquality.fst", "Functional/Collect.fst"
  , "Functional/ConsAsFun.fst", "Functional/DataDiffNumBoundVars.fst"
  , "Functional/DataUn.fst", "Functional/DiffEqTypeNames.fst"
  , "Functional/DollarSumFilterMap.fst", "Functional/DoubleUnderscore.fst"
  , "Functional/EqDataAndCons.fst", "Functional/FEqG.fst"
  , "Functional/Fact.fst", "Functional/FunAsArg.fst", "Functional/Hungry.fst"
  , "Functional/IOFunAsPureArg.fst", "Functional/IntList.fst"
  , "Functional/IntListElem.fst", "Functional/IntListSize.fst"
  , "Functional/IntListSum.fst", "Functional/IsPrime.fst"
  , "Functional/LambdaHO.fst", "Functional/LinConsumedInBody.fst"
  , "Functional/ListEquality.fst", "Functional/MConsumedInMNFun.fst"
  , "Functional/MainMissing.fst", "Functional/MultDivPrecedence.fst"
  , "Functional/MultPrecedence.fst", "Functional/MultiVarTypeSig.fst"
  , "Functional/MultipleListTransformations.fst", "Functional/MultipleOps.fst"
  , "Functional/MultipleParens.fst", "Functional/MutualRecData.fst"
  , "Functional/NTuples.fst", "Functional/ParensPrecedence.fst"
  , "Functional/Processes.fst", "Functional/RecData.fst"
  , "Functional/RecFun.fst", "Functional/RecPair.fst", "Functional/Scope.fst"
  , "Functional/SemiAsSection.fst", "Functional/SemicolonPriority.fst"
  , "Functional/Shape.fst", "Functional/SimpleApp.fst"
  , "Functional/SimpleVar.fst", "Functional/SkipSkipSL.fst"
  , "Functional/TAppAssoc.fst", "Functional/Triple.fst"
  , "Functional/TypeDecl.fst", "IO/CountLines.fst", "IO/EchoLines.fst"
  , "IO/ExitChild.fst", "IO/ExitMain.fst", "IO/Files.fst"
  , "IO/GetCharUntil.fst", "IO/GetLine.fst", "IO/LookupEnv.fst"
  , "IO/Print.fst", "IO/PutChar.fst", "IO/PutStrLn.fst", "IO/PutString.fst"
  , "IO/StdErr.fst", "IO/YourNameIs.fst", "IO/getContent.fst"
  , "Include/BasicInclude.fst", "Include/Diamond.fst"
  , "Inference/CounterInferKind.fst", "Inference/FlipFlop.fst"
  , "Inference/ForallCapture.fst", "Inference/HigherKindedParam.fst"
  , "Inference/HigherKindedSynonym.fst", "Inference/MutualDataKinds.fst"
  , "Inference/NegativePats.fst", "Inference/ParamComponentInferUn.fst"
  , "Inference/QuantifierBareVarBody.fst", "Inference/SharedChannelSemi.fst"
  , "Inference/TypeInPatInferKind.fst", "Inference/TypeLambdaInferKind.fst"
  , "Sections/LeftSection.fst", "Sections/PolyMultSection.fst"
  , "Sections/PolySectionCheck.fst", "Sections/RightSection.fst"
  , "SessionTypes/ArithExprServerRegular.fst"
  , "SessionTypes/ArithExprServerRegular1.fst", "SessionTypes/BoolServer.fst"
  , "SessionTypes/BoolServer1.fst", "SessionTypes/BoolServer2.fst"
  , "SessionTypes/BoolServer3.fst", "SessionTypes/BoolServerRecursive.fst"
  , "SessionTypes/ChainOfChannelOps.fst", "SessionTypes/CloseSkipEnd.fst"
  , "SessionTypes/ConjunctionCase.fst", "SessionTypes/ConjunctionLambda.fst"
  , "SessionTypes/ConjunctionPattern.fst", "SessionTypes/CrissCross.fst"
  , "SessionTypes/Deadlock.fst", "SessionTypes/DualMessage.fst"
  , "SessionTypes/DupConsChan.fst", "SessionTypes/InInPat.fst"
  , "SessionTypes/InPat.fst", "SessionTypes/InfiniteChannels.fst"
  , "SessionTypes/Math.fst", "SessionTypes/Math1.fst"
  , "SessionTypes/NDualRec.fst", "SessionTypes/NegativePats.fst"
  , "SessionTypes/PartialFork.fst", "SessionTypes/PartialReceive.fst"
  , "SessionTypes/PartialSend.fst", "SessionTypes/PartiallyAppliedSelect.fst"
  , "SessionTypes/PingPongDiverge.fst"
  , "SessionTypes/PolyInstatiatedWithUnnormed.fst", "SessionTypes/RecChan.fst"
  , "SessionTypes/RegularTreeStream.fst"
  , "SessionTypes/RegularTreeStreamAlt.fst", "SessionTypes/SelectUn.fst"
  , "SessionTypes/SendAndClose.fst", "SessionTypes/SendAndWait.fst"
  , "SessionTypes/SendAsSendArg.fst", "SessionTypes/SendInt.fst"
  , "SessionTypes/SendList.fst", "SessionTypes/SendReceive.fst"
  , "SessionTypes/SendReceive1.fst", "SessionTypes/SendRecvSameThread.fst"
  , "SessionTypes/SendTreeRegular.fst", "SessionTypes/SessionsWithinData.fst"
  , "SessionTypes/SkipSkip.fst", "SessionTypes/TypeDefEnd.fst"
  , "SessionTypes/TypeInPat.fst", "SessionTypes/TypeNameInSig.fst"
  , "SessionTypes/TypeTeqU.fst", "SessionTypes/UnChoicePat.fst"
  , "SessionTypes/UnChoicePatAbbrev.fst", "SessionTypes/UnInPat.fst"
  , "SessionTypes/UnInPatAbbrev.fst", "SessionTypes/Unnormed.fst"
  , "SessionTypes/WaitPat.fst", "SharedChannels/CakeStoreFork.fst"
  , "SharedChannels/CakeStoreJoin.fst", "SharedChannels/FtpServer.fst"
  , "SharedChannels/Semaphore.fst", "SharedChannels/SharedBag.fst"
  , "SharedChannels/SharedMathServer.fst", "SharedChannels/SharedQueue.fst"
  , "SharedChannels/SyncChannel.fst", "SystemF/SystemFTrees.fst"
  , "Tutorial/Colour.fst", "Tutorial/Copy.fst", "Tutorial/CopyFun.fst"
  , "Tutorial/CopyFunStarredArrow.fst", "Tutorial/Discard.fst"
  , "Tutorial/DiscardFun.fst", "Tutorial/InfiniteParameters.fst"
  , "Tutorial/IntBinTree.fst", "Tutorial/IntLinType.fst"
  , "Tutorial/LinIntData.fst", "Tutorial/MainEndsLast.fst"
  , "Tutorial/MultipleArgs.fst", "Tutorial/MutualRecFun.fst"
  , "Tutorial/PartialAppliedLinFun.fst", "Tutorial/PartialAppliedUnLinFun.fst"
  , "Tutorial/RemoteAdder.fst", "Tutorial/SendClose.fst"
  , "Tutorial/TrafficLight.fst", "Tutorial/Void.fst" ]

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
