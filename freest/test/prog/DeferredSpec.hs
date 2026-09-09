{- |
'SolveAfterTyping' is now the default, so what this spec measures has inverted:
it ran to grow the deferred staging up to the eager one, and it now guards that
the two still agree, running each program under both. 'carried' names the
programs the deferred staging carries — all 272 that compile — and a program
leaving it is a regression. It should be retired when 'Staging' goes and the
eager path with it.

What is deferred is multiplicities. Shape and baseKinds are settled before
typing: those are determined by the types alone (the paper infers them in §4,
over types), whereas multiplicities are what usage decides (§5, over
expressions), and they are all that a fused pass must carry unsolved.
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
  ["Applications/Genetic.fst", "Applications/Json.fst"
  , "Applications/MovingAverage.fst", "Applications/OddEvenSort.fst"
  , "Applications/Ordering.fst", "Applications/Sorting.fst"
  , "Applications/Tabuada.fst", "Applications/TechStore.fst"
  , "Existentials/Counter.fst", "Existentials/FlipFlop.fst"
  , "Existentials/HTree.fst", "Existentials/MCounter.fst"
  , "Existentials/RemoteCounter.fst", "Existentials/RemoteLazyCounter.fst"
  , "Existentials/Stack.fst", "Functional/ArrowLinType.fst"
  , "Functional/ArrowType.fst", "Functional/ArrowWithDataWithinType.fst"
  , "Functional/Average.fst", "Functional/BlockCommentInSig.fst"
  , "Functional/BoolEq.fst", "Functional/CaseRHS.fst"
  , "Functional/CharBin.fst", "Functional/CharEquality.fst"
  , "Functional/Collect.fst", "Functional/ConsAsFun.fst"
  , "Functional/DataDiffNumBoundVars.fst", "Functional/DataUn.fst"
  , "Functional/DiffEqTypeNames.fst", "Functional/DollarSumFilterMap.fst"
  , "Functional/Dot.fst", "Functional/DoubleUnderscore.fst"
  , "Functional/EqDataAndCons.fst", "Functional/FEqG.fst"
  , "Functional/Fact.fst", "Functional/Fact10.fst"
  , "Functional/FixPointAlt.fst", "Functional/FixZCombinator.fst"
  , "Functional/FstSnd.fst", "Functional/FunAsArg.fst"
  , "Functional/Hungry.fst", "Functional/IOFunAsPureArg.fst"
  , "Functional/IntList.fst", "Functional/IntListElem.fst"
  , "Functional/IntListSize.fst", "Functional/IntListSum.fst"
  , "Functional/IsPrime.fst", "Functional/LambdaHO.fst"
  , "Functional/LinConsumedInBody.fst", "Functional/ListEquality.fst"
  , "Functional/ListRW.fst", "Functional/MConsumedInMNFun.fst"
  , "Functional/MainMissing.fst", "Functional/MixedBinders.fst"
  , "Functional/MultDivPrecedence.fst", "Functional/MultPrecedence.fst"
  , "Functional/MultiVarTypeSig.fst"
  , "Functional/MultipleListTransformations.fst", "Functional/MultipleOps.fst"
  , "Functional/MultipleParens.fst", "Functional/MutualRecData.fst"
  , "Functional/NTuples.fst", "Functional/OptionalAbstractions.fst"
  , "Functional/ParensPrecedence.fst", "Functional/PolySUSL.fst"
  , "Functional/PolySUTL.fst", "Functional/PolyTwoParams.fst"
  , "Functional/Processes.fst", "Functional/RecData.fst"
  , "Functional/RecFun.fst", "Functional/RecPair.fst"
  , "Functional/ReversedFunApp.fst", "Functional/Scope.fst"
  , "Functional/SemiAsSection.fst", "Functional/SemicolonPriority.fst"
  , "Functional/Shape.fst", "Functional/SimpleApp.fst"
  , "Functional/SimpleVar.fst", "Functional/SkipSkipSL.fst"
  , "Functional/TAppAssoc.fst", "Functional/Triple.fst"
  , "Functional/TypeDecl.fst", "Functional/WildcardBinders.fst"
  , "IO/CountLines.fst", "IO/EchoLines.fst", "IO/ExitChild.fst"
  , "IO/ExitMain.fst", "IO/Files.fst", "IO/GetCharUntil.fst", "IO/GetLine.fst"
  , "IO/LookupEnv.fst", "IO/MixedOutput.fst", "IO/Print.fst", "IO/PutChar.fst"
  , "IO/PutStrLn.fst", "IO/PutString.fst", "IO/StdErr.fst"
  , "IO/YourNameIs.fst", "IO/getContent.fst", "IO/reverseWords.fst"
  , "Include/BasicInclude.fst", "Include/Diamond.fst"
  , "Inference/AsPatInferUn.fst", "Inference/ClosureDupInferUn.fst"
  , "Inference/CounterInferKind.fst", "Inference/ExistentialCompose.fst"
  , "Inference/ExistsDefaultUn.fst", "Inference/ExistsLinearWitness.fst"
  , "Inference/FlipFlop.fst", "Inference/ForallCapture.fst"
  , "Inference/FunctionDemandInferKind.fst", "Inference/HigherKindedParam.fst"
  , "Inference/HigherKindedSynonym.fst", "Inference/InferredContinuation.fst"
  , "Inference/InferredDataKinds.fst", "Inference/InferredDeclKinds.fst"
  , "Inference/InferredDeclSession.fst", "Inference/InferredKinds.fst"
  , "Inference/InferredReceive.fst", "Inference/InferredUsageKinds.fst"
  , "Inference/LinClosureCapture.fst", "Inference/LinFnDefCapture.fst"
  , "Inference/ListPolyInferKind.fst", "Inference/MutualDataKinds.fst"
  , "Inference/NegativePats.fst", "Inference/ParamComponentInferUn.fst"
  , "Inference/PartialFork.fst", "Inference/PolyDataParamKind.fst"
  , "Inference/QuantifierBareVarBody.fst", "Inference/ReceiveDiscard.fst"
  , "Inference/SendTypeDefaultUn.fst", "Inference/SharedChannelSemi.fst"
  , "Inference/SystemFBooleans.fst", "Inference/TypeInPatInferKind.fst"
  , "Inference/TypeLambdaInferChannel.fst"
  , "Inference/TypeLambdaInferKind.fst"
  , "Inference/WildcardDiscardInferUn.fst", "Sections/LeftSection.fst"
  , "Sections/PolyMultSection.fst", "Sections/PolySectionCheck.fst"
  , "Sections/RightSection.fst", "SessionTypes/AnBn.fst"
  , "SessionTypes/ArithExprServer.fst"
  , "SessionTypes/ArithExprServerRegular.fst"
  , "SessionTypes/ArithExprServerRegular1.fst", "SessionTypes/BoolServer.fst"
  , "SessionTypes/BoolServer1.fst", "SessionTypes/BoolServer2.fst"
  , "SessionTypes/BoolServer3.fst", "SessionTypes/BoolServerRecursive.fst"
  , "SessionTypes/ChainOfChannelOps.fst", "SessionTypes/CloseSkipEnd.fst"
  , "SessionTypes/CondSeqMultEquiv.fst", "SessionTypes/ConjunctionCase.fst"
  , "SessionTypes/ConjunctionLambda.fst"
  , "SessionTypes/ConjunctionPattern.fst", "SessionTypes/CrissCross.fst"
  , "SessionTypes/Deadlock.fst", "SessionTypes/DualMessage.fst"
  , "SessionTypes/DupConsChan.fst", "SessionTypes/DyckWords.fst"
  , "SessionTypes/FiniteStreamEnd.fst", "SessionTypes/HelloWorldList.fst"
  , "SessionTypes/ImpredicativeSend.fst", "SessionTypes/InInPat.fst"
  , "SessionTypes/InPat.fst", "SessionTypes/InfiniteChannels.fst"
  , "SessionTypes/LazyTreeTraversal.fst", "SessionTypes/ListSend.fst"
  , "SessionTypes/Math.fst", "SessionTypes/Math1.fst"
  , "SessionTypes/NDual.fst", "SessionTypes/NDualRec.fst"
  , "SessionTypes/NTreeSend.fst", "SessionTypes/NegativePats.fst"
  , "SessionTypes/PartialFork.fst", "SessionTypes/PartialReceive.fst"
  , "SessionTypes/PartialSend.fst", "SessionTypes/PartialSendReceiveType.fst"
  , "SessionTypes/PartiallyAppliedSelect.fst"
  , "SessionTypes/PingPongDiverge.fst", "SessionTypes/Pipeline.fst"
  , "SessionTypes/PolyInstatiatedWithUnnormed.fst", "SessionTypes/RecChan.fst"
  , "SessionTypes/RegularTreeStream.fst"
  , "SessionTypes/RegularTreeStreamAlt.fst"
  , "SessionTypes/RemoteListTransform.fst", "SessionTypes/SelectUn.fst"
  , "SessionTypes/SendAndClose.fst", "SessionTypes/SendAndWait.fst"
  , "SessionTypes/SendAsSendArg.fst", "SessionTypes/SendInt.fst"
  , "SessionTypes/SendList.fst", "SessionTypes/SendListType.fst"
  , "SessionTypes/SendReceive.fst", "SessionTypes/SendReceive1.fst"
  , "SessionTypes/SendRecvSameThread.fst", "SessionTypes/SendTree.fst"
  , "SessionTypes/SendTreeHO.fst", "SessionTypes/SendTreeRegular.fst"
  , "SessionTypes/SendTreeType.fst", "SessionTypes/SessionsWithinData.fst"
  , "SessionTypes/SkipSkip.fst", "SessionTypes/Stack.fst"
  , "SessionTypes/StackRecClient.fst", "SessionTypes/Streams.fst"
  , "SessionTypes/TreeTransform.fst", "SessionTypes/TypeDefEnd.fst"
  , "SessionTypes/TypeInPat.fst", "SessionTypes/TypeNameInSig.fst"
  , "SessionTypes/TypeTeqU.fst", "SessionTypes/USend.fst"
  , "SessionTypes/UnChoicePat.fst", "SessionTypes/UnChoicePatAbbrev.fst"
  , "SessionTypes/UnInPat.fst", "SessionTypes/UnInPatAbbrev.fst"
  , "SessionTypes/UnInstanceOfLinSemi.fst", "SessionTypes/Unnormed.fst"
  , "SessionTypes/WaitPat.fst", "SharedChannels/CakeStoreFork.fst"
  , "SharedChannels/CakeStoreJoin.fst", "SharedChannels/Donation.fst"
  , "SharedChannels/FtpServer.fst", "SharedChannels/MemoryCellDestructive.fst"
  , "SharedChannels/Random.fst", "SharedChannels/Semaphore.fst"
  , "SharedChannels/SharedBag.fst", "SharedChannels/SharedBool.fst"
  , "SharedChannels/SharedMathServer.fst", "SharedChannels/SharedQueue.fst"
  , "SharedChannels/SyncChannel.fst", "SystemF/SystemFBins.fst"
  , "SystemF/SystemFBooleans.fst", "SystemF/SystemFLists.fst"
  , "SystemF/SystemFNats.fst", "SystemF/SystemFPairs.fst"
  , "SystemF/SystemFSums.fst", "SystemF/SystemFTrees.fst"
  , "SystemF/SystemFWarmUps.fst", "SystemF/TypeAbsSuspension.fst"
  , "Tutorial/AtomicalListPrint.fst", "Tutorial/Buffered.fst"
  , "Tutorial/CakeStore.fst", "Tutorial/Colour.fst", "Tutorial/Copy.fst"
  , "Tutorial/CopyFun.fst", "Tutorial/CopyFunStarredArrow.fst"
  , "Tutorial/Discard.fst", "Tutorial/DiscardFun.fst", "Tutorial/ForkJoin.fst"
  , "Tutorial/InfiniteParameters.fst", "Tutorial/IntBinTree.fst"
  , "Tutorial/IntLinType.fst", "Tutorial/LinIntData.fst"
  , "Tutorial/MainEndsLast.fst", "Tutorial/MarshallAList.fst"
  , "Tutorial/MarshallATree.fst", "Tutorial/MarshallTreeOnStream.fst"
  , "Tutorial/MultipleArgs.fst", "Tutorial/MutualRecFun.fst"
  , "Tutorial/ParallelPredEval.fst", "Tutorial/PartialAppliedLinFun.fst"
  , "Tutorial/PartialAppliedUnLinFun.fst", "Tutorial/PolyRemoteFold.fst"
  , "Tutorial/RemoteAdder.fst", "Tutorial/RenderingService.fst"
  , "Tutorial/SendClose.fst", "Tutorial/Shape.fst", "Tutorial/TokenRing.fst"
  , "Tutorial/TrafficLight.fst", "Tutorial/UntilNegative.fst"
  , "Tutorial/Void.fst" ]

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
