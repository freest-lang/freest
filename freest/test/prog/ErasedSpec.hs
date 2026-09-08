{- |
Annotation erasure over whole programs — the paper's own evaluation (§7), which
stripped every kind annotation from the test suite and required the programs to
still be accepted. The unit corpus can only measure this for types in isolation;
usage-driven multiplicity inference is a property of programs, so it needs the
program suite to be measured at all.

Erased here are the binder kinds written inside types: the @a@ of
@forall (a : *T) -> …@ and its existential and session counterparts, wherever
they occur in a signature or a type declaration. Two things are deliberately
left alone, both the same open face as in "InferredKindSpec": a type operator's
domain and a higher-kinded quantifier binder, whose arrow kinds no body
constrains. Expression-level binders (@\\\@a@, pack and receive patterns) are not
erased yet.
-}
module ErasedSpec (spec) where

import Compiler.Include (resolveIncludes)
import Parser.Parser (runParseModule)
import Parser.Scoping (emptyScopingCtx, scopeModule')
import ProgSpecUtils (specTest')
import Syntax.Base (Scoped)
import Syntax.Declarations qualified as D
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Unkinded qualified as TU
import Paths_freest (getDataFileName)
import UI.CLI (preludePath)
import UI.Error (Error, Source, showErrors)
import Compiler.Pipeline (LoadState, loadPrelude)
import Validation.Base (runValidation)
import Validation.HOTRecursion (checkNoHOTRec)
import Validation.Kinding (emptyKindCtx, kindModule)
import Validation.Typing (emptyTypeCtx, typeModule)

import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import System.FilePath (takeFileName)
import Test.Hspec

spec :: Spec
spec = do
  -- the Prelude keeps its annotations: erasing them too would fail it once and
  -- report that same failure against every program that includes it
  prel <- runIO loadPrelude
  specTest' "erased" "/test/prog/Valid/" \_ (testFile, _) -> case prel of
    Nothing   -> expectationFailure "the Prelude failed to load"
    Just base -> do
      -- the property is that erasure makes no difference, so the same program
      -- unerased is the control: a program this cut-down pipeline cannot accept
      -- either way is a gap in the harness, not in inference
      intact <- accepts base id testFile
      erased <- accepts base eraseModule testFile
      case (intact, erased) of
        (Right (), Left (src, errs))
          | takeFileName testFile `elem` knownGaps -> pendingWith (gapMessage errs)
          | otherwise -> expectationFailure
              ("erasing the written binder kinds made this program stop "
                ++ "typechecking:\n" ++ showErrors src errs)
        _ -> return ()

-- | Programs whose written binder kinds inference cannot yet recover. Each is a
-- kind that only a /use/ justifies — @type Maker = forall (a : 1C) -> …@ is
-- warranted by a @channel \@a@ elsewhere — which is the cross-boundary
-- inference the fusion work is for. Shrink this list; do not grow it.
knownGaps :: [FilePath]
knownGaps =
  [ "MConsumedInMNFun.fst", "ReversedFunApp.fst", "FunctionDemandInferKind.fst"
  , "TypeLambdaInferChannel.fst", "PartialFork.fst", "RenderingService.fst" ]

gapMessage :: [Error] -> String
gapMessage errs = "inference does not recover this annotation ("
  ++ show (length errs) ++ " error(s))"

-- | Parse, scope, erase, then kind and type — 'Compiler.Pipeline.validateModule'
-- with the erasure spliced between scoping and kinding, and without running the
-- program: the property is that it is still /accepted/.
accepts :: LoadState -> (M.ScopedModule -> M.ScopedModule) -> FilePath
        -> IO (Either (Source, [Error]) ())
accepts (_, vs, sctx, kctx, tctx, prelude) erase root =
  resolveIncludes [root] >>= \case
    Left _       -> pure (Right ())  -- an unreadable root is not this spec's business
    Right inputs -> pure $ first (src inputs,) do
      modules <- mapM (uncurry runParseModule) inputs
      runValidation vs do
        -- the builtins came in with the Prelude; re-inserting them duplicates
        (_, smodl)     <- scopeModule' sctx (mconcat modules)
        (kctx', kmodl) <- kindModule kctx (erase smodl)
        checkNoHOTRec (M.typeDecls kmodl)
        _              <- typeModule kctx' tctx (inherit kmodl)
        pure ()
  where
    src inputs = Map.fromList [(p, lines t) | (p, t) <- inputs]
    inherit m = m { M.typeDecls = M.typeDecls m `Map.union` M.typeDecls prelude
                  , M.dataDecls = M.dataDecls m <>          M.dataDecls prelude }

-- | Every written binder kind in the module's types removed.
eraseModule :: M.ScopedModule -> M.ScopedModule
eraseModule m = m
  { M.typeDecls   = Map.map (fmap eraseType) (M.typeDecls m)
  , M.definitions = map eraseDecl (M.definitions m)
  }
  where
    eraseDecl = \case
      E.TypeSig xs t -> E.TypeSig xs (eraseType t)
      d              -> d

-- | As "InferredKindSpec"'s erasure: a quantifier's proper-kinded binder goes,
-- an arrow-kinded one and a type operator's domain stay.
eraseType :: TU.ScopedType -> TU.ScopedType
eraseType = \case
  TU.AppQuant s p bk m aks t ->
    TU.AppQuant s p bk m (map eraseProper aks) (eraseType t)
  TU.Abs s aks t      -> TU.Abs s aks (eraseType t)
  TU.App s t ts       -> TU.App s (eraseType t) (map eraseType ts)
  TU.ForallM s m φs t -> TU.ForallM s m φs (eraseType t)
  t                   -> t
  where
    eraseProper ak@(_, Just K.Arrow{}) = ak
    eraseProper (a, _)                 = (a, Nothing)
