{- |
Annotation erasure over whole programs — the paper's own evaluation (§7), which
stripped the kind annotations from the test suite and required the programs to
still be accepted. The unit corpus can only measure this for types in isolation;
usage-driven multiplicity inference is a property of programs, so it needs the
program suite to be measured at all.

Erased are the binder kinds written inside types: the @a@ of
@forall (a : *T) -> …@ and its existential and session counterparts, wherever
they occur in a signature or a type declaration. Two are deliberately left
alone, both the same open face as in "InferredKindSpec" — a type operator's
domain and a higher-kinded quantifier binder, whose arrow kinds no body
constrains. Expression-level binders and declaration kind signatures are not
erased yet.
-}
module ErasedSpec (spec) where

import Compiler.Include (resolveIncludes)
import Compiler.Pipeline (validateModule)
import Parser.Parser (runParseModule)
import Parser.Scoping (emptyScopingCtx)
import ProgSpecUtils (specTest')
import Syntax.Declarations qualified as D
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Unkinded qualified as TU
import UI.CLI (preludePath)
import UI.Error (Error, Source, showErrors)
import Validation.Base (emptyValidationState, runValidation)
import Validation.Kinding (emptyKindCtx)
import Validation.Typing (emptyTypeCtx)

import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Paths_freest (getDataFileName)
import System.FilePath (takeFileName)
import Test.Hspec

spec :: Spec
spec = do
  prelude <- runIO (getDataFileName preludePath)
  specTest' "erased" "/test/prog/Valid/" \_ (testFile, _) -> do
    -- the property is that erasure makes no difference, so the same program
    -- unerased is the control. A program rejected either way is one the
    -- compiler does not accept yet — every such program here is one the suite
    -- already marks pending — and says nothing about erasure
    intact <- accepts prelude Nothing         testFile
    erased <- accepts prelude (Just testFile) testFile
    case (intact, erased) of
      (Right (), Left (src, errs))
        | takeFileName testFile `elem` knownGaps -> pendingWith (gapMessage errs)
        | otherwise -> expectationFailure
            ("erasing the written binder kinds made this program stop "
              ++ "typechecking:\n" ++ showErrors src errs)
      _ -> return ()

-- | Programs whose written binder kinds inference cannot yet recover. Each is a
-- kind that only a /use/ justifies — @type Maker = forall (a : 1C) -> …@ is
-- warranted by a @channel \@a@ elsewhere — the cross-boundary inference the
-- fusion work is for. Shrink this list; do not grow it.
knownGaps :: [FilePath]
knownGaps = []

gapMessage :: [Error] -> String
gapMessage errs =
  "inference does not recover this annotation (" ++ show (length errs) ++ " error(s))"

-- | 'Compiler.Pipeline.loadM' without the IO and the banners, erasing the named
-- file's module before the merge. Erasing after it would take the Prelude's
-- annotations too, which fails the Prelude once and reports that failure against
-- every program including it; and validating the program separately from the
-- Prelude is not equivalent, since 'kindModule' inherits no type declarations.
accepts :: FilePath -> Maybe FilePath -> FilePath
        -> IO (Either (Source, [Error]) ())
accepts prelude eraseIn root = resolveIncludes Map.empty [prelude, root] >>= \case
  Left _       -> pure (Right ())  -- an unreadable root is not this spec's business
  Right inputs -> pure $ first (Map.fromList inputs,) do
    modules <- mapM parseOne inputs
    runValidation emptyValidationState do
      _ <- validateModule emptyScopingCtx emptyKindCtx emptyTypeCtx
             Map.empty D.emptyDataDecls
             (M.insertBuiltinLists (mconcat modules))
      pure ()
  where
    parseOne (p, t) =
      (if Just p == eraseIn then eraseModule else id) <$> runParseModule p t

-- | Every written binder kind in the module's types removed.
eraseModule :: M.ParsedModule -> M.ParsedModule
eraseModule m = m
  { M.typeDecls   = map (fmap (fmap eraseType)) (M.typeDecls m)
  , M.definitions = map eraseDecl (M.definitions m)
  }
  where
    eraseDecl = \case
      E.TypeSig xs t -> E.TypeSig xs (eraseType t)
      d              -> d

-- | As "InferredKindSpec"'s erasure: a quantifier's proper-kinded binder goes,
-- an arrow-kinded one and a type operator's domain stay.
eraseType :: TU.ParsedType -> TU.ParsedType
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
