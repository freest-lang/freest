{- |
Module      :  UI.Error
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Errors. A work in progress -- Life is a work in progress
-}

module UI.Error
  ( Error(..)
  , Source
  , toMessage
  , header
  , snippet
  , showErrors -- for testing
  , printErrors
  )
where

import Parser.Token
import Parser.Unparser
import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Provenance ( Origin(..) )
import Syntax.Type.Kinded qualified as TK
import Syntax.Type.Unkinded qualified as TU
import Compiler.Bug ( internalError )

import Data.List ( intercalate, nub )
import Data.Map.Strict qualified as Map
import Data.List qualified as List
import Data.Char qualified as Char
import Debug.Trace ( traceM )
import System.IO ( stderr, hPutStrLn )

-- | The errors that can be found in a FreeST program.
data Error
  = ArrowMultMismatch
      Span
      (Either Variable E.KindedExp)
      Int
      K.Multiplicity Origin
      K.Multiplicity Origin
  | CannotInferHigherKindedTypeApp Span K.Kind
  | CannotSatisfyKindConstraint Origin K.Kind K.Kind
  | CannotSatisfyBaseKindConstraint Origin K.BaseKind K.BaseKind
  | InfiniteKind Origin Variable K.Kind
  | CannotSatisfyMultConstraint Span K.Multiplicity Origin K.Multiplicity Origin
  | CannotSynthesisePack Span E.KindedExp
  | CannotSynthesisePat Span E.KindedPat
  | CannotSynthesiseReceiveType Span
  | CannotSynthesiseSelect Span Identifier
  | CannotSynthesiseSendType Span
  | CannotSynthesiseSection Span (Either Variable Identifier)
  | ConflictingDefs Span (Level String String String) [Span]
  | ConsOutOfScope Span Identifier
  | DConsPatArgMismatch Span Identifier Int Int
  | EquationArityMismatch Span Variable Int Int
  | ExpectsTooManyArgs Span TK.KindedType Int Int
  | ExpectsTooManyArgsK Span Identifier K.Kind
  | ExposeError Span (Either E.KindedPat E.KindedExp) String TK.KindedType
  | GivenTooManyArgs Span TK.KindedType Int Int
  | GivenTooManyArgsK Span TK.KindedType K.Kind Int Int
  | IllegalChoice Span Identifier TK.KindedType
  | KindMismatch Span K.Kind TK.KindedType
  | KindMismatchK Span K.Kind K.Kind TU.ScopedType
  | KSigLacksBinding Span Identifier
  | LacksTypeSig Span Variable
  | LexicalError Span Char
  | IncludeCycle Span [FilePath]
  | IncludeNotFound Span FilePath
  | MalformedInclude Span
  | LinConsumedInGuard 
      Span 
      (Either Variable Identifier) 
      TK.KindedType
  | LinConsumedInUnFun 
      Span 
      (Either Variable Identifier) 
      TK.KindedType 
      Span 
      K.Multiplicity
  | LinNotConsumedEvenly Span (Either Variable Identifier) TK.KindedType
    (Either (Either Variable E.KindedPat) E.KindedExp)
  | LinVarAtEndOfScope Span (Either Variable Identifier) TK.KindedType
  | MultipleConsDecls Span [Identifier]
  | MultipleFieldDecls Span [Identifier]
  | MultipleKindSigs Span [Identifier]
  | MultipleTypeDecls Span [Identifier]
  | MultipleVarDecls Span [Variable]
  | MultVarOutOfScope Span Variable
  | NonLinPat Span E.KindedPat TK.KindedType
  | ParseError Span (Token, [String])
  | PartiallyAppliedSelect Span Identifier
  | BaseKindMismatch Span K.BaseKind TK.KindedType K.Kind
  | ProperKindMismatch Span TK.KindedType K.Kind
  | RestrictedFunInMutual Span Variable TK.KindedType
  | SigLacksDef Span Variable
  | TypeConsOutOfScope Span Identifier
  | TypeMismatch Span TK.KindedType TK.KindedType (Either E.KindedExp E.KindedPat)
  | TypeMismatchList Span TK.KindedType (Either E.KindedExp E.KindedPat)
  | TypeMismatchChoice Span TK.KindedType Identifier E.KindedPat
  | TypeMismatchExists Span TK.KindedType (Either E.KindedPat E.KindedExp) -- TODO: should be (Either E.KindedPat E.Exp) everywhere. Mnemonic: pats occur on LHSs, exps on RHSs
  | TypeMismatchReceiveType Span TK.KindedType
  | TypeMismatchSelect Span TK.KindedType Identifier E.KindedExp
  | TypeMismatchSendType Span TK.KindedType
  | TypeMismatchTuple Span Int TK.KindedType (Either E.KindedExp E.KindedPat)
  | TypeVarOutOfScope Span Variable
  | UnexpectedArg 
      Span
      Int
      (Level (Maybe TK.KindedType) K.Kind ())
      (Level E.KindedExp TK.KindedType K.Multiplicity)
  | UnexpectedParam Span Int (Level TK.KindedType K.Kind ()) (Level () () ())
  | UnsupportedError Span String String
  | VarOutOfScope Span Variable
  | PolymorphicTypeRecursion
      Span
      Identifier
      [Variable]
      (Either K.Kind TK.KindedType)
  | HigherOrderTypeRHS Span Identifier
  | MixedSessionVarPats Span E.KindedPat E.KindedPat
  | UnexpectedEOF Span
    -- ^ Alex ran past the end of the file with no more input to inspect —
    -- typically an unterminated string literal or block comment.

-- | Errors can be tracked to the source code.
instance Located Error where
  -- | Returns the span of an 'Error', i.e., where the error occurs in the
  -- source code.
  getSpan = \case
    ArrowMultMismatch s _ _ _ _ _ _ -> s
    CannotInferHigherKindedTypeApp s _ -> s
    CannotSatisfyKindConstraint o _ _ -> getSpan o
    CannotSatisfyBaseKindConstraint o _ _ -> getSpan o
    InfiniteKind o _ _ -> getSpan o
    CannotSatisfyMultConstraint s _ _ _ _ -> s
    CannotSynthesisePack s _ -> s
    CannotSynthesisePat s _ -> s
    CannotSynthesiseReceiveType s -> s
    CannotSynthesiseSelect s _ -> s
    CannotSynthesiseSendType s -> s
    CannotSynthesiseSection s _ -> s
    ConflictingDefs s _ _ -> s
    ConsOutOfScope s _ -> s
    DConsPatArgMismatch s _ _ _ -> s
    EquationArityMismatch s _ _ _ -> s
    ExpectsTooManyArgs s _ _ _ -> s
    ExpectsTooManyArgsK s _ _ -> s
    ExposeError s _ _ _ -> s
    GivenTooManyArgs s _ _ _ -> s
    GivenTooManyArgsK s _ _ _ _ -> s
    IllegalChoice s _ _ -> s
    KindMismatch s _ _ -> s
    KindMismatchK s _ _ _ -> s
    KSigLacksBinding s _ -> s
    LacksTypeSig s _ -> s
    LexicalError s _ -> s
    IncludeCycle s _ -> s
    IncludeNotFound s _ -> s
    MalformedInclude s -> s
    LinNotConsumedEvenly s _ _ _ -> s
    LinVarAtEndOfScope s _ _ -> s
    LinConsumedInGuard s _ _ -> s
    LinConsumedInUnFun s _ _ _ _ -> s
    MultipleConsDecls s _ -> s
    MultipleFieldDecls s _ -> s
    MultipleKindSigs s _ -> s
    MultipleTypeDecls s _ -> s
    MultipleVarDecls s _ ->  s
    MultVarOutOfScope s _ -> s
    NonLinPat s _ _ -> s
    ParseError s _ -> s
    BaseKindMismatch s _ _ _ -> s
    ProperKindMismatch s _ _ -> s
    RestrictedFunInMutual s _ _ -> s
    SigLacksDef s _ -> s
    TypeConsOutOfScope s _ -> s
    TypeMismatch s _ _ _ -> s
    TypeMismatchExists s _ _ -> s
    TypeMismatchList s _ _ -> s
    TypeMismatchChoice s _ _ _ -> s
    TypeMismatchReceiveType s _ -> s
    TypeMismatchSelect s _ _ _ -> s
    TypeMismatchSendType s _ -> s
    TypeMismatchTuple s _ _ _ -> s
    TypeVarOutOfScope s _ -> s
    UnexpectedArg s _ _ _ -> s
    UnexpectedParam s _ _ _ -> s
    UnsupportedError s _ _ -> s
    VarOutOfScope s _ -> s
    PolymorphicTypeRecursion s _ _ _ -> s
    HigherOrderTypeRHS s _ -> s
    MixedSessionVarPats s _ _ -> s
    UnexpectedEOF s -> s

  -- There should be no need to relocate an error. (At least for now...)
  setSpan = internalError "span not settable for Error type."

-- | The source code of a FreeST program, represented as a mapping from file paths
-- to the lines of code in those files. This is used to extract snippets of code
-- to display in error messages.
-- The list of lines of code may be empty, when parsing from an interactive prompt.
type Source = Map.Map FilePath [String]

getFromSpan :: Located a => Source -> a -> String
getFromSpan src (getSpan -> (Span fp (sl, sc) (_, ec))) =
  take (ec - sc) . drop (sc - 1) $ lookupSrc src fp !! (sl - 1)

getLineFromSpan :: Located a => Source -> a -> String
getLineFromSpan src (getSpan -> Span fp (sl, _) (_, _)) =
  lookupSrc src fp !! (sl - 1)

-- | The source lines of a file, or @[]@ if it is not in the map (e.g. a
-- synthetic or inferred span), so error rendering degrades instead of crashing.
lookupSrc :: Source -> FilePath -> [String]
lookupSrc src fp = Map.findWithDefault [] fp src

-- | Collapse the standard-library install path to a stable, readable suffix,
-- e.g. ".../share/.../StandardLib/Prelude.fst" becomes "StandardLib/Prelude.fst".
prettyPath :: FilePath -> FilePath
prettyPath fp =
  case [ rest | t <- List.tails fp, Just rest <- [List.stripPrefix "StandardLib/" t] ] of
    (rest : _) -> "StandardLib/" ++ rest
    []         -> fp

-- | A span rendered like 'show', but with 'prettyPath' applied to its file.
prettySpan :: Span -> String
prettySpan s = prettyPath (filepath s) ++ drop (length (filepath s)) (show s)

snippet :: Located a => Source -> a -> Bool -> String
snippet src (getSpan -> s@(Span fp (sl, sc) (el, ec))) showSpan =
  unlines ([ spaces (n + 1) ++ prettySpan s | showSpan ] ++
           [ spaces n ++ sep
           , rpad n ' ' (show sl) ++ sep ++ l
           , spaces n ++ sep ++ spaces (sc - 1)
             ++ if sl == el then carets (ec - sc)
                else carets (length (strip (drop (sc - 1) l))) ++ "..."
           ])
  where
    sep = " | "
    n = length (show el)
    srcf = lookupSrc src fp
    l | null srcf = []
      | otherwise = srcf !! (min (length srcf) sl - 1)
    spaces x = replicate x ' '
    carets x = replicate x '^'

multiLineSnippet :: Located a => Source -> a -> String
multiLineSnippet src (getSpan -> Span fp (sl, sc) (el, ec)) =
  unlines $ (spaces n ++ sep) : zipWith lineCarets [sl..] ls
  where
    n = length (show el)
    sep = " | "
    ls  = take (el - (sl - 1)) $ drop (sl - 1) $ lookupSrc src fp
    spaces x = replicate x ' '
    lineCarets i li =
      rpad n ' ' (show i) ++ sep ++ li ++ "\n" ++ spaces n ++ sep
      ++ if | sl == el  -> spaces (sc - 1) ++ carets (ec - sc)
            | i  == sl  -> spaces (sc - 1) ++ caretsFrom (strip (drop (sc - 1) li))
            | i  == el  -> ws ++ carets (ec - 1 - length ws)
            | otherwise -> ws ++ caretsFrom (strip li')
      where
        carets x = replicate x '^'
        caretsFrom = map (const '^')
        (ws, li') = List.span Char.isSpace li

header :: Located a => String -> a -> String
header sort (getSpan -> s) = prettySpan s ++ ": " ++ sort ++ ":"

errorHeader :: Located a => a -> String
errorHeader = header "error"

makeError :: Located a => Source -> a -> String -> String
makeError src (getSpan -> s) msg =
  errorHeader s ++ "\n" ++ msg ++ "\n" ++ snippet src s False

-- | Does a type still mention a solvable (unification) type variable? Such a
-- variable is one the checker never resolved — it unparses to @_@. In a type
-- mismatch it signals that a type argument could not be inferred, a limitation
-- of type inference that an explicit type argument works around. All the session
-- constructors are 'App' synonyms, so the traversal only needs the three
-- underlying shapes.
hasSolvableTypeVar :: TK.KindedType -> Bool
hasSolvableTypeVar = \case
  TK.Var _ _ lv _ -> solvable lv
  TK.Abs _ _ t    -> hasSolvableTypeVar t
  TK.App _ t ts   -> hasSolvableTypeVar t || any hasSolvableTypeVar ts
  _               -> False

-- | Does a type contain a universal quantifier (a @forall@)? When one side of a
-- mismatch has one and the other does not, the likely cause is a polymorphic
-- value (e.g. @Nothing : forall a. Maybe a@) whose leading quantifier was never
-- instantiated — another limitation of type inference, fixed by an explicit type
-- argument or annotation on that value.
hasForall :: TK.KindedType -> Bool
hasForall = \case
  TK.AppForall _ _ _ _ -> True
  TK.ForallM _ _ _ _   -> True
  TK.Abs _ _ t         -> hasForall t
  TK.App _ t ts        -> hasForall t || any hasForall ts
  _                    -> False

toMessage :: Source -> Error -> String
toMessage src = \case
  ArrowMultMismatch s xe i m om m' om' -> makeError src s
    ("Multiplicity mismatch:" ++ onParam)
    ++ "expected " ++ multSide src m om
    ++ "but got " ++ multSide src m' om'
    where
      onParam
        | i > 0 = " (on the " ++ ordinal (i + 1) ++ " parameter of this "
                  ++ (case xe of Left _  -> "function definition" -- should not occur
                                 Right _ -> "expression") ++ ")"
        | otherwise = ""
  CannotInferHigherKindedTypeApp s k -> makeError src s
    "Cannot infer a higher-kinded type argument"
    ++ "The type parameter has kind " ++ bt (tidyK k) ++ ", declared at"
    ++ locateSpan src (getSpan k)
    ++ "Higher-kinded type arguments are not inferred; please provide them explicitly"
  CannotSatisfyKindConstraint o k1 k2 -> makeError src (getSpan o)
    ("Couldn't match kind " ++ bt a ++ " with kind " ++ bt b)
    where (a, b) = tidyKK k1 k2
  CannotSatisfyBaseKindConstraint o p1 p2 -> makeError src (getSpan o)
    ("Expected a " ++ prettyBk p2 ++ ", but got a " ++ prettyBk p1)
  InfiniteKind o v k -> makeError src (getSpan o)
    ("Cannot construct the infinite kind " ++ bt (va ++ " ~ " ++ vk))
    where e  = mkTidy (('k', v) : kMetas k)
          va = tidyName e v
          vk = tidyKind e k
  CannotSatisfyMultConstraint s m1 o1 m2 o2 -> makeError src s
    "Could not infer consistent multiplicities for this application"
    ++ "Could not match multiplicity " ++ multSide src m1 o1
    ++ "with multiplicity " ++ multSide src m2 o2
  CannotSynthesisePack s e -> makeError src s
    "Could not infer a type for this package expression"
  CannotSynthesisePat s p -> makeError src s
    ("Could not infer a type for pattern " ++ bt (show p))
    ++ "Consider giving it a type annotation: " ++ bt ("(" ++ show p ++ " : T)")
  CannotSynthesiseReceiveType s -> makeError src s
    "Could not infer a type for this `receiveType` expression"
  CannotSynthesiseSelect s id -> makeError src s
    "Could not infer a type for this `select` expression"
  CannotSynthesiseSendType s -> makeError src s
    "Could not infer a type for this `sendType` expression"
  CannotSynthesiseSection s op -> makeError src s
    ("Could not infer a type for this section over " ++ bt (either show show op))
    ++ "Its operator is polymorphic, so the omitted operand's type is ambiguous here.\n"
    ++ "Consider giving the section a type annotation."
  ConflictingDefs s xa ss -> makeError src s
    ("Conflicting definitions for " ++ case xa of
      ExpLevel x -> "variable " ++ bt x
      TypeLevel a -> "type variable " ++ bt a
      MultLevel φ -> "multiplicity variable " ++ bt φ)
    ++ "Conflicting definitions at:\n" ++ unlines (map show ss)
  ConsOutOfScope s i -> makeError src s
    ("Constructor out of scope: " ++ bt (show i))
  DConsPatArgMismatch s i n m -> makeError src s
    ("Constructor " ++ bt (show i) ++ " takes " ++ show n
      ++ " arguments, but it is given " ++ show m)
  EquationArityMismatch s f n m -> makeError src s
    ("Equations for " ++ bt (external f) ++ " have different numbers of value parameters:"
      ++ " this equation binds " ++ show m ++ ", but an earlier one binds " ++ show n)
  ExpectsTooManyArgs s t n m -> makeError src s
     ("This function expects " ++ prettyArgs n
       ++ ", but its type " ++ bt (unparse t) ++ " takes"
       ++ case m of
        0 -> " none"
        n -> " only " ++ show n)
  ExpectsTooManyArgsK s i k -> makeError src s
    ("Type " ++ bt (show i) ++ " expects too many arguments, its kind "
      ++ bt (tidyK k) ++ " takes only " ++ show (K.depth k))
  ExposeError s pe msg t -> makeError src s
    case pe of
      Left _  -> "Cannot match this pattern against the expected type " ++ bt (unparse t)
      Right _ -> "Expected " ++ msg ++ ", but got an expression of type " ++ bt (unparse t)
    ++ case pe of Left _ -> "(It matches " ++ msg ++ ")"; Right{} -> ""
  GivenTooManyArgs s t n m -> makeError src s
    ("Got " ++ prettyModifiedArgs "unexpected" (m - n))
    ++ "(This expression cannot be applied to further arguments: it has type " ++ bt (unparse t)
    ++ ", which is not a function type)"
  GivenTooManyArgsK s t k n m -> makeError src s
    ("Got " ++ prettyModifiedArgs "unexpected" (m - n))
    ++ "(A type of kind " ++ bt (tidyK k) ++ " cannot be applied to further arguments)"
  IllegalChoice s i t -> makeError src (getSpan i)
    ("Choice " ++ bt (show i) ++ " is not offered by type " ++ bt (unparse t))
  KindMismatch s k1 t -> makeError src s
    -- TODO: this would give us weird errors, like "Expected 1 less argument to
    -- type `Int`" with `type T : *T -> *T` and `type T = Int`
    -- if | K.depth k1 < K.depth k2 ->
    --      ("Expected " ++ prettyMoreArgs diff ++ " to type " ++ bt (unparse t))
    --    | K.depth k1 > K.depth k2 ->
    --      ("Expected " ++ prettyLessArgs (- diff) ++ " to type " ++ bt (unparse t))
    --    | otherwise ->
      (let (a, b) = tidyKK k1 (TK.kindOf t)
       in "Kind " ++ bt b ++ " is not a subkind of the expected kind " ++ bt a)
    ++ kindMismatchHint (unparse t) (TK.kindOf t) k1
    -- where
    --   diff = (K.depth k2 - K.depth k1)
  KindMismatchK s k1 k2 t -> makeError src s
      (let (a, b) = tidyKK k1 k2
       in "Kind " ++ bt b ++ " is not a subkind of the expected kind " ++ bt a)
    ++ kindMismatchHint (unparse t) k2 k1
    -- where
    --   diff = (K.depth k2 - K.depth k1)
  KSigLacksBinding s i -> makeError src s
    ("The kind signature for type " ++ bt (show i)
      ++ " lacks an accompanying binding")
  LacksTypeSig s x -> makeError src s
    ("Function " ++ bt (external x) ++ " is missing a type signature")
  LexicalError span c -> makeError src span
    ("Unsupported character " ++ bt [c])
  UnexpectedEOF s -> makeError src s
    "Unexpected end of input (an unterminated string literal or comment?)"
  IncludeCycle s files -> makeError src s
    ("Include cycle: " ++ intercalate " -> " files)
  IncludeNotFound s path -> makeError src s
    ("Cannot find included file \"" ++ path ++ "\"")
  MalformedInclude s -> makeError src s
    "Malformed INCLUDE pragma, expected {-# INCLUDE \"path\" #-}"
  LinVarAtEndOfScope s xi t ->
    makeError src s
      ("Linear " ++ prettyVarCons xi ++ " of type " ++ bt (unparse t) ++ " is not consumed")
    ++ case sessionHint t of
         Just op -> "  hint: consume it with " ++ bt op ++ "\n"
         Nothing -> ""
  LinConsumedInGuard s xi t -> errorHeader s ++ "\n"
      ++ ((case m' of
        K.Lin{} -> "Linear " ++ prettyVarCons xi ++ " of "
        _ -> "Potentially linear " ++ prettyVarCons xi ++ " with multiplicity " ++ bt (tidyM m') ++ " and ")
      ++ "type " ++ bt (unparse t) ++ ", bound at\n"
      ++ snippet src xi True
      ++ " cannot be consumed inside a guard")
    where
      m' = case TK.kindOf t of
        K.Proper _ m _ -> m
        _ -> internalError "non-proper type for expression variable"
  LinConsumedInUnFun s xi t fe m -> errorHeader s ++ "\n" 
      ++ ((case m' of 
        K.Lin{} -> "Linear " ++ prettyVarCons xi ++ " of "
        _ -> "Potentially linear " ++ prettyVarCons xi ++ " with multiplicity " ++ bt (tidyM m') ++ " and ")
      ++ "type " ++ bt (unparse t) ++ ", bound at\n"
      ++ snippet src xi True
      ++ " is consumed in body of "
      ++ (case m of 
        K.Un{} -> "an unrestricted function"
        _      -> "a function with multiplicity " ++ bt (tidyM m))
      ++ "\n" ++ snippet src fe True)
    ++ "(This would allow duplicating or discarding the value. "
    ++ "Consider using a linear function instead.)"
    where 
      m' = case TK.kindOf t of
        K.Proper _ m _ -> m
        _ -> internalError "non-proper type for expression variable"
  MultipleConsDecls s is -> makeError src s
    ("Multiple declarations of constructor " ++ bt (show (head is)))
    ++ "Duplicate declarations at:\n"
    ++ unlines (map (("  " ++) . show . getSpan) is)
  MultipleFieldDecls s is -> makeError src s
    ("Multiple declarations of field " ++ bt (show (head is)))
    ++ "Duplicate declarations at:\n"
    ++ unlines (map (("  " ++) . show . getSpan) is)
  MultipleKindSigs s is -> makeError src s
    ("Multiple kind signatures for type " ++ bt (show (head is)))
    ++ "Duplicate signatures at:\n"
    ++ unlines (map (("  " ++) . show . getSpan) is)
  MultipleTypeDecls s is -> makeError src s
    ("Multiple declarations of type " ++ bt (show (head is)))
    ++ "Duplicate declarations at:\n"
    ++ unlines (map (("  " ++) . show . getSpan) is)
  MultipleVarDecls s xs -> makeError src s
    ("Multiple declarations of variable " ++ bt (external (head xs)))
    ++ "Duplicate declarations at:\n"
    ++ unlines (map (("  " ++) . show . getSpan) xs)
  MultVarOutOfScope s φ -> makeError src s
    ("Multiplicity variable out of scope: " ++ external φ)
  NonLinPat s p t -> makeError src s
    ("Non-linear pattern for" ++ case TK.kindOf t of
      K.Proper _ K.Lin{} _ -> " linear type " ++ bt (unparse t)
      K.Proper _ m _       -> " potentially linear type " ++ bt (unparse t) ++ " with multiplicity " ++ bt (tidyM m)
      _ -> internalError "pattern with non-proper type")
  ParseError s (_, ss) -> makeError src s
    "Parse error"
    ++ case ss of
      [] -> ""
      [x] -> "(Expected " ++ x ++ ")"
      ss  -> "(Expected one of: " ++ intercalate ", " ss ++ ")"
  BaseKindMismatch s bk t k -> makeError src s
    ("Expected a " ++ prettyBk bk ++ ", but got " ++
      (case k of
        K.Proper _ m bk -> prettyBk bk ++ " " ++ bt (unparse t)
        k               -> bt (unparse t) ++ " of kind " ++ bt (tidyK k))
      ++ " instead")
  ProperKindMismatch s t k -> case k of
    -- an unsolved kind variable: inference could not determine a proper kind here
    K.Var{} -> makeError src s
      ("Could not infer a proper kind for " ++ bt (unparse t)
       ++ "; consider annotating it")
    _ -> makeError src s
      ("Expected " ++ prettyMoreArgs (K.depth k) ++ " to " ++ bt (unparse t))
      ++ "(Expected a proper type, but got " ++ bt (unparse t)
      ++ " of kind " ++ bt (tidyK k) ++ ")"
  RestrictedFunInMutual s x t -> makeError src s
    ("Mutually recursive function " ++ bt (external x)
      ++ " must be unrestricted, but has type " ++ bt (unparse t))
  SigLacksDef s x -> makeError src s
    ("Variable " ++  external x ++ " has a type signature but no definition")
  TypeConsOutOfScope s i -> makeError src s
    ("Type constructor out of scope: " ++ bt (show i))
  LinNotConsumedEvenly s xi t fpe -> errorHeader s ++ "\n" ++
    ("Linear " ++ (case xi of Left x  -> "variable " ++ bt (external x)
                              Right i -> "constructor " ++ bt (show i))
      ++ " of type " ++ bt (unparse t) ++", bound at\n"
      ++ snippet src xi True
      ++ "is not consumed evenly among the branches of a"
      ++ (case fpe of
        Left (Left  x) -> " function definition"
        Left (Right p) -> " value definition"
        Right e        -> case e of
          E.Case{} -> " case expression"
          E.If{}   -> " conditional expression"
          _        -> "n expression") ++ "\n"
      ++ snippet src fpe True)
  TypeMismatch s t u _ -> makeError src s "Type mismatch:"
    ++ "Couldn't match expected type " ++ bt (unparse t) ++ fromClause s src t
    ++ "with actual type " ++ bt (unparse u) ++ fromClause s src u
    ++ inferenceHint
    where
    -- Only when a type argument was left unresolved (it shows as `_`): the
    -- mismatch may stem from a limitation of type inference, and an explicit
    -- type argument is the fix. Stays silent on ordinary mismatches.
    inferenceHint
      | hasSolvableTypeVar t || hasSolvableTypeVar u =
          "Type inference could not determine a type argument here "
          ++ "(shown as `_`).\nConsider annotating the application with an explicit "
          ++ "type argument (e.g. `f @a`),\nbinding the signature's type variables with "
          ++ "`@a` patterns on the left-hand side."
      | hasForall t /= hasForall u =
          "A polymorphic value was not instantiated here "
          ++ "(note the `forall`).\nConsider giving it an explicit type argument "
          ++ "(e.g. `Nothing @a`) or a type annotation."
      | otherwise = ""
    fromClause primary src ty
      | sp == primary                      = "\n"
      | not (Map.member (filepath sp) src) = "\n"
      | otherwise                          = ", taken from:\n" ++ snippet src sp True
      where sp = getSpan ty
  TypeMismatchExists s t poe -> makeError src s
    ("Couldn't match expected type " ++ bt (show t) ++ " with a package "
      ++ case poe of Left  p -> "pattern"
                     Right e -> "expression")
  TypeMismatchList s t _ -> makeError src s
    ("Couldn't match expected type " ++ bt (unparse t)
      ++ " with a list pattern")
  TypeMismatchChoice s t i p -> makeError src s
    ("Couldn't match expected type " ++ bt (unparse t)
      ++ " with choice pattern " ++ bt (getFromSpan src i))
  TypeMismatchReceiveType s t -> makeError src s
    ("Couldn't match expected type " ++ bt (unparse t)
      ++ " with a `receiveType` expression")
  TypeMismatchSelect s t i _ -> makeError src s
    ("Couldn't match expected type " ++ bt (unparse t)
      ++ " with a `select` expression")
  TypeMismatchSendType s t -> makeError src s
    ("Couldn't match expected type " ++ bt (unparse t)
      ++ " with a `sendType` expression")
  TypeMismatchTuple s n t _ -> makeError src s
    ("Couldn't match expected type " ++ bt (unparse t) ++ " with "
      ++ (case n of 0 -> "()"
                    2 -> "a pair pattern"
                    m -> "a " ++ show m ++ "-tuple pattern"))
  TypeVarOutOfScope s a -> makeError src s
    ("Type variable out of scope: " ++ external a)
  UnexpectedArg s n arg1 arg2 -> makeError src s -- TODO: use n to write the ordinal of the argument?
    ("Expected " ++ expected ++ ", but got " ++ got)
    where
      expected = case arg1 of
        ExpLevel mt -> "a value argument" ++ maybe "" ((" of type "++) . bt . unparse) mt
        TypeLevel k -> "a type argument of kind " ++ bt (unparse k)
        MultLevel _ -> "a multiplicity argument"
      got = case arg2 of
        ExpLevel _ -> "a value argument"
        TypeLevel _ -> "a type argument"
        MultLevel _ -> "a multiplicity argument"
  UnexpectedParam s n p1 p2 -> makeError src s -- TODO: use n to write the ordinal of the parameter?
    ("Expected " ++ expected ++ ", but got " ++ got)
    where
      expected = case p1 of
        ExpLevel t -> "a pattern of type " ++ bt (unparse t)
        TypeLevel k -> "a type parameter of kind " ++ bt (unparse k)
        MultLevel _ -> "a multiplicity parameter"
      got = case p2 of
        ExpLevel _ -> "a pattern"
        TypeLevel _ -> "a type parameter"
        MultLevel _ -> "a multiplicity parameter"
  UnsupportedError s msg1 msg2 -> makeError src s
    ("Unsupported feature: " ++ msg1)
    ++ msg2
  VarOutOfScope s x -> makeError src s
    ("Variable out of scope: " ++ bt (external x))
  PolymorphicTypeRecursion s i as ekt -> makeError src s
    ("Higher-order recursion detected in the declaration for type " ++ bt (show i))
    ++ case ekt of 
      Left k ->
        "(Expected a proper type on the right-hand side, but found a type of kind "
        ++ bt (unparse k) ++ ". Consider adding " ++ prettyMoreParams (K.depth k)
        ++ " to the equation.)"
      Right t ->
        "(Found a self-reference different from the left-hand side "
        ++ bt (show i ++ (if null as then "" else " ") ++ unwords (map external as))
        ++ ", namely " ++ bt (unparse t) ++ ")"
  MixedSessionVarPats s sp vp -> errorHeader s ++ "\n"
    ++ "Cannot mix session patterns with variable patterns\n"
    ++ "  session pattern:\n"
    ++ snippet src sp True
    ++ "  variable pattern:\n"
    ++ snippet src vp True
    ++ "(Session and variable patterns cannot appear together in the same match)"
  where
  -- Tidying (GHC-style cosmetics). Kind inference leaves solvable metavariables
  -- in a type's kind precisely when it cannot pin one down; those must never
  -- reach the user as raw internal names. Following GHC's tidying, we rewrite
  -- each solvable metavariable to a short, generated name — @k0@/@m0@/@p0@ by
  -- sort (the leading letter), numbered in first-seen order and shared within a
  -- message — and leave every ground kind and rigid (object-level: @#m@,
  -- ∀-bound) variable exactly as the unparser prints it.

  -- The solvable metavariables of a kind/multiplicity/baseKind, tagged with the
  -- letter of their sort, in first-seen (left-to-right) order.
  kMetas = \case
    K.Proper _ m bk -> mMetas m ++ bkMetas bk
    K.Arrow _ a b   -> kMetas a ++ kMetas b
    K.Var _ lv v    -> [('k', v) | solvable lv]
  mMetas = \case K.Sup _ as -> [('m', v) | (lv, v) <- as, solvable lv]; _ -> []
  bkMetas = \case K.VarBK lv v | solvable lv -> [('p', v)]; _ -> []

  -- Assign each distinct metavariable a name, in first-seen order, per sort.
  mkTidy = go Map.empty Map.empty
    where
      go env _   []             = env
      go env cnt ((c, v) : rest)
        | Map.member (internal v) env = go env cnt rest
        | otherwise = go (Map.insert (internal v) (c : show n) env)
                         (Map.insert c (n + 1) cnt) rest
        where n = Map.findWithDefault (0 :: Int) c cnt

  tidyName env v = Map.findWithDefault "_" (internal v) env

  -- The renderers mirror the 'Parser.Unparser' kind instances exactly on ground
  -- and rigid input, diverging only to print a metavariable's tidy name.
  tidyKind env = \case
    K.Proper _ m bk -> tidyMultB env m ++ tidyBaseKind env bk
    K.Arrow _ a b   -> dom ++ " -> " ++ tidyKind env b
      where dom = case a of K.Arrow{} -> "(" ++ tidyKind env a ++ ")"
                            _         -> tidyKind env a
    K.Var _ lv v | solvable lv -> tidyName env v
                 | otherwise   -> show v

  tidyMult env = \case
    K.Lin _    -> "1"
    K.Un _     -> "*"
    K.Sup _ as -> intercalate " + " (map atom as)
      where atom (lv, v) | solvable lv = tidyName env v
                         | otherwise   = show v

  -- As 'tidyMult', but bracketing a multi-atom join before a baseKind, as the
  -- unparser does inside a proper kind.
  tidyMultB env = \case
    m@(K.Sup _ as) | length as > 1 -> "(" ++ tidyMult env m ++ ")"
    m                              -> tidyMult env m

  tidyBaseKind env = \case
    K.Top -> "T"; K.Session -> "S"; K.Channel -> "C"
    K.VarBK lv v | solvable lv -> tidyName env v
                 | otherwise   -> external v

  -- Tidy a single kind/multiplicity/baseKind, or a pair sharing one environment
  -- (so a metavariable common to both sides of a mismatch prints one name).
  tidyK  k      = tidyKind (mkTidy (kMetas k)) k
  tidyKK k1 k2  = let e = mkTidy (kMetas k1 ++ kMetas k2)
                  in (tidyKind e k1, tidyKind e k2)
  tidyM  m      = tidyMult (mkTidy (mMetas m)) m
  tidyMM m1 m2  = let e = mkTidy (mMetas m1 ++ mMetas m2)
                  in (tidyMult e m1, tidyMult e m2)
  tidyBk  p      = tidyBaseKind (mkTidy (bkMetas p)) p

  prettyModifiedPlural w q  = \case
    0 -> "no "   ++ q ++ " " ++ w ++ "s"
    1 -> "1 "    ++ q ++ " " ++ w
    n -> show n ++ " " ++ q ++ " " ++ w ++ "s"
  
  prettyModifiedArgs = prettyModifiedPlural "argument"
  prettyArgs         = prettyModifiedArgs ""
  prettyMoreArgs     = prettyModifiedArgs "more"
  prettyLessArgs     = prettyModifiedArgs "less"

  prettyMoreParams = prettyModifiedPlural "parameter" "more"

  bt s = "`" ++ s ++ "`"

  prettyVarCons = \case
    Left x -> "variable " ++ bt (external x)
    Right i -> "constructor " ++ bt (show i)

  prettyBk = \case
    K.Top     -> "type"
    K.Session -> "session type"
    K.Channel -> "channel type"
    ψ@K.VarBK{} -> "type of base kind " ++ bt (tidyBk ψ)

  -- | Explain, component by component, why a kind is not a subkind of the one
  -- required (the header already states the subkind relation failed). A kind
  -- pairs a multiplicity (linear vs unrestricted -- how many times a value may be
  -- used) with a base kind (plain type, session type, channel type); either
  -- component can break the subkind relation, so we spell out each one that does,
  -- relating it to the offending type. Silent for arrow or variable kinds, where
  -- a component-wise story does not apply.
  kindMismatchHint :: String -> K.Kind -> K.Kind -> String
  kindMismatchHint t actual@K.Proper{} expected@K.Proper{} = multHint ++ bkHint
    where
      K.Proper _ am abk = actual
      K.Proper _ em ebk = expected
      multHint
        | not (am K.<: em) =
            "  hint: " ++ bt t ++ " is " ++ multWord am
              ++ ", but this position requires " ++ multReq em ++ "\n"
        | otherwise = ""
      bkHint
        | not (abk K.<: ebk) =
            "  hint: " ++ bt t ++ " is a " ++ prettyBk abk
              ++ ", but this position requires a " ++ prettyBk ebk ++ "\n"
        | otherwise = ""
      multWord = \case
        K.Lin{} -> "linear (it must be used exactly once)"
        K.Un{}  -> "unrestricted"
        m       -> "of multiplicity " ++ bt (tidyM m)
      multReq = \case
        K.Un{}  -> "an unrestricted type (one that may be discarded or shared)"
        K.Lin{} -> "a linear type"
        m       -> "a type of multiplicity " ++ bt (tidyM m)
  kindMismatchHint _ _ _ = ""

  -- | Render one side of a multiplicity mismatch
  multSide :: Source -> K.Multiplicity -> Origin -> String
  multSide src m (Origin sp) =
    bt (tidyM m) ++ multAdj ++ " inferred from" ++locateSpan src sp
    where
    multAdj = case m of
      K.Lin{} -> " (linear)"
      K.Un{}  -> " (unrestricted)"
      _       -> ""

  -- | A snippet of the origin span, unless it is not in the source (e.g. an
  -- inferred multiplicity), in which case just end the line.
  locateSpan :: Source -> Span -> String
  locateSpan src sp@(Span fp _ _)
    | Map.member fp src = ":\n" ++ snippet src sp True
    | otherwise         = "\n"

-- | For each of the eight session-type constructors, name the operator that
-- consumes the endpoint. Returns 'Nothing' when the type does not currently
-- expose a session action at its head (e.g. it is a function type, a name
-- yet to be unfolded, or an unsolved metavariable). Walks through @;@
-- ('AppSemi') so the /next/ action of a sequenced session is reported.
sessionHint :: TK.KindedType -> Maybe String
sessionHint = go
  where
    go = \case
      TK.End _ TK.Out              -> Just "close"        -- Close
      TK.End _ TK.In               -> Just "wait"         -- Wait
      TK.Message _ _ TK.Out        -> Just "send"         -- Message Out
      TK.Message _ _ TK.In         -> Just "receive"      -- Message In
      TK.AppMessage _ _ TK.Out _   -> Just "send"
      TK.AppMessage _ _ TK.In  _   -> Just "receive"
      TK.Choice _ _ TK.Out _       -> Just "select"       -- Choice Out (select)
      TK.Choice _ _ TK.In  _       -> Just "match"        -- Choice In  (branch)
      TK.AppLinChoice _ TK.Out _   -> Just "select"
      TK.AppLinChoice _ TK.In  _   -> Just "match"
      TK.QuantS _ _ TK.Out         -> Just "sendType"     -- Type Out
      TK.QuantS _ _ TK.In          -> Just "receiveType"  -- Type In
      TK.AppQuantS _ TK.Out _ _ _  -> Just "sendType"
      TK.AppQuantS _ TK.In  _ _ _  -> Just "receiveType"
      TK.AppSemi _ t _             -> go t
      _                            -> Nothing

showErrors :: Source -> [Error] -> String
showErrors src = intercalate "\n" . map (toMessage src)

printErrors :: Source -> [Error] -> IO ()
printErrors src es = hPutStrLn stderr $ showErrors src es

-- | The ordinal 'String' of an 'Integral'.
ordinal :: (Integral a, Show a) => a -> String
ordinal i = show i ++ suffix
  where suffix | i' > 10 && i' < 20 = "th"
               | otherwise = suffix' (i' `mod` 10)
        suffix' = \case 1 ->"st"; 2 ->"nd"; 3 ->"rd"; _ ->"th"
        i' = abs i 

-- | From MissingH. Removes any whitespace characters that are present at the
-- start or end of a string.
strip :: String -> String
strip = lstrip . rstrip

-- | From MissingH. Same as 'strip', but applies only to the left side of the
-- string.
lstrip :: String -> String
lstrip = \case 
  []                 -> []
  s@(x:xs) 
    | elem x " \t\r\n" -> lstrip xs
    | otherwise      -> s

-- | From MissingH. Same as 'strip', but applies only to the right side of the
-- string.
rstrip :: String -> String
rstrip = reverse . lstrip . reverse

rpad :: Int -> a -> [a] -> [a]
rpad n c s = s ++ replicate (n - length s) c
