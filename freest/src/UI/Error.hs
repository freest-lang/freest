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
import Syntax.Type.Kinded qualified as TK
import Syntax.Type.Unkinded qualified as TU
import Validation.Constraint qualified as C
import Compiler.Bug ( internalError )

import Data.List ( intercalate, nub )
import Data.Map.Strict qualified as Map
import Data.List qualified as List
import Data.Char qualified as Char
import Data.Maybe ( fromMaybe )
import Debug.Trace ( traceM )
import System.IO ( stderr, hPutStrLn )

-- | The errors that can be found in a FreeST program.
data Error
  = ArrowMultMismatch 
      Span 
      (Either Variable E.KindedExp) 
      Int
      K.Multiplicity 
      K.Multiplicity
  | CannotInferHigherKindedTypeApp Span K.Kind
  | CannotSatisfyMultConstraint Span K.Multiplicity K.Multiplicity
  | CannotSynthesisePack Span E.KindedExp
  | CannotSynthesiseReceiveType Span
  | CannotSynthesiseSelect Span Identifier
  | CannotSynthesiseSendType Span
  | ConflictingDefs Span (Level String String String) [Span]
  | ConsOutOfScope Span Identifier
  | DConsPatArgMismatch Span Identifier Int Int
  | ExpectsTooManyArgs Span TK.KindedType Int Int
  | ExpectsTooManyArgsK Span Identifier K.Kind
  | ExposeError Span (Either E.Pat E.KindedExp) String TK.KindedType
  | TooManyEArgs Span TK.KindedType Int Int
  | TooManyKArgs Span TK.KindedType K.Kind Int Int
  | IllegalChoice Span Identifier TK.KindedType
  | KindMismatch Span K.Kind TK.KindedType
  | KindMismatchK Span K.Kind K.Kind TU.ScopedType
  | KSigLacksBinding Span Identifier
  | LacksKindSig Span Identifier
  | LacksTypeSig Span Variable
  | LexicalError Span Char
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
    (Either (Either Variable E.Pat) E.KindedExp)
  | LinVarAtEndOfScope Span (Either Variable Identifier) TK.KindedType
  | MultipleConsDecls Span [Identifier]
  | MultipleFieldDecls Span [Identifier]
  | MultipleKindSigs Span [Identifier]
  | MultipleTypeDecls Span [Identifier]
  | MultipleVarDecls Span [Variable]
  | MultVarOutOfScope Span Variable
  | NonLinPat Span E.Pat TK.KindedType
  | ParseError Span (Token, [String])
  | PartiallyAppliedSelect Span Identifier
  | PrekindMismatch Span K.Prekind TK.KindedType K.Kind
  | ProperKindMismatch Span TK.KindedType K.Kind
  | RestrictedFunInMutual Span Variable TK.KindedType
  | SigLacksDef Span Variable
  | TypeConsOutOfScope Span Identifier
  | TypeMismatch Span TK.KindedType TK.KindedType (Either E.KindedExp E.Pat)
  | TypeMismatchList Span TK.KindedType (Either E.KindedExp E.Pat)
  | TypeMismatchChoice Span TK.KindedType Identifier E.Pat
  | TypeMismatchExists Span TK.KindedType (Either E.Pat E.KindedExp) -- TODO: should be (Either E.Pat E.Exp) everywhere. Mnemonic: pats occur on LHSs, exps on RHSs
  | TypeMismatchReceiveType Span TK.KindedType
  | TypeMismatchSelect Span TK.KindedType Identifier E.KindedExp
  | TypeMismatchSendType Span TK.KindedType
  | TypeMismatchTuple Span Int TK.KindedType (Either E.KindedExp E.Pat)
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
  | MixedSessionVarPats Span E.Pat E.Pat
  | UnifyFailed Span C.Constraints
    -- ^ Kind-inference constraints have no solution.

-- | Errors can be tracked to the source code.
instance Located Error where
  -- | Returns the span of an 'Error', i.e., where the error occurs in the
  -- source code.
  getSpan = \case
    ArrowMultMismatch s _ _ _ _ -> s
    CannotInferHigherKindedTypeApp s _ -> s
    CannotSatisfyMultConstraint s _ _ -> s
    CannotSynthesisePack s _ -> s
    CannotSynthesiseReceiveType s -> s
    CannotSynthesiseSelect s _ -> s
    CannotSynthesiseSendType s -> s
    ConflictingDefs s _ _ -> s
    ConsOutOfScope s _ -> s
    DConsPatArgMismatch s _ _ _ -> s
    ExpectsTooManyArgs s _ _ _ -> s
    ExpectsTooManyArgsK s _ _ -> s
    ExposeError s _ _ _ -> s
    TooManyEArgs s _ _ _ -> s
    TooManyKArgs s _ _ _ _ -> s
    IllegalChoice s _ _ -> s
    KindMismatch s _ _ -> s
    KindMismatchK s _ _ _ -> s
    KSigLacksBinding s _ -> s
    LacksKindSig s _ -> s
    LacksTypeSig s _ -> s
    LexicalError s _ -> s
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
    PrekindMismatch s _ _ _ -> s
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
    UnifyFailed s _ -> s

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

lookupSrc :: Source -> FilePath -> [String]
lookupSrc src fp = fromMaybe
  (internalError $ "file not in source map: " ++ fp)
  (src Map.!? fp)

snippet :: Located a => Source -> a -> Bool -> String
snippet src (getSpan -> s@(Span fp (sl, sc) (el, ec))) showSpan =
  unlines ([ spaces (n + 1) ++ show s | showSpan ] ++
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
header sort (getSpan -> s) = show s ++ ": " ++ sort ++ ":"

errorHeader :: Located a => a -> String
errorHeader = header "error"

makeError :: Located a => Source -> a -> String -> String
makeError src (getSpan -> s) msg =
  errorHeader s ++ "\n" ++ msg ++ "\n" ++ snippet src s False

toMessage :: Source -> Error -> String
toMessage src = \case
  ArrowMultMismatch s xe i m m' -> makeError src s
    ("Expected " ++ showMult m ++ ", but got " ++ showMult m'
      ++ " instead"
      ++ (if i > 0
          then " (on the " ++ ordinal (i + 1) ++ " parameter of this "
            ++ (case xe of Left _ -> "function definition" -- should not occur
                           Right _ -> "expression") ++ ")"
          else ""))
    where
      showMult = \case
        K.Lin{}   -> "a linear function"
        K.Un{}    -> "an unrestricted function"
        m@K.Sup{} -> "a function with multiplicity " ++ bt (unparse m)
  CannotInferHigherKindedTypeApp s k -> makeError src s
    ("Cannot infer type application for a type of kind " ++ bt (unparse k))
    ++ "Please provide all type arguments before this one"
  CannotSatisfyMultConstraint s m1 m2 -> makeError src s
    "Cannot satisfy multiplicity constraints"
    ++ "(Cannot unify " ++ bt (unparse m1) ++ " with " ++ bt (unparse m2) ++ ")"
  CannotSynthesisePack s e -> makeError src s
    "Could not infer a type for this package expression"
  CannotSynthesiseReceiveType s -> makeError src s
    "Could not infer a type for this `receiveType` expression"
  CannotSynthesiseSelect s id -> makeError src s
    "Could not infer a type for this `select` expression"
  CannotSynthesiseSendType s -> makeError src s
    "Could not infer a type for this `sendType` expression"
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
      ++ " arguments, but it was given " ++ show m)
  ExpectsTooManyArgs s t n m -> makeError src s
     ("This function expects " ++ prettyArgs n
       ++ ", but its type " ++ bt (unparse t) ++ " takes"
       ++ case m of
        0 -> " none"
        n -> " only " ++ show n)
  ExpectsTooManyArgsK s i k -> makeError src s
    ("Type " ++ bt (show i) ++ " expects too many arguments, its kind "
      ++ bt (unparse k) ++ " takes only " ++ show (K.depth k))
  ExposeError s pe msg t -> makeError src s
    case pe of
      Left _  -> "Cannot match this pattern against the expected type " ++ bt (unparse t)
      Right _ -> "Expected " ++ msg ++ ", but got an expression of type " ++ bt (unparse t)
    ++ case pe of Left _ -> "(It matches " ++ msg ++ ")"; Right{} -> ""
  TooManyEArgs s t n m -> makeError src s
    ("Got " ++ prettyModifiedArgs "unexpected" (m - n))
    ++ "(Cannot apply an expression of type " ++ bt (unparse t) ++ " to "
    ++ thirdPerson (m - n) ++ ")"
  TooManyKArgs s t k n m -> makeError src s
    ("Got " ++ prettyModifiedArgs "unexpected" (m - n))
    ++ "(A type of kind " ++ bt (unparse k) ++ " cannot be applied to further arguments)"
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
      ("Couldn't match expected kind " ++ bt (unparse k1)
        ++ " with actual kind " ++ bt (unparse $ TK.kindOf t))
    -- where
    --   diff = (K.depth k2 - K.depth k1)
  KindMismatchK s k1 k2 t -> makeError src s
      ("Couldn't match expected kind " ++ bt (unparse k1)
        ++ " with actual kind " ++ bt (unparse k2))
    -- where
    --   diff = (K.depth k2 - K.depth k1)
  KSigLacksBinding s i -> makeError src s
    ("The kind signature for type " ++ bt (show i)
      ++ " lacks an accompanying binding")
  LacksKindSig s i -> makeError src s
    ("Type " ++ bt (show i) ++ " lacks a kind signature")
  LacksTypeSig s x -> makeError src s
    ("Function " ++ bt (external x) ++ " is missing a type signature")
  LexicalError span c -> makeError src span
    ("Unsupported character " ++ bt [c])
  LinVarAtEndOfScope s xi _ -> makeError src s
    ("Linear " ++ prettyVarCons xi ++ " was not consumed")
  LinConsumedInGuard s xi t -> errorHeader s ++ "\n"
      ++ ((case m' of
        K.Lin{} -> "Linear " ++ prettyVarCons xi ++ " of "
        _ -> "Potentially linear " ++ prettyVarCons xi ++ " with multiplicity " ++ bt (unparse m') ++ " and ")
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
        _ -> "Potentially linear " ++ prettyVarCons xi ++ " with multiplicity " ++ bt (unparse m') ++ " and ")
      ++ "type " ++ bt (unparse t) ++ ", bound at\n"
      ++ snippet src xi True
      ++ " was consumed in body of "
      ++ (case m of 
        K.Un{} -> "an unrestricted function"
        _      -> "a function with multiplicity " ++ bt (unparse m))
      ++ "\n" ++ snippet src fe True)
    ++ "(This would allow duplicating or discarding it. "
    ++ "Consider using a restricted function instead.)"
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
      K.Proper _ m _       -> " potentially linear type " ++ bt (unparse t) ++ " with multiplicity " ++ bt (unparse m)
      _ -> internalError "pattern with non-proper type")
  ParseError s (_, ss) -> makeError src s
    "Parse error"
    ++ case ss of
      [] -> ""
      [x] -> "(Expected " ++ x ++ ")"
      ss  -> "(Expected one of: " ++ intercalate ", " ss ++ ")"
  PrekindMismatch s pk t k -> makeError src s
    ("Expected a " ++ prettyPk pk ++ ", but got " ++
      (case k of
        K.Proper _ m pk -> prettyPk pk ++ " " ++ bt (unparse t)
        k               -> bt (unparse t) ++ " of kind " ++ bt (unparse k))
      ++ " instead")
  ProperKindMismatch s t k -> makeError src s
    ("Expected " ++ prettyMoreArgs arity ++ " to " ++ bt (unparse t))
    ++ "(Expected a proper type, but got " ++ bt (unparse t)
    ++ " of kind " ++ bt (unparse k) ++ ")"
    where arity = K.depth k
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
      ++ "was not consumed evenly among the branches of a"
      ++ (case fpe of
        Left (Left  x) -> " function definition"
        Left (Right p) -> " value definition"
        Right e        -> case e of
          E.Case{} -> " case expression"
          E.If{}   -> " conditional expression"
          _        -> "n expression") ++ "\n"
      ++ snippet src fpe True)
  TypeMismatch s t u _ -> makeError src s
    ("Couldn't match expected type " ++ bt (unparse t)
      ++ " with actual type " ++ bt (unparse u))
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
  UnifyFailed s cs -> makeError src s $
    "Unsolvable kind-inference constraints:\n  "
    ++ intercalate "\n  " (map show (foldr (:) [] cs))
  where
    thirdPerson = \case 1 -> "it"; _ -> "them"

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

    prettyPk = \case
      K.Top     -> "type"
      K.Session -> "session type"
      K.Channel -> "channel type"
      K.VarPK ψ -> "prekind " ++ show ψ ++ " type"

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
