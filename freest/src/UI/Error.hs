{- |
Module      :  UI.Error
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Errors. A work in progress.
-}
{-# LANGUAGE LambdaCase #-}


module UI.Error
  ( Error(..)
  , Source
  , toMessage
  , showErrors
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
import Utils

import Data.List (intercalate,nub)
import Data.Map.Strict qualified as Map
import Syntax.Expression
import Data.List qualified as List
import Data.Char qualified as Char

-- | The errors that can be found in a FreeST program.
data Error
  = ArrowMultMismatch Span (Either Variable E.KindedExp) Int
    K.Multiplicity K.Multiplicity
  | CannotSynthesisePack Span E.KindedExp
  | CannotSynthesiseReceiveType Span
  | CannotSynthesiseSelect Span Identifier
  | CannotSynthesiseSendType Span
  | ConflictingDefs Span (Level String String) [Span]
  | ConsOutOfScope Span Identifier
  | DConsPatArgMismatch Span Identifier Int Int
  | ExpectsTooManyArgs Span (Either Variable E.KindedExp) TK.KindedType Int Int
  | ExpectsTooManyArgsK Span Identifier K.Kind
  | ExposeError Span (Either E.Pat E.KindedExp) String TK.KindedType
  | GivenTooManyArgs Span E.KindedExp TK.KindedType Int Int
  | GivenTooManyArgsK Span TK.KindedType K.Kind Int Int
  | IllegalChoice Span Identifier TK.KindedType
  | KindMismatch Span K.Kind TK.KindedType
  | KindMismatchK Span K.Kind K.Kind TU.ScopedType
  | LacksKindSig Span Identifier
  | LacksTypeSig Span Variable
  | LexicalError Span Char
  | LinConsumedInUnFun Span (Either Variable Identifier) TK.KindedType (Either Variable E.KindedExp)
  | LinNotConsumedEvenly Span (Either Variable Identifier) TK.KindedType
    (Either (Either Variable E.Pat) E.KindedExp)
  | LinVarAtEndOfScope Span (Either Variable Identifier) TK.KindedType
  | MultipleConsDecls Span [Identifier]
  | MultipleFieldDecls Span [Identifier]
  | MultipleKindSigs Span [Identifier]
  | MultipleTypeDecls Span [Identifier]
  | MultipleVarDecls Span [Variable]
  | NonLinPat Span E.Pat TK.KindedType
  | ParseError Span (Token, [String])
  | PartiallyAppliedSelect Span Identifier
  | PrekindMismatch Span K.Prekind TK.KindedType K.Kind
  | ProperKindMismatch Span TK.KindedType K.Kind
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
  | UnexpectedArg Span Int (Level (Maybe TK.KindedType) K.Kind) (Level E.KindedExp TK.KindedType)
  | UnexpectedParam Span Int (Either Variable E.KindedExp) (Level TK.KindedType K.Kind)
    (Level E.Pat Variable) 
  | UnsupportedError Span String String
  | VarOutOfScope Span Variable

-- | Errors can be tracked to the source code.
instance Located Error where
  -- | Returns the span of an 'Error', i.e., where the error occurs in the
  -- source code.
  getSpan = \case
    ArrowMultMismatch s _ _ _ _ -> s
    CannotSynthesisePack s _ -> s
    CannotSynthesiseReceiveType s -> s
    CannotSynthesiseSelect s _ -> s
    CannotSynthesiseSendType s -> s
    ConflictingDefs s _ _ -> s
    ConsOutOfScope s _ -> s
    DConsPatArgMismatch s _ _ _ -> s
    ExpectsTooManyArgs s _ _ _ _ -> s
    ExpectsTooManyArgsK s _ _ -> s
    ExposeError s _ _ _ -> s
    GivenTooManyArgs s _ _ _ _ -> s
    GivenTooManyArgsK s _ _ _ _ -> s
    IllegalChoice s _ _ -> s
    KindMismatch s _ _ -> s
    KindMismatchK s _ _ _ -> s
    LacksKindSig s _ -> s
    LacksTypeSig s _ -> s
    LexicalError s _ -> s
    LinNotConsumedEvenly s _ _ _ -> s
    LinVarAtEndOfScope s _ _ -> s
    LinConsumedInUnFun s _ _ _ -> s
    MultipleConsDecls s _ -> s
    MultipleFieldDecls s _ -> s
    MultipleKindSigs s _ -> s
    MultipleTypeDecls s _ -> s
    MultipleVarDecls s _ ->  s
    NonLinPat s _ _ -> s
    ParseError s _ -> s
    PrekindMismatch s _ _ _ -> s
    ProperKindMismatch s _ _ -> s
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
    UnexpectedParam s _ _ _ _ -> s
    UnsupportedError s _ _ -> s
    VarOutOfScope s _ -> s

  -- There should be no need to relocate an error. (At least for now...)
  setSpan = internalError "span not settable for Error type."

type Source = Map.Map FilePath [String]

getFromSpan :: Located a => Source -> a -> String
getFromSpan src (getSpan -> (Span fp (sl, sc) (_, ec))) =
  take (ec - sc) . drop (sc - 1) $ (src Map.! fp) !! (sl - 1)

getLineFromSpan :: Located a => Source -> a -> String
getLineFromSpan src (getSpan -> Span fp (sl, _) (_, _)) =
  (src Map.! fp) !! (sl - 1)

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
    srcf = src Map.! fp
    l = srcf !! (min (length srcf) sl - 1)
    spaces x = replicate x ' '
    carets x = replicate x '^'

multiLineSnippet :: Located a => Source -> a -> String
multiLineSnippet src (getSpan -> Span fp (sl, sc) (el, ec)) =
  unlines $ (spaces n ++ sep) : zipWith lineCarets [sl..] ls
  where
    n = length (show el)
    sep = " | "
    ls  = take (el - (sl - 1)) $ drop (sl - 1) $ src Map.! fp
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

errorHeader :: Located a => a -> String
errorHeader (getSpan -> s) = show s ++ ": error:"

makeError :: Located a => Source -> a -> String -> String
makeError src (getSpan -> s) msg =
  errorHeader s ++ "\n" ++ msg ++ "\n" ++ snippet src s False

prettyKind :: K.Kind -> String
prettyKind = \case
  K.Proper _ m pk -> prettyMulti m ++ prettyPre pk
  K.Arrow _ k1 k2 -> prettyKind k1 ++ " -> " ++ prettyKind k2
  K.Var _ τ       -> "kind variable " ++ external τ
  where
    prettyMulti = \case
      K.Lin -> "a linear"
      K.Un -> "an unrestricted"
      K.VarM φ -> "a multiplicity variable " ++ external φ
    prettyPre = \case
      K.Top -> ""
      K.Session -> " session"
      K.Channel -> " channel"
      K.VarPK ψ -> " prekind variable " ++ external ψ

toMessage :: Source -> Error -> String
toMessage src = \case
  ArrowMultMismatch s xe i m m' -> makeError src s
    ("Expected " ++ showMult m ++ " function, but got " ++ showMult m'
      ++ " one instead" 
      ++ (if i > 0
          then " (on the " ++ ordinal (i + 1) ++ " parameter of this " 
            ++ (case xe of Left _ -> "function definition" -- should not occur
                           Right _ -> "expression") ++ ")"
          else ""))
    where
      showMult = \case
        K.Lin    -> "a linear"
        K.Un     -> "an unrestricted"
        K.VarM x -> "a multiplicity" ++ external x
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
      ExpLevel x -> "variable " ++ x
      TypeLevel a -> "type variable " ++ bt a)
    ++ "Conflicting definitions at:\n" ++ unlines (map show ss)
  ConsOutOfScope s i -> makeError src s
    ("Constructor out of scope: " ++ bt (show i))
  DConsPatArgMismatch s i n m -> makeError src s
    ("Constructor " ++ bt (show i) ++ " takes " ++ show n
      ++ " arguments, but it was given " ++ show m)
  ExpectsTooManyArgs s _ t n m -> makeError src s
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
  GivenTooManyArgs s e t n m -> makeError src s
    ("Got " ++ prettyQArgs "unexpected" (m - n))
    ++ "(Cannot apply an expression of type " ++ bt (unparse t) ++ " to " 
    ++ thirdPerson (m - n) ++ ")"
  GivenTooManyArgsK s t k n m -> makeError src s
    ("Got " ++ prettyQArgs "unexpected" (m - n))
    ++ "(Cannot apply a type of kind " ++ bt (unparse k) ++ " to " 
    ++ thirdPerson (m - n) ++ ")"
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
  LacksKindSig s i -> makeError src s
    ("Type " ++ bt (show i) ++ " lacks a kind signature")
  LacksTypeSig s x -> makeError src s
    ("Function " ++ bt (external x) ++ " is missing a type signature")
  LexicalError span c -> makeError src span
    ("Unsupported character " ++ bt [c])
  LinVarAtEndOfScope s xi _ -> makeError src s
    ("Linear variable " ++ prettyVarCons xi ++ " was not consumed")
  LinConsumedInUnFun s xi t fe -> errorHeader s ++ "\n" ++
    ("Linear " ++ prettyVarCons xi
      ++ " of type " ++ unparse t ++ ", bound at\n"
      ++ snippet src xi True
      ++ " was consumed in body of an unrestricted function\n"
      ++ snippet src fe True)
    ++ "(This would allow duplicating or discarding it. "
    ++ "Consider using a linear function instead.)"
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
    ++ "Duplicate signatures  at:\n"
    ++ unlines (map (("  " ++) . show . getSpan) is)
  MultipleTypeDecls s is -> makeError src s
    ("Multiple declarations of type " ++ bt (show (head is)))
    ++ "Duplicate declarations at:\n"
    ++ unlines (map (("  " ++) . show . getSpan) is)
  MultipleVarDecls s xs -> makeError src s
    ("Multiple declarations of variable " ++ bt (external (head xs)))
    ++ "Duplicate declarations at:\n"
    ++ unlines (map (("  " ++) . show . getSpan) xs)
  NonLinPat s p t -> makeError src s
    ("Non-linear pattern for linear type " ++ bt (unparse t))
  ParseError s (_, ss) -> makeError src s
    "Parse error"
    ++ "(Expected one of: " ++ intercalate ", " ss ++ ")"
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
  UnexpectedArg s n a1 a2 -> makeError src s -- TODO: use n to write the ordinal of the argument?
    (case (a1, a2) of 
      (TypeLevel k, ExpLevel e) ->
        "Expected a type argument of kind " ++ bt (unparse k) 
        ++ ", but got a value argument"
      (ExpLevel  t, TypeLevel u) ->
        "Expected a value argument "
        ++ maybe "" (\t -> "of type " ++ bt (unparse t)) t 
        ++ ", but got type argument")
  UnexpectedParam s n f p1 p2 -> makeError src s -- TODO: use n to write the ordinal of the parameter?
    (case (p1, p2) of 
      (TypeLevel k, ExpLevel p ) ->
        "Expected a type parameter of kind " ++ bt (unparse k) ++ ", but got a pattern"
      (ExpLevel  t, TypeLevel a) ->
        "Expected a pattern of type " ++ bt (unparse t) ++ ", but got a type parameter")
  UnsupportedError s msg1 msg2 -> makeError src s
    ("Unsupported feature: " ++ msg1)
    ++ msg2
  VarOutOfScope s x -> makeError src s
    ("Variable out of scope: " ++ bt (external x))
  where
    thirdPerson    = \case 
      1 -> "it"
      _ -> "them"

    prettyQArgs q  = \case 
      0 -> "no "   ++ q ++ " arguments"
      1 -> "1 "    ++ q ++ " argument"
      n -> show n ++ " " ++ q ++ " arguments"

    prettyArgs     = prettyQArgs ""

    prettyMoreArgs = prettyQArgs "more"

    prettyLessArgs = prettyQArgs "less"

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
printErrors src es = putStrLn $ showErrors src es
