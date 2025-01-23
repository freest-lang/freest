{- |
Module      :  UI.Error
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Errors. A work in progress.
-}
{-# LANGUAGE LambdaCase #-}
module UI.Error 
  (Error(..))
where 

import Parser.Token
import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import qualified Syntax.Type as T
import Utils

import Data.List (intercalate)
import qualified Data.Map.Strict as Map

data Error 
  = LexicalError Span Char 
  | ParseError Span (Token, [String])
  | OutOfScope Span Variable
  | ConsOutOfScope Span Identifier
  | TypeOutOfScope Span Identifier
  | ConflictingDefs (Map.Map (Level String String) [Span])
  | MultipleVarDecls Span Variable
  | MultipleConsDecls Span Identifier
  | MultipleTypeDecls Span Identifier
  | MultipleKindSigs Span Identifier
  | LacksKindSig Span Identifier
  | GivenTooManyArgs Span E.Exp T.Type Int Int
  | LinVarsConsumedInUnFun Span [Variable] E.Exp
  | LinVarsCreatedInUnFun Span [Variable] E.Exp
  | ExposeError Span String (Either E.Exp E.Pat) T.Type
  | UnexpectedArg Span (Level T.Type K.Kind) (Level E.Exp T.Type) Int E.Exp
  | NonLinPat Span E.Pat T.Type
  | KindMismatch Span K.Kind T.Type K.Kind
  | ProperKindMismatch Span T.Type K.Kind
  | GivenTooManyArgsK Span T.Type Int Int
  | ExpectsTooManyArgsK Span Identifier K.Kind
  | InvalidType Span T.Type
  | TypeMismatch Span T.Type T.Type (Either E.Exp E.Pat)
  | TypeCtxMismatch Span E.Exp [(Variable, T.Type)] [(Variable, T.Type)]
  | ConstructorArgumentMismatch Span Identifier Int Int
  | ChoiceNotAllowed Span Identifier T.Type
  | UnsupportedError Span String

instance Located Error where
  getSpan = \case 
    LexicalError s _ -> s
    ParseError s _ -> s
    OutOfScope s _ -> s
    ConsOutOfScope s _ -> s
    TypeOutOfScope s _ -> s
    ConflictingDefs xss -> foldr1 spanFromTo $ concat $ Map.elems xss
    MultipleVarDecls s _ -> s
    MultipleConsDecls s _ -> s
    MultipleTypeDecls s _ -> s
    MultipleKindSigs s _ -> s
    LacksKindSig s _ -> s
    GivenTooManyArgs s _ _ _ _ -> s
    LinVarsConsumedInUnFun s _ _ -> s
    LinVarsCreatedInUnFun s _ _ -> s
    ExposeError s _ _ _ -> s
    UnexpectedArg s _ _ _ _ -> s
    NonLinPat s _ _ -> s
    KindMismatch s _ _ _ -> s
    ProperKindMismatch s _ _ -> s
    GivenTooManyArgsK s _ _ _ -> s
    ExpectsTooManyArgsK s _ _ -> s
    InvalidType s _ -> s
    TypeMismatch s _ _ _ -> s
    TypeCtxMismatch s _ _ _ -> s
    ConstructorArgumentMismatch s _ _ _ -> s
    ChoiceNotAllowed s _ _ -> s
    UnsupportedError s _ -> s

  setSpan = internalError "span not settable for Error type."

instance Show Error where
  show e = show (getSpan e) ++ ": error:"++showError e
    where 
      showError :: Error -> String
      showError = \case
        LexicalError _ inp ->
          "\n  Lexical error on input `"++show inp++"`"
        ParseError _ (_,ss) -> 
          "\n  Parse error, expected: `"++intercalate "`, `" ss++"`"
        OutOfScope _ x -> 
          "\n  Not in scope: variable `"++external x++"`"
        ConsOutOfScope _ i -> 
          "\n  Not in scope: constructor `"++show i++"`"
        TypeOutOfScope _ i ->
          "\n Not in scope: type constructor `"++show i++"`"
        ConflictingDefs vos -> 
          "\n  Conflicting definitions in patterns:"
          ++Map.foldrWithKey (\case 
              ExpLevel x -> \ss msg -> 
                  "\n    Variable `"++x++"` bound at:"
                  ++foldr (\s msg' -> "\n      "++show s++msg') "" ss
                  ++msg
              TypeLevel a -> \ss msg -> 
                  "\n    Type variable `"++a++"` bound at:"
                  ++foldr (\s msg' -> "\n      "++show s++msg') "" ss
                  ++msg)
          "" vos
        MultipleVarDecls _ i ->
          "\n  Multiple declarations of variable `"++show i++"`"
        MultipleConsDecls _ i ->
          "\n  Multiple declarations of constructor `"++show i++"`"
        MultipleTypeDecls _ i ->
          "\n  Multiple declarations of type `"++show i++"`"
        MultipleKindSigs _ i ->
          "\n  Multiple kind signatures for type `"++show i++"`"
        LacksKindSig _ i -> 
          "\n Type `"++show i++"` lacks an accompanying kind signature."
        GivenTooManyArgs _ f t expected actual ->
          "\n  Expression `"++show f++"` of type `"++show t++"` takes "++show expected++" arguments, but it was given "++show actual++"."
        LinVarsConsumedInUnFun _ xs e ->
          "\n  Linear variables `" ++ intercalate "`, `" (map show xs) ++ "` consumed in the body of unrestricted function `" ++ show e ++"`"++
          "\n  (This allows duplicating or discarding the variables! Consider using a linear function instead.)"
        LinVarsCreatedInUnFun _ xs e ->
          "\n  Linear variables `" ++ intercalate "`, `" (map show xs) ++ "` consumed in the body of unrestricted function `" ++ show e ++"`"++
          "\n  (This allows duplicating or discarding the variables! Consider using a linear function instead.)"
        ExposeError _ s e t -> 
          "\n  Expecting "++s++" type for "++showExpPat e++", but got type `"++show t++"`"
        UnexpectedArg _ (TypeLevel k) (ExpLevel e) n f -> 
          "\n  Expecting a type argument of kind `"++show k++"`, but got value argument `"++show e++
          "\n  In the "++show n {- TODO: use numerals-}++"th argument of function `"++show f++"`."
        UnexpectedArg _ (ExpLevel  t) (TypeLevel u) n f -> 
          "\n  Expecting a value argument of type `"++show t++"`, but got type argument `"++show u++
          "\n  In the "++show n {- TODO: use numerals-}++"th argument of function `"++show f++"`."
        NonLinPat s p t ->
          "\n  Non-linear pattern `"++show p++"` on linear type `"++show t++"`." -- TODO: better error
        KindMismatch s k1 t k2 ->
          "\n  Expected kind "++show k1++" for type "++show t++", but got kind "++show k2
        ProperKindMismatch s t k -> 
          "\n  Expected a proper kind for type "++show t++", but got kind "++show k
        GivenTooManyArgsK s t n m ->
          "\n  Type "++show t++" expects "++show n++" arguments, but it was given "++show m++"."
        ExpectsTooManyArgsK s i k ->
          "\n  Type "++show i++" expects too many arguments, it should have kind "++show k++"."
        InvalidType s t ->
          "\n  Invalid type: "++show t
        TypeMismatch s t u ep ->
          "\n  Couldn't match expected type "++show t++" with actual type "++show u++" in the "++showExpPat ep++"."
        TypeCtxMismatch s e tctx1 tctx2 -> 
          -- TODO: different messages for abstractions, cases and conditional expressions; ideally better than Freest 3.
          "\n  Couldn't match the final contexts in two distinct branches in a case expression " ++
          "\n  \t       One context is " ++ show tctx1 ++
          "\n  \t         the other is " ++ show tctx2 ++
          "\n  \tand the expression is " ++ show e ++
          "\n  \t(was a variable consumed in one branch and not in the other?)" ++
          "\n  \t(is there a variable with different types in the two contexts?)"
        ConstructorArgumentMismatch _ i n m ->
          "\n  The constructor `"++show i++"` should have "++show n++" arguments, but has been given "++show m++"."
        ChoiceNotAllowed s i t ->
          "\n  Choice `"++show i++"` is not allowed by type "++show t
        UnsupportedError _ m ->
          "\n  " ++ m

      showExpPat = \case 
        Left  p -> "pattern `"++show p++"`"
        Right e -> "expression `"++show e++"`"