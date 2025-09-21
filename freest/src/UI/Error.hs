{- |
Module      :  UI.Error
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Errors. A work in progress.
-}
{-# LANGUAGE LambdaCase #-}
module UI.Error
  (Error(..)
  ,errorToMessage)
where

import           Parser.Token
import           Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind       as K
import qualified Syntax.Type       as T
import           Utils

import           Data.List         (intercalate)
import qualified Data.Map.Strict   as Map

-- | The errors that can be found in a FreeST program.
data Error
  = LexicalError Span Char
  | ParseError Span (Token, [String])
  | VarOutOfScope Span Variable
  | TypeVarOutOfScope Span Variable
  | ConsOutOfScope Span Identifier
  | TypeOutOfScope Span Identifier
  | ConflictingDefs (Map.Map (Level String String) [Span])
  | MultipleVarDecls Span [Variable]
  | MultipleFieldDecls Span [Identifier]
  | MultipleConsDecls Span [Identifier]
  | MultipleTypeDecls Span [Identifier]
  | MultipleKindSigs Span [Identifier]
  | LacksKindSig Span Identifier
  | LacksTypeSig Span Variable
  | GivenTooManyArgs Span E.Exp T.Type Int Int
  | ExpectsTooManyArgs Span E.Exp T.Type Int Int
  | LinVarsConsumedInUnFun Span [Variable] E.Exp
  | LinVarsCreatedInUnFun Span [Variable] E.Exp
  | ExposeError Span String T.Type
  | UnexpectedArg Span (Level (Maybe T.Type) K.Kind) (Level E.Exp T.Type) Int E.Exp
  | UnexpectedParam Span (Level T.Type K.Kind) (Level E.Pat Variable) Int E.Exp
  | NonLinPat Span E.Pat T.Type
  | KindMismatch Span K.Kind T.Type K.Kind
  | ProperKindMismatch Span T.Type K.Kind
  | SessionTypeMismatch Span T.Type K.Kind
  | ChannelTypeMismatch Span T.Type K.Kind
  | ArrowMultiplicityMismatch Span E.Exp Int K.Multiplicity T.Type K.Multiplicity
  | GivenTooManyArgsK Span T.Type Int Int
  | ExpectsTooManyArgsK Span Identifier K.Kind
  | InvalidType Span T.Type
  | TypeMismatch Span T.Type T.Type (Either E.Exp E.Pat)
  | TypeMismatchSelect Span T.Type Identifier E.Exp
  | TypeMismatchList Span T.Type (Either E.Exp E.Pat)
  | TypeMismatchTuple Span Int T.Type (Either E.Exp E.Pat)
  | TypeCtxMismatch Span E.Exp (Map.Map (Either Variable Identifier) T.Type)
                               (Map.Map (Either Variable Identifier) T.Type)
  | ConstructorArgumentMismatch Span Identifier Int Int
  | IllegalChoice Span Identifier T.Type
  | PartiallyAppliedSelect Span Identifier
  | LinVarAtEndOfScope Span (Either Variable Identifier) T.Type
  | UnsupportedError Span String
  | SigLacksDef Span Variable

-- | Errors can be tracked to the source code.
instance Located Error where
  -- | Returns the span of an 'Error', i.e., where the error occurs in the
  -- source code.
  getSpan = \case
    LexicalError s _ -> s
    ParseError s _ -> s
    VarOutOfScope s _ -> s
    TypeVarOutOfScope s _ -> s
    ConsOutOfScope s _ -> s
    TypeOutOfScope s _ -> s
    ConflictingDefs xss -> foldr1 spanFromTo $ concat $ Map.elems xss
    MultipleVarDecls s _ ->  s
    MultipleFieldDecls s _ -> s
    MultipleConsDecls s _ -> s
    MultipleTypeDecls s _ -> s
    MultipleKindSigs s _ -> s
    LacksKindSig s _ -> s
    LacksTypeSig s _ -> s
    GivenTooManyArgs s _ _ _ _ -> s
    ExpectsTooManyArgs s _ _ _ _ -> s
    LinVarsConsumedInUnFun s _ _ -> s
    LinVarsCreatedInUnFun s _ _ -> s
    ExposeError s _ _ -> s
    UnexpectedArg s _ _ _ _ -> s
    UnexpectedParam s _ _ _ _ -> s
    NonLinPat s _ _ -> s
    KindMismatch s _ _ _ -> s
    ProperKindMismatch s _ _ -> s
    SessionTypeMismatch s _ _ -> s
    ChannelTypeMismatch s _ _ -> s
    ArrowMultiplicityMismatch s _ _ _ _ _ -> s
    GivenTooManyArgsK s _ _ _ -> s
    ExpectsTooManyArgsK s _ _ -> s
    InvalidType s _ -> s
    TypeMismatch s _ _ _ -> s
    TypeMismatchSelect s _ _ _ -> s
    TypeMismatchList s _ _ -> s
    TypeMismatchTuple s _ _ _ -> s
    TypeCtxMismatch s _ _ _ -> s
    ConstructorArgumentMismatch s _ _ _ -> s
    LinVarAtEndOfScope s _ _ -> s
    IllegalChoice s _ _ -> s
    PartiallyAppliedSelect s _ -> s
    UnsupportedError s _ -> s
    SigLacksDef s _ -> s
  -- | There should be no need to relocate an error. (At least for now...)
  setSpan = internalError "span not settable for Error type."


-- span = filePaht POS POS
-- POS = int int
getFromSpan :: String -> Span -> String
getFromSpan src (Span _ (sl, sc) (_, ec)) =
  take (ec - sc) . drop (sc - 1) $ lines src !! (sl - 1)

getLineFromSPan :: String -> Span -> String
getLineFromSPan src (Span _ (sl, _) (_, _)) =
  lines src !! (sl - 1)

snippetWithCaret :: String -> Span -> String
snippetWithCaret src (Span _ (sl, sc) (_, ec)) =
  let line       = lines src !! (sl - 1)
      start      = max 0 (sc - 1)
      end        = max start (ec - 1)
      len        = max 1 (end - start)
      caretLine  = replicate start ' ' ++ replicate len '^'
  in "  |\n"
     ++ show sl ++ " | " ++ line ++ "\n"
     ++ "  | " ++ caretLine




shortHeader :: Span -> String -> String
shortHeader span msg = show (getSpan span) ++ ": error: \n" ++ msg

makeError :: String -> Span -> String -> String
makeError src span msg   =
  unlines
    [ shortHeader span msg
    , snippetWithCaret src span
  ]



prettyKind :: K.Kind -> String
prettyKind = \case
  K.Proper _ m pk -> prettyMulti m ++ prettyPre pk
  K.Arrow _ k1 k2 -> prettyKind k1 ++ " -> " ++ prettyKind k2
  K.Var _ v -> "kind variable " ++ show v
  where
    prettyMulti = \case
      K.Lin -> "linear"
      K.Un -> "unrestricted"
      K.VarM v -> "multiplicity variable " ++ show v
    prettyPre = \case
      K.Top -> ""
      K.Session -> " session"
      K.Channel -> " channel"
      K.VarPK v -> " prekind variable " ++ show v

errorToMessage :: String -> Error -> String
errorToMessage src = \case

  LexicalError span c ->
    makeError src span
      ("Lexical error: unexpected character " ++ var)
      where var = getFromSpan src span

  ParseError span (tok, expected) ->
    let expectedMsg = case expected of
                        [] -> ""
                        xs -> " Expected one of: " ++ intercalate ", " (map (\t -> "`" ++ t ++ "`") xs) ++ "."
    in makeError src span
         ("Parse error: unexpected token " ++ show tok)

  VarOutOfScope span _ ->
    makeError src span
         ("VarOutOfScope: Variable out of scope: " ++ var)
         where var = getFromSpan src span

  TypeVarOutOfScope span _ ->
     makeError src span
         (" TypeVarOutOfScope: Type variable out of scope: " ++ var)
         where var = getFromSpan src span

  ConsOutOfScope s _ ->
     makeError src s
      ("ConsOutOfScope: Constructor out of scope: " ++ con) 
      where con = getFromSpan src s

  TypeOutOfScope span _ ->
    makeError src span
         ("TypeOutOfScope: Type out of scope: " ++ ty)
      where ty = getFromSpan src span
  -------------------------------------------------------- conflicting defs todo

  MultipleVarDecls span vars ->
      makeError src span
         ("Multiple declarations of variable `" ++ var ++ "`")++
         "Duplicate variable declarations for `" ++ var ++ "` at:\n"++
         unlines (map (\(Variable s ext _) -> "  "++show s) vars)
         where var = getFromSpan src  span

  MultipleFieldDecls span idents ->
     makeError src span
         ("Multiple declarations of field `" ++ field ++ "`")++
         "Duplicate Field declarations for `" ++ field ++ "` at:\n"++
         unlines (map (\(Identifier s _) -> "  "++show s) idents)
         where field = getFromSpan src span

  MultipleConsDecls span idents ->
     makeError src span
         ("Multiple declarations of constructor `" ++ con ++ "`")++
         "Duplicate Cons declarations for `" ++ con ++ "` at:\n"++
         unlines (map (\(Identifier s _) -> "  "++show s) idents)
         where con = getFromSpan src span

  MultipleTypeDecls span idents ->
     makeError src span
         ("Multiple declarations of type `" ++ ty ++ "`")++
         "Duplicate type declarations for `" ++ ty ++ "` at:\n"++
         unlines (map (\(Identifier s _) -> "  "++show s) idents)
         where ty = getFromSpan src span

  MultipleKindSigs span idents ->
     makeError src span
         ("Multiple kind signatures for type `" ++ ty ++ "`")++
         "Duplicate kind signatures for `" ++ ty ++ "` at:\n"++
         unlines (map (\(Identifier s _) -> "  "++show s) idents)
         where ty = getFromSpan src span


  LacksKindSig span ident ->
     makeError src span
         ("Type `" ++ ty ++ "` lacks a kind signature") 
         where ty = getFromSpan src span


  LacksTypeSig span _ ->
     makeError src span
         ("Function `" ++ var ++ "` lacks an accompanying type signature")
         where var = getFromSpan src span


  SigLacksDef span v ->
    makeError src span
      ("Variable `" ++ var ++ "` has a type signature but no definition")
      where var = getFromSpan src span


  GivenTooManyArgs span _ _ expected actual -> 
    makeError src span
      ("The funcion" ++ var ++ " is applied to " ++ show actual ++ " arguments, but its type has only " ++ show expected)
      where var = getFromSpan src span


  ExpectsTooManyArgs span _ _ expected actual ->
    makeError src span
     "Funcion defenicion expects more arguments than it's type"++
     ("The equation for" ++ var ++ " has " ++ show expected ++ "arguments, but its type has" ++ show actual ++ ".")
     where var = getFromSpan src span




  GivenTooManyArgsK span ty expected actual ->
     makeError src span
       ("Type `" ++ typeName ++ "` expects " ++ show expected ++ " argument" ++ (if expected == 1 then "" else "s") ++ ", but it was given " ++ show actual ++ ".")
       where typeName = getFromSpan src span
        


  ExpectsTooManyArgsK span _ expectedKind -> -- mudar , nao falar nos kinds
    makeError src span
       ("Type `" ++ typeName ++ "` expects fewer type arguments") --should have kind `" ++ prettyKind expectedKind ++ "`"
         where typeName        = getFromSpan src span

  KindMismatch span expectedKind ty gotKind ->
     makeError src span
       ("Kind mismatch: expected a `" ++ prettyKind expectedKind ++ "` type for `" ++ typeName ++ "`, but got a `" ++ prettyKind gotKind ++ "` type instead")
       where typeName      = getFromSpan src span


  ProperKindMismatch span ty gotKind ->
     makeError src span
       ("Expected a type `" ++ typeName ++ "`of proper kind, but got kind `" ++ prettyKind gotKind ++ "`")
       where  typeName      = getFromSpan src span


  SessionTypeMismatch span ty kind ->
    makeError src span $
      (\isSession ->
         if isSession --mudar o 1 caso
           then "Session type mismatch: expected a session type, but found `" ++ show ty ++ "` of kind `" ++ prettyKind kind ++ "`"
           else "Session type mismatch: expected a session type, but found non-session type `" ++ show ty ++ "`"
      ) (case kind of
           K.Proper _ _ K.Session -> True
           K.Arrow _ k1 k2        -> True
           _                      -> False)


  TypeMismatch span expected actual _ ->
      makeError src span
        ("Couldn't match expected type `" ++ show expected ++ "` with actual type `" ++ show actual ++ "`")

  IllegalChoice span (Identifier s str) ty ->
    makeError src s
      ("Illegal choice: Selection `" ++ str ++ "` not found in type `" ++ show ty ++ "`")


  LinVarsConsumedInUnFun span xs e ->
    makeError src span
      ("Linear variables `" ++ intercalate "`, `" (map show xs) ++ "` consumed in body of unrestricted function `" ++ show e ++ "`")

  LinVarAtEndOfScope span xi _ ->
    makeError src span
      ("Linear variable " ++ var ++ " was not consumed")
      where var = getFromSpan src span


  InvalidType span t ->
    makeError src span
      ("Invalid type: `" ++ show t ++ "`")

  PartiallyAppliedSelect span (Identifier s str) ->
    makeError src span
      ("Cannot infer type for partially applied select of label `" ++ str ++ "`")

  ConstructorArgumentMismatch span (Identifier s str) n m ->
    makeError src span
      ("Constructor `" ++ str ++ "` expects " ++ show n ++ " arguments, but given " ++ show m)

  NonLinPat span p t ->
    makeError src span
      ("Non-linear pattern `" ++ show p ++ "` for linear type `" ++ show t ++ "`")

 -- ConflictingDefs defs ->
    

  LinVarsCreatedInUnFun span xs e ->
    makeError src span
      ("Linear variables `" ++ intercalate "`, `" (map show xs) ++ "` created in body of unrestricted function `" ++ show e ++ "`")

  ExposeError span s t ->
    makeError src span
      ("Expose error: expecting " ++ s ++ ", but got type `" ++ show t ++ "`")

  UnexpectedArg span (TypeLevel k) (ExpLevel e) n f ->
    makeError src span
      ("Unexpected argument: expected a type of kind `" ++ prettyKind k ++ "`, but got expression `" ++ show e ++ "` in the "
       ++ show n ++ ordinal n ++ " argument")

  UnexpectedArg span (ExpLevel t) (TypeLevel u) n f ->
    makeError src span
      ("Unexpected argument: expected an expression"
       ++ maybe "" (\ty -> " of type `" ++ show ty ++ "`") t
       ++ ", but got type `" ++ show u ++ "` in the "
       ++ show n ++ ordinal n ++ " argument")

  UnexpectedParam span (TypeLevel k) (ExpLevel p) n f ->
    makeError src span
      ("Unexpected parameter: expected a type parameter of kind `" ++ prettyKind k ++ "`, but got pattern `" ++ show p
       ++ "` in the " ++ show n ++ ordinal n ++ " parameter of `" ++ show f ++ "`")

  UnexpectedParam span (ExpLevel t) (TypeLevel a) n f ->
    makeError src span
      ("Unexpected parameter: expected a pattern of type `" ++ show t ++ "`, but got type parameter `" ++ show a
       ++ "` in the " ++ show n ++ ordinal n ++ " parameter of `" ++ show f ++ "`")

  ChannelTypeMismatch span ty k ->
    makeError src span
      ("Channel type mismatch: expected a channel type, but found `" ++ show ty ++ "` of kind `" ++ prettyKind k ++ "`")

  ArrowMultiplicityMismatch span e n m ty m' ->
    makeError src span
      ("Arrow multiplicity mismatch: expected "
        ++ showMult m ++ " function of type `" ++ show ty ++ "`, but got "
        ++ showMult m' ++ " function after the " ++ show n ++ ordinal n
        ++ " parameter of `" ++ show e ++ "`")
    where
      showMult = \case
        K.Lin    -> "a linear"
        K.Un     -> "an unrestricted"
        K.VarM x -> "a multiplicity `" ++ show x ++ "`"

  TypeMismatchSelect span expected (Identifier s str) e ->
    makeError src span
      ("Couldn't match expected type `" ++ show expected
        ++ "` with selection `" ++ str)

  TypeMismatchList span expected _ ->
    makeError src span
      ("Couldn't match expected type `" ++ show expected ++ "` with a list")

  TypeMismatchTuple span n expected _ ->
    makeError src span
      ("Couldn't match expected type `" ++ show expected ++ "` with a "
       ++ case n of
            0 -> "unit ()"
            2 -> "pair"
            k -> show k ++ "-tuple")

 -- TypeCtxMismatch span e ctx1 ctx2 ->
   -- makeError src span
     -- ("Type context mismatch in `" ++ show e ++ "`."
       -- ++ "\n  First context has: " ++ showCtx (ctx1 Map.\\ ctx2)
       -- --++ "\n  Second context has: " ++ showCtx (ctx2 Map.\\ ctx1))
   -- where
    --  showCtx m =
      --  case Map.toList m of
        --  [] -> "nothing"
        --  xs -> intercalate ", " $ [ either show show v ++ " : " ++ show t| (v,t) <- xs ]

  UnsupportedError span msg ->
    makeError src span
      ("Unsupported feature: " ++ msg)

















-- | Convert an error to a readable 'String', which should include its location
-- in the source code in a way that is parseable and by most common IDEs.
-- (Needs some work.)
instance Show Error where
  show e = show (getSpan e) ++ ": error:"++showError e
    where
      showError :: Error -> String
      showError = \case
        LexicalError _ inp ->
          "\n  Lexical error on input `"++show inp++"`"
        ParseError _ (_,ss) ->
          "\n  Parse error, expected: `"++intercalate "`, `" ss++"`"
        VarOutOfScope _ x ->
          "\n  Not in scope: variable `"++show x++"`"
        TypeVarOutOfScope _ x ->
          "\n  Not in scope: type variable `"++show x++"`"
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
        MultipleFieldDecls _ i ->
          "\n  Multiple declarations of field `"++show i++"`"
        MultipleConsDecls _ i ->
          "\n  Multiple declarations of constructor `"++show i++"`"
        MultipleTypeDecls _ i ->
          "\n  Multiple declarations of type `"++show i++"`"
        MultipleKindSigs _ i ->
          "\n  Multiple kind signatures for type `"++show i++"`"
        LacksKindSig _ i ->
          "\n Type `"++show i++"` lacks an accompanying kind signature."
        LacksTypeSig _ x ->
          "\n Function `"++show x++"` lacks an accompanying type signature."
        SigLacksDef _ x ->
          "\n Signature for variable `"++show x++"` lacks an accompanying definition."
        GivenTooManyArgs _ f t expected actual ->
          "\n  Expression `"++show f++"` of type `"++show t++"` takes "++show expected++" arguments, but it was given "++show actual++"."
        ExpectsTooManyArgs _ f t n m->
          "\n  Function `"++show f++"` expects "++show m++" argument"++(if m == 1 then "" else "s")++", but its type `"++show t++"` takes at most "++show n++"."
        LinVarsConsumedInUnFun _ xs e ->
          "\n  Linear variables `" ++ intercalate "`, `" (map show xs) ++ "` consumed in the body of unrestricted function `" ++ show e ++"`"++
          "\n  (This allows duplicating or discarding the variables! Consider using a linear function instead.)"
        LinVarsCreatedInUnFun _ xs e ->
          "\n  Linear variables `" ++ intercalate "`, `" (map show xs) ++ "` consumed in the body of unrestricted function `" ++ show e ++"`"++
          "\n  (This allows duplicating or discarding the variables! Consider using a linear function instead.)"
        ExposeError _ s t ->
          "\n  Expecting "++s++", but got type `"++show t++"`"
        UnexpectedArg _ (TypeLevel k) (ExpLevel e) n f ->
          "\n  Expecting a type argument of kind `"++show k++"`, but got value argument `"++show e++"`"++
          "\n  In the "++ordinal n++" argument of function `"++show f++"`."
        UnexpectedArg _ (ExpLevel  t) (TypeLevel u) n f ->
          "\n  Expecting a value argument "++maybe "" (\t -> "of type `"++show t++"`") t++", but got type argument `"++show u++
          "\n  In the "++ordinal n++" argument of function `"++show f++"`."
        UnexpectedParam _ (TypeLevel k) (ExpLevel p) n f ->
          "\n  Expecting a type parameter of kind `"++show k++"`, but got pattern `"++show p++
          "\n  In the "++ordinal n++" parameter of function `"++show f++"`."
        UnexpectedParam _ (ExpLevel  t) (TypeLevel a) n f ->
          "\n  Expecting a pattern of type `"++show t++"`, but got type parameter `"++show a++"`"++
          "\n  In the "++ordinal n++" parameter of function `"++show f++"`."
        NonLinPat s p t ->
          "\n  Non-linear pattern `"++show p++"` on linear type `"++show t++"`." -- TODO: better error
        KindMismatch s k1 t k2 ->
          "\n  Expected kind `"++show k1++"` for type `"++show t++"`, but got kind `"++show k2++"`."
        ProperKindMismatch s t k ->
          "\n  Expected a proper kind for type `"++show t++"`, but got kind `"++show k++"`."
        SessionTypeMismatch s t k ->
          "\n Expected a session type, but found type `"++show t++"` of kind `"++show k++"`."
        ChannelTypeMismatch s t k ->
          "\n Expected a channel type, but found type `"++show t++"` of kind `"++show k++"`."
        ArrowMultiplicityMismatch s e n m t m' ->
          "\n Expected a"++showMult m++" function of type `"++show t++"`, but got "++showMult m'++" function after the "++ordinal n++" parameter of `"++ show e++"`."
          where showMult = \case K.Lin -> "a linear"; K.Un -> "an unrestricted"; K.VarM x -> "a multiplicity `"++show x++"`"
        GivenTooManyArgsK s t n m ->
          "\n  Type `"++show t++"` expects "++show n++" arguments, but it was given "++show m++"."
        ExpectsTooManyArgsK s i k ->
          "\n  Type "++show i++" expects too many arguments, it should have kind `"++show k++"`."
        InvalidType s t ->
          "\n  Invalid type: `"++show t++"`"
        TypeMismatch s t u ep ->
          "\n  Couldn't match expected type `"++show t++"` with actual type `"++show u++"` in "++showExpPat ep++"."
        TypeMismatchSelect s t i e ->
          "\n  Couldn't match expected type `"++show t++"` with selection of choice `"++show i++"` in expression "++show e++"."
        TypeMismatchList _ t ep ->
          "\n  Couldn't match expected type `"++show t++"` with a list type in "++showExpPat ep++"."
        TypeMismatchTuple _ n t ep ->
          "\n  Couldn't match expected type `"++show t++"` with "++
            (case n of 0 -> "actual type ()"
                       2 -> "a pair type"
                       n -> "a "++show n++"-tuple type.")
          ++" in "++showExpPat ep++"."
        TypeCtxMismatch s e tctx1 tctx2 -> -- TODO: better error message, ideally better than freest 3
          "\n  Couldn't match "++ (case e of E.Case{} -> "the final contexts in two distinct branches in a `case` expression"
                                             E.Abs {} -> "the initial and final contexts in an unrestricted function"
                                             _        -> "contexts in an expression") ++"."++
          "\n  \tWhere the former contains " ++ showCtx (tctx1 Map.\\ tctx2) ++
          "\n  \t      The latter contains " ++ showCtx (tctx2 Map.\\ tctx1) ++
          "\n  \tIn expression `" ++ show e ++"`"++
          "\n  \t(was a variable consumed in one branch and not in the other?)" ++
          "\n  \t(is there a variable with different types in the two contexts?)"
          where showCtx tctx = case Map.foldrWithKey (\cases (Left  x) t ss -> ("`"++show x++" : "++show t++"`") : ss
                                                             (Right c) t ss -> ("`"++show c++" : "++show t++"`") : ss) [] tctx of
                                [] -> "nothing"
                                ss -> intercalate "," ss
        ConstructorArgumentMismatch _ i n m ->
          "\n  The constructor `"++show i++"` should have "++show n++" arguments, but has been given "++show m++"."
        LinVarAtEndOfScope _ xi t ->
          "\n  "++showVarCons xi++", of linear type `"++show t++"`, was not consumed."
          where showVarCons = \case Left x  -> "Variable `"    ++show x++"`"
                                    Right i -> "Constructor `"++show i++"`"
        IllegalChoice s i t ->
          "\n  Choice `"++show i++"` is not allowed by type `"++show t++"`"
        PartiallyAppliedSelect s i ->
          "\n  Cannot synthesize type of partially applied `select` expression."
        UnsupportedError _ m ->
          "\n  " ++ m

      showExpPat = \case
        Left  e -> "expression `"++show e++"`"
        Right p -> "pattern `"++show p++"`"
