{- |
Module      :  Syntax.Expression
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module defines the Exp data type, which represents expressions in the
external language. Expressions contain patterns and let declarations, which
are also represented by the Pat and LetDecl data types also defined here.
-}
module Syntax.Expression
  ( Pat(..)
  , RHS(..)
  , LetDecl(..)
  , Exp(..)
  )
where

import Syntax.Base
import Syntax.Kind (Multiplicity, Kind)
import Syntax.Type (Type)

import Data.List (intercalate)
import Syntax.Names

data Pat
  = IntPat Span Int
  | FloatPat Span Double
  | CharPat Span Char
  | WildPat Span Variable
  | VarPat Span Variable
  | ConsPat Span Identifier [Pat]
  | AsPat Span Variable Pat

stringPat :: Span -> String -> Pat
stringPat s = \case
  []     -> ConsPat s (mkNil s) []
  (c:cs) -> ConsPat s (mkCons s) [CharPat s c, stringPat s cs]

data LetDecl
  = ValDecl Pat      RHS
  | FnDecl  Variable [([Level Pat Variable], RHS)]
  | SigDecl [Variable] Type

data RHS
  = GuardedRHS [(Exp, Exp)] (Maybe [LetDecl])
  | UnguardedRHS Exp (Maybe [LetDecl])

data Exp
  = Int    Span Int
  | Float  Span Double
  | Char   Span Char
  | Cons   Span Identifier
  | Var    Span Variable
  | App    Span Exp [Level Exp Type]
  | Abs    Span [Level (Pat,Type) (Variable,Kind)] Multiplicity Exp
  | Let    Span [LetDecl] Exp
  | Case   Span Exp [(Pat, RHS)]
  | If     Span Exp Exp Exp
  | Channel Span Type
  | Select Span Identifier Exp

instance Located Pat where
  getSpan = \case
    WildPat s _   -> s
    VarPat s _    -> s
    ConsPat s _ _ -> s
    IntPat s _    -> s
    FloatPat s _  -> s
    CharPat s _   -> s
    AsPat s _ _   -> s

  setSpan s = \case
    WildPat _ x    -> WildPat s x
    VarPat _ x     -> VarPat s x
    ConsPat _ c ps -> ConsPat s c ps
    IntPat _ i     -> IntPat s i
    FloatPat _ f   -> FloatPat s f
    CharPat _ c    -> CharPat s c
    AsPat _ x p    -> AsPat s x p

instance Located LetDecl where 
  getSpan = \case
    ValDecl p rhs -> spanFromTo p rhs
    FnDecl x rhs  -> spanFromTo x (snd $ last rhs)
    SigDecl xs t  -> spanFromTo (head xs) t
  setSpan = error "cannot set span of a LetDecl"

instance Located Exp where
  getSpan = \case
    Int s _      -> s
    Float s _    -> s
    Char s _     -> s
    Cons s _     -> s
    Var s _      -> s
    App s _ _    -> s
    Abs s _ _ _  -> s
    Let s _ _    -> s
    Case s _ _   -> s
    If s _ _ _   -> s
    Channel s _  -> s
    Select s _ _ -> s

  setSpan s = \case
    Int _ i       -> Int s i
    Float _ f     -> Float s f
    Char _ c      -> Char s c
    Cons _ i      -> Cons s i
    Var _ x       -> Var s x
    App _ e as    -> App s e as
    Abs _ ps m e  -> Abs s ps m e
    Let _ ds w    -> Let s ds w
    Case _ e cs   -> Case s e cs
    If _ e1 e2 e3 -> If s e1 e2 e3
    Channel _ t   -> Channel s t
    Select _ i e  -> Select s i e

instance Located RHS where
  getSpan = \case
    GuardedRHS ges w -> 
      spanFromTo (fst $ head ges) 
        (maybe (getSpan $ snd $ last ges) (getSpan . last) w)
    UnguardedRHS e w ->
      spanFromTo e (maybe (getSpan e) (getSpan . last) w)
  setSpan = error "cannot set span of a RHS"

instance Show Pat where
  show = \case
    WildPat _ x    -> show x
    VarPat _ x     -> show x
    ConsPat _ c ps -> "("++show c++" "++unwords (map show ps)++")"
    IntPat _ i     -> show i
    FloatPat _ f   -> show f
    CharPat _ c    -> show c
    AsPat _ x p    -> show x++"&"++show p -- TODO: change to @

instance Show LetDecl where
  show = \case
    ValDecl p rhs   -> show p++show rhs
    FnDecl x psrhss -> intercalate "\n" $ map (\(ps,rhs) -> show x++" "++unwords (map show ps)++show rhs) psrhss
    SigDecl xs t    -> intercalate ", " (map show xs) ++" : "++show t

instance Show RHS where
  show = \case
    GuardedRHS ges w ->
      concatMap (\(g,e) -> " | "++show g++" = "++show e) ges++showWhere w
    UnguardedRHS e w ->
      " = "++show e++showWhere w

showWhere :: Maybe [LetDecl] -> String
showWhere = \case
  Nothing -> ""
  Just ds -> " where ⦃ "++intercalate " ⨾ " (map show ds)++" ⦄"

instance Show Exp where
  show = \case
    Int _ i        -> show i
    Float _ d      -> show d
    Char _ c       -> show c
    Cons _ i       -> show i
    Var _ x        -> show x
    App _ f as     -> foldl (\s a -> "("++s++" "++showArg a++")") (show f) as
                      where showArg (ExpLevel  e) = show e
                            showArg (TypeLevel t) = "@"++show t
    Abs _ ps m e   -> "(\\"++unwords (map showParam ps)++" "++show m++"-> "
                      ++show e++")"
                      where showParam (ExpLevel  (p,t)) = show p++":"++show t
                            showParam (TypeLevel (a,k)) = show a++":"++show k
    Let _ ds e     -> "(let ⦃ "
                      ++intercalate " ⨾ " (map show ds)
                      ++" ⦄ in "++show e++")"
    Case _ e pes   -> "(case "++show e++" of ⦃ "
                      ++intercalate " ⨾ " (map showCase pes)
                      ++" ⦄)"
                      where showCase (p, e) = show p ++ " -> " ++ show e
    If _ e1 e2 e3  -> "(if "++show e1++" then "++show e2++" else "++show e3++")"
    Channel _ t    -> "(channel @"++show t++")"
    Select _ i e   -> "select "++show i++" "++show e
