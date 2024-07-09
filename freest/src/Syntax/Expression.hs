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

data Pat 
  = WildPat Span Variable
  | VarPat Span Variable 
  | ConsPat Span Identifier [Pat]
  | TuplePat Span [Pat]
  | IntPat Span Int 
  | FloatPat Span Float 
  | CharPat Span Char 
  | StringPat Span String 
  | AsPat Span Variable Pat

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
  | String Span String
  | Tuple  Span [Exp]
  | Cons   Span Identifier 
  | Var    Span Variable
  | App    Span Exp [Level Exp Type]
  | Abs    Span [Level (Pat,Type) (Variable,Kind)] Multiplicity Exp
  | Let    Span [LetDecl] Exp
  | Case   Span Exp [(Pat, Exp)]
  | If     Span Exp Exp Exp
  | Channel Span Type
  | Select Span Identifier

instance Show Pat where
  show (WildPat _ x) = show x
  show (VarPat _ x) = show x 
  show (ConsPat _ c ps) = "("++show c++" "++unwords (map show ps)++")"
  show (TuplePat _ []) = "()"
  show (TuplePat _ [p]) = error "Syntax.Expression.show: tuple pattern with one element"
  show (TuplePat _ (p:ps)) = "("++show p++unwords (map (\e -> ", "++show e) ps)++")"
  show (IntPat _ i) = show i 
  show (FloatPat _ f) = show f
  show (CharPat _ c) = show c
  show (StringPat _ s) = show s
  show (AsPat _ x p) = show x++"&"++show p -- TODO: change to @

instance Located Pat where
  getSpan (WildPat s _) = s
  getSpan (VarPat s _) = s 
  getSpan (ConsPat s _ _) = s 
  getSpan (TuplePat s _) = s
  getSpan (IntPat s _) = s 
  getSpan (FloatPat s _) = s
  getSpan (CharPat s _) = s
  getSpan (StringPat s _) = s
  getSpan (AsPat s _ _) = s
  
  setSpan s (WildPat _ x) = WildPat s x
  setSpan s (VarPat _ x) = VarPat s x
  setSpan s (ConsPat _ c ps) = ConsPat s c ps
  setSpan s (TuplePat _ ps) = TuplePat s ps
  setSpan s (IntPat _ i) = IntPat s i
  setSpan s (FloatPat _ f) = FloatPat s f
  setSpan s (CharPat _ c) = CharPat s c
  setSpan s (StringPat _ s') = StringPat s s'
  setSpan s (AsPat _ x p) = AsPat s x p

instance Show LetDecl where 
  show (ValDecl p rhs) = show p++show rhs
  show (FnDecl x psrhss) = intercalate "\n" $ map (\(ps,rhs) -> show x++" "++unwords (map show ps)++show rhs) psrhss
  show (SigDecl xs t) = intercalate ", " (map show xs) ++" : "++show t 

instance Show RHS where
  show (GuardedRHS ges w) = 
    concatMap (\(g,e) -> " | "++show g++" = "++show e) ges++showWhere w
  show (UnguardedRHS e w) =
    " = "++show e++showWhere w

showWhere Nothing   = ""
showWhere (Just ds) = " where ⦃ "++intercalate " ⨾ " (map show ds)++" ⦄"

instance Show Exp where
  show (Int _ i) = show i 
  show (Float _ d) = show d
  show (Char _ c) = show c 
  show (String _ s) = show s
  show (Tuple _ []) = "()"
  show (Tuple _ [e]) = error "Syntax.Expression.show: tuple with one element"
  show (Tuple _ (e:es)) = "("++show e++unwords (map (\e -> ", "++show e) es)++")"
  show (Cons _ i) = show i
  show (Var _ x) = show x  
  show (App _ f as) = foldl (\s a -> "("++s++" "++showArg a++")") (show f) as
    where showArg (ExpLevel  e) = show e
          showArg (TypeLevel t) = "@"++show t
  show (Abs _ ps m e) = "(\\"++unwords (map showParam ps)++" "++show m++"-> "++show e++")"
    where showParam (ExpLevel  (p,t)) = show p++":"++show t
          showParam (TypeLevel (a,k)) = show a++":"++show k
  show (Let _ ds e) = "(let ⦃ "++intercalate " ⨾ " (map show ds)++" ⦄ in "++show e++")"
  show (Case _ e pes) = "(case "++show e++" of ⦃ "++intercalate " ⨾ " (map showCase pes)++" ⦄)"
    where showCase (p, e) = show p ++ " -> " ++ show e 
  show (If _ e1 e2 e3) = "(if "++show e1++" then "++show e2++" else "++show e3++")"
  show (Channel _ t) = "(channel @"++show t++")"
  show (Select _ i) = "select "++show i

instance Located Exp where
  getSpan (Int s _) = s
  getSpan (Float s _) = s
  getSpan (Char s _) = s
  getSpan (String s _) = s
  getSpan (Tuple s _) = s
  getSpan (Var s _) = s
  getSpan (App s _ _) = s
  getSpan (Abs s _ _ _) = s
  getSpan (Let s _ _) = s
  getSpan (Case s _ _) = s
  getSpan (If s _ _ _) = s
  getSpan (Channel s _) = s
  getSpan (Select s _) = s
  
  setSpan s (Int _ i) = Int s i
  setSpan s (Float _ f) = Float s f
  setSpan s (Char _ c) = Char s c
  setSpan s (String _ s') = String s s'
  setSpan s (Tuple _ es) = Tuple s es
  setSpan s (Var _ x) = Var s x
  setSpan s (App _ e as) = App s e as
  setSpan s (Abs _ ps m e) = Abs s ps m e
  setSpan s (Let _ ds w) = Let s ds w
  setSpan s (Case _ e cs) = Case s e cs
  setSpan s (If _ e1 e2 e3) = If s e1 e2 e3
  setSpan s (Channel _ t) = Channel s t
  setSpan s (Select _ i) = Select s i
