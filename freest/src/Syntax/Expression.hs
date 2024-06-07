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
  , Arg(..)
  , Exp(..)
  ) 
where

import Syntax.Base
import Syntax.Kind (Multiplicity, Kind)
import Syntax.Type (Type)

import Data.List (intercalate)

data Arg = EArg Exp | TArg Type

data Pat 
  = WildPat Span Variable
  | VarPat Span Variable 
  | ConsPat Span Variable [Pat]
  | TuplePat Span [Pat]
  | IntPat Span Int 
  | FloatPat Span Float 
  | CharPat Span Char 
  | StringPat Span String 
  | AsPat Span Variable Pat

data LetDecl
  = ValDecl Pat      RHS
  | FnDecl  Variable [([Pat], RHS)]
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
  | Var    Span Variable
  | App    Span Exp [Arg]
  | Abs    Span [(Pat, Type)] Multiplicity Exp
  | Let    Span [LetDecl] Exp
  | Case   Span Exp [(Pat, Exp)]
  | If     Span Exp Exp Exp
  | TAbs   Span [(Variable, Kind)] Exp

instance Show Arg where
  show (EArg  e) = show e
  show (TArg t) = show t

instance Located Arg where 
  getSpan (EArg e) = getSpan e
  getSpan (TArg t) = getSpan t
  setSpan s (EArg e) = EArg (setSpan s e)
  setSpan s (TArg t) = TArg (setSpan s t)

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

instance Located Pat where
  getSpan (WildPat s _) = s
  getSpan (VarPat s _) = s 
  getSpan (ConsPat s _ _) = s 
  getSpan (TuplePat s _) = s
  getSpan (IntPat s _) = s 
  getSpan (FloatPat s _) = s
  getSpan (CharPat s _) = s
  getSpan (StringPat s _) = s
  
  setSpan s (WildPat _ x) = WildPat s x
  setSpan s (VarPat _ x) = VarPat s x
  setSpan s (ConsPat _ c ps) = ConsPat s c ps
  setSpan s (TuplePat _ ps) = TuplePat s ps
  setSpan s (IntPat _ i) = IntPat s i
  setSpan s (FloatPat _ f) = FloatPat s f
  setSpan s (CharPat _ c) = CharPat s c
  setSpan s (StringPat _ s') = StringPat s s'

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
  show (Var _ x) = show x  
  show (App _ f as) = foldl (\s a -> "("++s++" "++show a++")") (show f) as
  show (Abs _ ps m e) = "(\\"++unwords (map showPatType ps)++" "++show m++"-> "++show e++")"
    where showPatType (p,t) = "("++show p++":"++show t++")"
  show (Let _ ds e) = "(let ⦃ "++intercalate " ⨾ " (map show ds)++" ⦄ in "++show e++")"
  show (Case _ e pes) = "(case "++show e++" of ⦃ "++intercalate " ⨾ " (map showCase pes)++" ⦄)"
    where showCase (p, e) = show p ++ " -> " ++ show e 
  show (If _ e1 e2 e3) = "(if "++show e1++" then "++show e2++" else "++show e3++")"
  show (TAbs _ aks e) = "(\\\\"++unwords (map (\(a,k)->show a++":"++show k) aks)++" -> "++show e++")"

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
  getSpan (TAbs s _ _) = s
  
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
  setSpan s (TAbs _ as e) = TAbs s as e
