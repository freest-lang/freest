{-# LANGUAGE DataKinds #-}
{- |
Module      :  Syntax.Expression
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module defines the Exp data type, which represents expressions in the
external language. Expressions contain patterns and let declarations, which
are also represented by the Pat and LetDecl data types also defined here.
-}
module Syntax.Expression
  ( Pat( ..
       , NilPat
       , ConsPat
       , TuplePat
       )
  , listPat
  , stringPat
  , RHS(..)
  , LetDecl(..)
  , Exp( ..
       , Tuple
       , Nil
       , Cons
       )
  , listExp
  )
where

import Syntax.Base
import Syntax.Kind ( Multiplicity, Kind )
import Syntax.Names
import Syntax.Type ( Type )

import Data.List ( intercalate )

data Pat x
  = IntPat Span Int
  | FloatPat Span Double
  | CharPat Span Char
  | WildPat Span Variable
  | VarPat Span Variable
  | DConsPat Span Identifier [Pat x]
  | ChoicePat Span Identifier (Pat x)
  | AsPat Span Variable (Pat x)

pattern NilPat :: Span -> (Pat x)
pattern NilPat s <- DConsPat s ((== mkNilId s) -> True) []
  where NilPat s =  DConsPat s (mkNilId s) []

pattern ConsPat :: Span -> (Pat x) -> (Pat x) -> (Pat x)
pattern ConsPat s p1 p2 <- DConsPat s ((== mkConsId s) -> True) [p1,p2]
  where ConsPat s p1 p2 =  DConsPat s (mkConsId s) [p1,p2]

pattern TuplePat :: Span -> [Pat x] -> (Pat x)
pattern TuplePat s ps <- DConsPat s (isTupleId -> True) ps
  where TuplePat s ps =  DConsPat s (mkTupleId (length ps - 1) s) ps

listPat :: Span -> [Pat x] -> (Pat x)
listPat s = \case
  []       -> NilPat s
  (p : ps) -> ConsPat s p (listPat s ps)

stringPat :: Span -> String -> (Pat x)
stringPat s = listPat s . map (CharPat s)

data LetDecl x
  = ValDef (Pat x)      (RHS x)
  | FnDef  Variable [([Level (Pat x) Variable], RHS x)]
  | TypeSig [Variable] (Type x)
  | Mutual [LetDecl x {- FnDef only -}]

data RHS x
  = GuardedRHS [(Exp x, Exp x)] (Maybe [LetDecl x])
  | UnguardedRHS (Exp x) (Maybe [LetDecl x])

data Exp x
  = Int    Span Int
  | Float  Span Double
  | Char   Span Char
  | DCons  Span Identifier
  | Var    Span Variable
  | App    Span (Exp x) [Level (Exp x) (Type x)]
  | Abs    Span [Level (Pat x, Type x) (Variable,Kind)] Multiplicity (Exp x)
  | Let    Span [LetDecl x] (Exp x)
  | Semi   Span (Exp x) (Exp x)
  | Case   Span (Exp x) [(Pat x, RHS x)]
  | If     Span (Exp x) (Exp x) (Exp x)
  | Channel Span (Type x)
  | Select Span Identifier

pattern Tuple :: Span -> [Exp x] -> Exp x
pattern Tuple s es <- (\case e@(App s (DCons _ (isTupleId -> True)) args) -> e
                             e@(DCons s i@(isTupleId -> True)) -> App s e []
                             e -> e
                      -> App s (DCons _ (isTupleId -> True)) (partitionLevels -> (es,_)))
  where Tuple s es =  App s (DCons s (mkTupleId (length es - 1) s)) (map ExpLevel es)

pattern Nil :: Span -> Type x -> Exp x
pattern Nil s t <- App s (DCons _ ((== mkNilId s) -> True)) [TypeLevel t]
  where Nil s t =  App s (DCons s (mkNilId s)) [TypeLevel t]

pattern Cons :: Span -> Exp x -> Exp x -> Exp x 
pattern Cons s e1 e2 <- App s (DCons _ ((== mkConsId s) -> True)) [ExpLevel e1, ExpLevel e2]
  where Cons s e1 e2 =  App s (DCons s (mkConsId s)) (map ExpLevel [e1,e2])

listExp :: Span -> Type x -> [Exp x] -> Exp x
listExp s t = foldr (Cons s) (Nil s t)

instance Located (Pat x) where
  getSpan = \case
    IntPat s _      -> s
    FloatPat s _    -> s
    CharPat s _     -> s
    WildPat s _     -> s
    VarPat s _      -> s
    DConsPat s _ _  -> s
    ChoicePat s _ _ -> s
    AsPat s _ _     -> s

  setSpan s = \case
    IntPat _ i      -> IntPat s i
    FloatPat _ f    -> FloatPat s f
    CharPat _ c     -> CharPat s c
    WildPat _ x     -> WildPat s x
    VarPat _ x      -> VarPat s x
    DConsPat _ c ps -> DConsPat s c ps
    ChoicePat _ l p -> ChoicePat s l p
    AsPat _ x p     -> AsPat s x p

instance Located (LetDecl x) where 
  getSpan = \case
    ValDef p rhs -> spanFromTo p rhs
    FnDef x rhs  -> spanFromTo x (snd $ last rhs)
    TypeSig xs t  -> spanFromTo (head xs) t
  setSpan = error "cannot set span of a LetDecl"

instance Located (Exp x) where
  getSpan = \case
    Int s _      -> s
    Float s _    -> s
    Char s _     -> s
    DCons s _    -> s
    Var s _      -> s
    App s _ _    -> s
    Abs s _ _ _  -> s
    Let s _ _    -> s
    Semi s _ _   -> s
    Case s _ _   -> s
    If s _ _ _   -> s
    Channel s _  -> s
    Select s _ -> s

  setSpan s = \case
    Int _ i       -> Int s i
    Float _ f     -> Float s f
    Char _ c      -> Char s c
    DCons _ i     -> DCons s i
    Var _ x       -> Var s x
    App _ e as    -> App s e as
    Abs _ ps m e  -> Abs s ps m e
    Let _ ds w    -> Let s ds w
    Semi _ e1 e2  -> Semi s e1 e2
    Case _ e cs   -> Case s e cs
    If _ e1 e2 e3 -> If s e1 e2 e3
    Channel _ t   -> Channel s t
    Select _ i -> Select s i

instance Located (RHS x) where
  getSpan = \case
    GuardedRHS ges w -> 
      spanFromTo (fst $ head ges) 
        (maybe (getSpan $ snd $ last ges) (getSpan . last) w)
    UnguardedRHS e w ->
      spanFromTo e (maybe (getSpan e) (getSpan . last) w)
  setSpan = error "cannot set span of a RHS"

instance Show (Pat x) where
  show = \case
    IntPat _ i      -> show i
    FloatPat _ f    -> show f
    CharPat _ c     -> show c
    WildPat _ x     -> show x
    VarPat _ x      -> show x
    DConsPat _ c ps -> "("++show c++" "++unwords (map show ps)++")"
    ChoicePat _ l p -> "(&"++show l++" "++show p++")"
    AsPat _ x p     -> show x++"@"++show p

instance Show (LetDecl x) where
  show = \case
    ValDef p rhs   -> show p++show rhs
    FnDef x psrhss -> 
      intercalate "\n" $ map (\(ps,rhs) -> 
        show x++" "++unwords (map showParam ps)++show rhs) psrhss
      where showParam = \case TypeLevel a -> "@"++show a
                              ExpLevel  p -> show p
    TypeSig xs t    -> intercalate ", " (map show xs) ++" : "++show t
    Mutual ds -> "mutual ⦃\n"++intercalate "⨾\n" (map show ds)++"\n⦄"

instance Show (RHS x) where
  show = \case
    GuardedRHS ges w ->
      concatMap (\(g,e) -> " | "++show g++" = "++show e) ges++showWhere w
    UnguardedRHS e w ->
      " = "++show e++showWhere w

showWhere :: Maybe [LetDecl x] -> String
showWhere = \case
  Nothing -> ""
  Just ds -> " where ⦃ "++intercalate " ⨾ " (map show ds)++" ⦄"

instance Show (Exp x) where
  show = \case
    Int _ i        -> show i
    Float _ d      -> show d
    Char _ c       -> show c
    DCons _ i      -> show i
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
    Semi _ e1 e2   -> "(" ++ show e1 ++ "; " ++ show e2 ++ ")"
    Case _ e pes   -> "(case "++show e++" of ⦃ "
                      ++intercalate " ⨾ " (map showCase pes)
                      ++" ⦄)"
                      where showCase (p, e) = show p ++ " -> " ++ show e
    If _ e1 e2 e3  -> "(if "++show e1++" then "++show e2++" else "++show e3++")"
    Channel _ t    -> "(channel @"++show t++")"
    Select _ i     -> "(select "++show i++")"
