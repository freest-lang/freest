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
  , ParsedExp, ScopedExp, KindedExp
  , ParsedLetDecl, ScopedLetDecl, KindedLetDecl
  , ParsedRHS, ScopedRHS, KindedRHS
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
import Syntax.Type.Internal ( Type )

import Data.List ( intercalate )

type ParsedLetDecl = LetDecl Parsed
type ScopedLetDecl = LetDecl Scoped
type KindedLetDecl = LetDecl Kinded
type ParsedRHS = RHS Parsed
type ScopedRHS = RHS Scoped
type KindedRHS = RHS Kinded

data Pat
  = IntPat Span Int
  | FloatPat Span Double
  | CharPat Span Char
  | WildPat Span Variable
  | VarPat Span Variable
  | PackPat Span [(Variable, Kind)] Pat
  | DConsPat Span Identifier [Pat]
  | WaitPat Span
  | InPat Span Pat Pat
  | ChoicePat Span Identifier Pat
  | TypeInPat Span (Variable, Kind) Pat
  | AsPat Span Variable Pat

instance Eq Pat where
  IntPat _ i1 == IntPat _ i2 = i1 == i2
  FloatPat _ d1 == FloatPat _ d2 = d1 == d2
  CharPat _ c1 == CharPat _ c2 = c1 == c2
  WildPat _ _ == WildPat _ _ = True
  VarPat _ v1 == VarPat _ v2 = v1 == v2
  PackPat _ vars1 pat1 == PackPat _ vars2 pat2 = vars1 == vars2 && pat1 == pat2
  DConsPat _ id1 pat1 == DConsPat _ id2 pat2 = id1 == id2 && pat1 == pat2
  ChoicePat _ id1 pat1 == ChoicePat _ id2 pat2 = id1 == id2 && pat1 == pat2
  AsPat _ var1 pat1 == AsPat _ var2 pat2 = var1 == var2 && pat1 == pat2

pattern NilPat :: Span -> Pat
pattern NilPat s <- DConsPat s ((== mkNilId s) -> True) []
  where NilPat s =  DConsPat s (mkNilId s) []

pattern ConsPat :: Span -> Pat -> Pat -> Pat
pattern ConsPat s p1 p2 <- DConsPat s ((== mkConsId s) -> True) [p1,p2]
  where ConsPat s p1 p2 =  DConsPat s (mkConsId s) [p1,p2]

pattern TuplePat :: Span -> [Pat] -> Pat
pattern TuplePat s ps <- DConsPat s (isTupleId -> True) ps
  where TuplePat s ps =  DConsPat s (mkTupleId (length ps - 1) s) ps

listPat :: Span -> [Pat] -> Pat
listPat s = \case
  []       -> NilPat s
  (p : ps) -> ConsPat s p (listPat s ps)

stringPat :: Span -> String -> Pat
stringPat s = listPat s . map (CharPat s)

data LetDecl x
  = ValDef Pat      (RHS x)
  | FnDef  Variable [([Level Pat Variable], RHS x)]
  | TypeSig [Variable] (Type x)
  | Mutual [LetDecl x {- FnDef only -}]

data RHS x
  = GuardedRHS [(Exp x, Exp x)] (Maybe [LetDecl x])
  | UnguardedRHS (Exp x) (Maybe [LetDecl x])

type ParsedExp = Exp Parsed
type ScopedExp = Exp Scoped
type KindedExp = Exp Kinded

data Exp x
  = Int    Span Int
  | Float  Span Double
  | Char   Span Char
  | DCons  Span Identifier
  | Var    Span Variable
  | App    Span (Exp x) [Level (Exp x) (Type x)]
  | Abs    Span [Level (Pat,Type x) (Variable,Kind)] Multiplicity (Exp x)
  | Pack   Span [Type x] (Exp x)
  | Asc    Span (Exp x) (Type x)
  | Let    Span [LetDecl x] (Exp x)
  | Semi   Span (Exp x) (Exp x)
  | Case   Span (Exp x) [(Pat, RHS x)]
  | If     Span (Exp x) (Exp x) (Exp x)
  | Channel Span (Type x)
  | Select Span Identifier
  | SendType Span (Type x)
  | ReceiveType Span

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

instance Located Pat where
  getSpan = \case
    IntPat s _      -> s
    FloatPat s _    -> s
    CharPat s _     -> s
    WildPat s _     -> s
    VarPat s _      -> s
    PackPat s _ _   -> s
    DConsPat s _ _  -> s
    WaitPat s       -> s
    InPat s _ _     -> s
    ChoicePat s _ _ -> s
    TypeInPat s _ _ -> s
    AsPat s _ _     -> s

  setSpan s = \case
    IntPat _ i      -> IntPat s i
    FloatPat _ f    -> FloatPat s f
    CharPat _ c     -> CharPat s c
    WildPat _ x     -> WildPat s x
    VarPat _ x      -> VarPat s x
    PackPat _ as p  -> PackPat s as p
    DConsPat _ c ps -> DConsPat s c ps
    WaitPat _       -> WaitPat s
    InPat s p1 p2   -> InPat s p1 p2
    ChoicePat _ i p -> ChoicePat s i p
    TypeInPat _ a p -> TypeInPat s a p
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
    Pack s _ _   -> s
    Asc s _ _    -> s
    Let s _ _    -> s
    Semi s _ _   -> s
    Case s _ _   -> s
    If s _ _ _   -> s
    Channel s _  -> s
    Select s _   -> s
    SendType s _ -> s
    ReceiveType s -> s

  setSpan s = \case
    Int _ i       -> Int s i
    Float _ f     -> Float s f
    Char _ c      -> Char s c
    DCons _ i     -> DCons s i
    Var _ x       -> Var s x
    App _ e as    -> App s e as
    Abs _ ps m e  -> Abs s ps m e
    Pack _ ts e   -> Pack s ts e
    Asc _ e t     -> Asc s e t
    Let _ ds w    -> Let s ds w
    Semi _ e1 e2  -> Semi s e1 e2
    Case _ e cs   -> Case s e cs
    If _ e1 e2 e3 -> If s e1 e2 e3
    Channel _ t   -> Channel s t
    Select _ i -> Select s i
    SendType _ t -> SendType s t
    ReceiveType _ -> ReceiveType s

instance Located (RHS x) where
  getSpan = \case
    GuardedRHS ges w ->
      spanFromTo (fst $ head ges)
        (maybe (getSpan $ snd $ last ges) (getSpan . last) w)
    UnguardedRHS e w ->
      spanFromTo e (maybe (getSpan e) (getSpan . last) w)
  setSpan = error "cannot set span of a RHS"

instance Show Pat where
  show = \case
    IntPat _ i      -> show i
    FloatPat _ f    -> show f
    CharPat _ c     -> show c
    WildPat _ x     -> show x
    VarPat _ x      -> show x
    PackPat _ aks p  -> "(" ++intercalate ", " (map (\(a, k) -> "@("++ show a ++ " : " ++ show k ++ ")") aks) ++ ", " ++ show p ++ ")"
    DConsPat _ c ps -> "("++show c++" "++unwords (map show ps)++")"
    WaitPat _       -> "Wait"
    InPat _ p1 p2   -> "(?" ++ show p1 ++ "; " ++ show p2 ++ ")"
    ChoicePat _ l p -> "(&"++show l++" "++show p++")"
    TypeInPat _ (a, k) p -> "(??(" ++ show a ++ " : " ++ show k ++ "). " ++ show p ++ ")"
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
    Pack _ ts e    -> "(" ++ intercalate ", " (map (('@' :) . show) ts) ++ ", " ++ show e ++ ")"
    Asc _ e t      -> "(" ++ show e ++ " : " ++ show t ++ ")"
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
    SendType _ t   -> "(sendType @" ++ show t ++ ")"
    ReceiveType _  -> "receiveType"
