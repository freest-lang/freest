{- |
Module      :  Syntax.Type
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module defines the Type data type, which represents FreeST's higher-order
polymorphic context-free session types.
-}
module Syntax.Type
  ( Polarity(..)
  , Type(.., Forall, Exists, AppArrow, AppMessage, AppSemi, AppDual, AppTName, AppDName, AppVar)
  , smartApp
  , variadicQuant
  , Dual(..)
  , isConstant
  , isSkip
  , isSemi
  , isDual
  , isTName
  )
where

import           Syntax.Base
import qualified Syntax.Kind                  as K

import           Data.List (intercalate, sort)
import           Data.Bifunctor
import qualified Data.Map.Strict               as M

data Polarity = In | Out 
  deriving (Eq, Ord)

class Dual a where
  dual :: a -> a

instance Dual Polarity where
  dual Out = In
  dual In = Out

data Type
  -- Functional types
  = Int Span
  | Float Span
  | Char Span
  | Arrow Span K.Multiplicity
  -- Session types
  | Skip Span
  | End Span Polarity
  | Semi Span
  | Message Span K.Multiplicity Polarity
  | Choice Span K.Multiplicity Polarity [(Identifier, Type)]
  | Dual Span
  -- Polymorphism
  | Quant Span Polarity Variable K.Kind Type
  -- Equations
  | TName Span Identifier
  | DName Span Identifier
  -- Higher-order
  | Var Span Variable
  | App Span Type [Type]
  deriving Ord

-- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/pattern_synonyms.html
-- (also, consider OverloadedLists:
-- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/overloaded_lists.html)
pattern Forall :: Span -> Variable -> K.Kind -> Type -> Type
pattern Forall s a k t <- Quant s In a k t
  where Forall s a k t  = Quant s In a k t

pattern Exists :: Span -> Variable -> K.Kind -> Type -> Type
pattern Exists s a k t <- Quant s Out a k t
  where Exists s a k t  = Quant s Out a k t

pattern AppArrow :: Span -> K.Multiplicity -> Type -> Type -> Type
pattern AppArrow s m t u <- App s (Arrow _ m) [t,u]
  where AppArrow s m t u  = App s (Arrow s m) [t,u]

pattern AppMessage :: Span -> K.Multiplicity -> Polarity -> Type -> Type
pattern AppMessage s m p t <- App s (Message _ m p) [t] 
  where AppMessage s m p t  = App s (Message s m p) [t]

pattern AppSemi :: Span -> Type -> Type -> Type
pattern AppSemi s t u <- App s (Semi _) [t,u]
  where AppSemi s t u  = App s (Semi s) [t,u]

pattern AppDual :: Span -> Type -> Type
pattern AppDual s t <- App s (Dual _) [t]
  where AppDual s t  = App s (Dual s) [t]

pattern AppTName :: Span -> Identifier -> [Type] -> Type
pattern AppTName s i ts <- (\case TName s i            -> App s (TName s i) []
                                  App s (TName _ i) ts -> App s (TName s i) ts
                                  t                    -> t
                           -> App s (TName _ i) ts)
  where AppTName _ i [] = TName (getSpan i) i
        AppTName s i ts = App s (TName (getSpan i) i) ts      

pattern AppDName :: Span -> Identifier -> [Type] -> Type
pattern AppDName s i ts <- (\case DName s i            -> App s (DName s i) []
                                  App s (DName _ i) ts -> App s (DName s i) ts
                                  t                    -> t 
                           -> App s (DName _ i) ts)
  where AppDName _ i [] = DName (getSpan i) i
        AppDName s i ts = App s (DName (getSpan i) i) ts

pattern AppVar :: Span -> Variable -> [Type] -> Type
pattern AppVar s a ts <- (\case Var s a            -> App s (Var s a) []
                                App s (Var _ a) ts -> App s (Var s a) ts
                                t                  -> t
                           -> App s (Var _ a) ts)
  where AppVar _ a [] = Var (getSpan a) a
        AppVar s a ts = App s (Var (getSpan a) a) ts 

variadicQuant :: Span -> Polarity -> [(Variable, K.Kind)] -> Type -> Type
variadicQuant _ _ [] t = t
variadicQuant s p ((a,k) : aks) t =
  Quant s p a k $ variadicQuant s p aks t

smartApp :: Span -> Type -> [Type] -> Type
smartApp s (App _ t ts) us = App s t (ts ++ us)
smartApp s t            us = App s t us

isConstant :: Type -> Bool
isConstant Choice{} = False
isConstant Quant{} = False
isConstant TName{} = False
-- isConstant DName{} = False -- Does not reduce
isConstant Var{} = False
isConstant App{} = False
isConstant _ = True

isSkip :: Type -> Bool
isSkip Skip{} = True
isSkip _ = False

isSemi :: Type -> Bool
isSemi Semi{} = True
isSemi _ = False

isDual :: Type -> Bool
isDual Dual{} = True
isDual _ = False

isTName :: Type -> Bool
isTName TName{} = True
isTName _ = False

instance Show Polarity where
  show In  = "?"
  show Out = "!"

instance Show Type where
  show = \case 
    Int{}             -> "Int"
    Float{}           -> "Float"
    Char{}            -> "Char"
    Arrow _ m         -> "("++show m++"->)"
    Message _ K.Un p  ->  "(*"++ show p++")"
    Message _ _ p     -> "("++show p++")"
    Choice  _ m p lts -> showMult m++showView p++"{"++intercalate "," (map (\(l, t) -> show l ++ ": "++ show t) lts)++"}"
      where showMult K.Lin = ""
            showMult K.Un  = "*"
            showView In    = "&"
            showView Out   = "+"
    End _ In          -> "Wait"
    End _ Out         -> "Close"
    Skip{}            -> "Skip"
    Semi{}            -> "(;)"
    Dual{}            -> "Dual"
    Var _ a           -> show a
    Quant _ p a k t   -> "("++showQuant p++" "++show a++":"++show k++". "++show t++")"
      where showQuant In  = "forall"
            showQuant Out = "exists"
    App _ t ts        -> foldl (\s a -> "("++s++" "++show a++")") (show t) ts
    TName _ i         -> show i
    DName _ i         -> show i

class Congruence t where
  congruent :: M.Map Variable Variable -> t -> t -> Bool

instance Eq Type where
  (==) = congruent M.empty
  
instance Congruence Type where
  -- Functional types
  congruent _ Int{} Int{} = True
  congruent _ Float{} Float{} = True
  congruent _ Char{} Char{} = True
  congruent _ (Arrow _ m1) (Arrow _ m2) = m1 == m2
  -- Session types
  congruent _ Skip{} Skip{} = True
  congruent _ (End _ p1) (End _ p2) = p1 == p2
  congruent _ Semi{} Semi{} = True
  congruent m (Message _ m1 p1) (Message _ m2 p2) = m1 == m2 && p1 == p2
  congruent m (Choice _ m1 p1 lts1) (Choice _ m2 p2 lts2) = 
    m1 == m2 && p1 == p2 && congruent m lts1 lts2
  congruent _ Dual{} Dual{} = True
  -- Polymorphism
  congruent m (Quant _ p1 a k1 t) (Quant _ p2 b k2 u) = 
    p1 == p2 && a == b && k1 == k2 && congruent m t u
  -- Equations
  congruent _ (TName _ i1) (TName _ i2) = i1 == i2
  congruent _ (DName _ i1) (DName _ i2) = i1 == i2
  -- Higher-order
  congruent m (Var _ v1) (Var _ v2) =
    v1 == v2 ||              -- free variables
    Just v2 == M.lookup v1 m -- bound variables
  congruent m (App _ t ts) (App _ u us) = congruent m t u && congruent m ts us
  congruent _ _ _ = False

instance Congruence [Type] where
  congruent m ts us =
    length ts == length us &&
    all (uncurry (congruent m)) (zip ts us)

instance Congruence [(Identifier, Type)] where
  congruent m m1 m2 =
    length m1 == length m2 &&
    all (\((id1, t1), (id2, t2)) -> id1 == id2 && congruent m t1 t2) (zip (sort m1) (sort m2))

instance Located Type where
  getSpan (Int s)           = s
  getSpan (Float s)         = s
  getSpan (Char s)          = s
  getSpan (Arrow s _)       = s
  getSpan (Message s _ _)   = s
  getSpan (Choice  s _ _ _) = s
  getSpan (End s _)         = s
  getSpan (Skip s)          = s
  getSpan (Semi s)          = s
  getSpan (Dual s)          = s
  getSpan (Var s _)         = s
  getSpan (Quant s _ _ _ _) = s
  getSpan (App s _ _)       = s
  getSpan (TName s _)       = s
  getSpan (DName s _)       = s

  setSpan s (Int _)             = Int s
  setSpan s (Float _)           = Float s
  setSpan s (Char _)            = Char s
  setSpan s (Arrow _ m)         = Arrow s m
  setSpan s (Message _ m p)     = Message s m p
  setSpan s (Choice  _ m p lts) = Choice s m p lts
  setSpan s (End _ p)           = End s p
  setSpan s (Skip _)            = Skip s
  setSpan s (Semi _)            = Semi s
  setSpan s (Dual _)            = Dual s
  setSpan s (Var _ a)           = Var s a
  setSpan s (Quant _ p a k t)   = Quant s p a k t
  setSpan s (App _ t1 t2)       = App s t1 t2
  setSpan s (TName _ n)         = TName s n
  setSpan s (DName _ n)         = DName s n
