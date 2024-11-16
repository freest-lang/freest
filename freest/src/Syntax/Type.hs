{- |
Module      :  Syntax.Type
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module defines the Type data type, which represents FreeST's higher-order
polymorphic context-free session types.
-}
module Syntax.Type
  ( Polarity(..)
  , Labelled(..)
  , Type(.., AppArrow, AppMessage, AppSemi, AppDual)
  , variadicForall
  , Dual(..)
  , isConstant
  , isName
  )
where

import           Syntax.Base
import qualified Syntax.Kind                  as K

import           Data.List (intercalate, sort)
import           Data.Bifunctor
import qualified Data.List.NonEmpty            as NE
import qualified Data.Map.Strict               as M

data Polarity = In | Out 
  deriving (Eq, Ord)

class Dual a where
  dual :: a -> a

instance Dual Polarity where
  dual Out = In
  dual In = Out

data Labelled -- TODO: use a name, not an adjective. Label?
  = Variant
  | Record 
  | Choice K.Multiplicity Polarity
  deriving (Eq, Ord)

data Type
  -- Functional types
  = Int Span
  | Float Span
  | Char Span
  | Arrow Span K.Multiplicity
  -- Functional or session
  | Labelled Span Labelled [(Identifier, Type)]
  -- Session types
  | Skip Span
  | End Span Polarity
  | Semi Span
  | Message Span K.Multiplicity Polarity
  | Dual Span
  -- Polymorphism
  | Forall Span Variable K.Kind Type
  -- Equations
  | Name Span Identifier
  -- Higher-order
  | Var Span Variable
  | App Span Type (NE.NonEmpty Type)
  deriving Ord

-- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/pattern_synonyms.html
-- (also, consider OverloadedLists:
-- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/overloaded_lists.html)
pattern AppArrow :: Span -> K.Multiplicity -> Type -> Type -> Type
pattern AppArrow s1 m t u <- App s1 (Arrow s2 m) (NE.toList -> [t,u]) where
  AppArrow s m t u = App s (Arrow s m) (NE.fromList [t,u])

pattern AppMessage :: Span -> K.Multiplicity -> Polarity -> Type -> Type
pattern AppMessage s1 m p t <- App s1 (Message s2 m p) (NE.toList -> [t]) where
  AppMessage s m p t = App s (Message s m p) (NE.singleton t)

pattern AppSemi :: Span -> Type -> Type -> Type
pattern AppSemi s t u <- App s (Semi _) (NE.toList -> [t,u]) where
  AppSemi s t u = App s (Semi s) (NE.fromList [t,u])

pattern AppDual :: Span -> Type -> Type
pattern AppDual s t <- App s (Dual _) (NE.toList -> [t]) where
  AppDual s t = App s (Dual s) (NE.singleton t)

variadicForall :: Span -> NE.NonEmpty (Variable, K.Kind) -> Type -> Type
variadicForall s ((a,k) NE.:| []) t = 
  Forall s a k t
variadicForall s ((a,k) NE.:| (NE.fromList -> aks)) t =
  Forall s a k $ variadicForall s aks t

isConstant :: Type -> Bool
isConstant Labelled{} = False
isConstant Forall{} = False
isConstant Name{} = False
isConstant Var{} = False
isConstant App{} = False
isConstant _ = True

isName :: Type -> Bool
isName Name{} = True
isName _ = False

instance Show Polarity where
  show In  = "?"
  show Out = "!"

instance Show Labelled where
  show Record = "×"  -- temporary, just for show
  show Variant = "⊕" -- temporary, just for show
  show (Choice K.Lin In)  = "&"
  show (Choice K.Lin Out) = "+"
  show (Choice K.Un In)   = "*&"
  show (Choice K.Un Out)  = "*+"
  show _ = error "Syntax.Type.show: kind or multiplicity variable in Labelled"

instance Show Type where
  show (Int _)             = "Int"
  show (Float _)           = "Float"
  show (Char _)            = "Char"
  show (Arrow _ m)         = "("++show m++"->)"
  show (Labelled  _ l lts) = show l++"{"++intercalate "," (map (\(l, t) -> show l ++ ": "++ show t) lts)++"}"
  show (Message _ K.Un p)  =  "(*"++ show p++")"
  show (Message _ _ p)     = "("++show p++")"
  show (End _ In )         = "Wait"
  show (End _ Out)         = "Close"
  show (Skip _)            = "Skip"
  show (Semi _)            = "(;)"
  show (Dual _)            = "Dual"
  show (Var _ a)           = show a
  show (Forall _ a k t)    = "(forall "++show a++":"++show k++". "++show t++")"
  show (App _ t as)        = foldl (\s a -> "("++s++" "++show a++")") (show t) as
  show (Name _ n)          = show n

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
  congruent m (Labelled _ l1 m1) (Labelled _ l2 m2) = l1 == l2 && congruent m m1 m2
  -- Session types
  congruent _ Skip{} Skip{} = True
  congruent _ (End _ p1) (End _ p2) = p1 == p2
  congruent m Semi{} Semi{} = True
  congruent _ (Message _ m1 p1) (Message _ m2 p2) = m1 == m2 && p1 == p2
  congruent m Dual{} Dual{} = True
  -- Polymorphism
  congruent m (Forall _ a k1 t) (Forall _ b k2 u) = a == b && k1 == k2 && congruent m t u
  -- Equations
  congruent _ (Name _ id1) (Name _ id2) = id1 == id2
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

instance Congruence (NE.NonEmpty Type) where
  congruent m ts us = congruent m (NE.toList ts) (NE.toList us)

instance Congruence [(Identifier, Type)] where
  congruent m m1 m2 =
    length m1 == length m2 &&
    all (\((id1, t1), (id2, t2)) -> id1 == id2 && congruent m t1 t2) (zip (sort m1) (sort m2))

instance Located Type where
  getSpan (Int s)           = s
  getSpan (Float s)         = s
  getSpan (Char s)          = s
  getSpan (Arrow s _)       = s
  getSpan (Labelled  s _ _) = s
  getSpan (Message s _ _)   = s
  getSpan (End s _)         = s
  getSpan (Skip s)          = s
  getSpan (Semi s)          = s
  getSpan (Dual s)          = s
  getSpan (Var s _)         = s
  getSpan (Forall s _ _ _)  = s
  getSpan (App s _ _)       = s
  getSpan (Name s _)        = s

  setSpan s (Int _)             = Int s
  setSpan s (Float _)           = Float s
  setSpan s (Char _)            = Char s
  setSpan s (Arrow _ m)         = Arrow s m
  setSpan s (Labelled  _ l lts) = Labelled s l lts
  setSpan s (Message _ m p)     = Message s m p
  setSpan s (End _ p)           = End s p
  setSpan s (Skip _)            = Skip s
  setSpan s (Semi _)            = Semi s
  setSpan s (Dual _)            = Dual s
  setSpan s (Var _ a)           = Var s a
  setSpan s (Forall _ a k t)    = Forall s a k t
  setSpan s (App _ t1 t2)       = App s t1 t2
  setSpan s (Name _ n)          = Name s n

