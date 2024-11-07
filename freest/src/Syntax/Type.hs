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
  , Type(.., Arrow', Message')
  , Dual(..)
  , isConstant
  )
where

import Syntax.Base
import qualified Syntax.Kind as K

import Data.List (intercalate)
import Data.Bifunctor

data Polarity = In | Out 
  deriving (Eq, Ord)

class Dual a where
  dual :: a -> a

instance Dual Polarity where
  dual Out = In
  dual In = Out

data Labelled
  = Variant
  | Choice K.Multiplicity Polarity
  deriving (Eq, Ord)

data Type
  -- Functional types
  = Int Span
  | Float Span
  | Char Span
  | String Span -- | Would List Char work?
  | Arrow Span K.Multiplicity
  | Tuple Span [Type]
  -- Functional or session
  | Labelled Span Labelled [(Identifier, Type)]
  -- Session types
  | Skip Span
  | End Span Polarity
  | Semi Span Type Type
  | Message Span K.Multiplicity Polarity
  | Dual Span Type
  -- Polymorphism
  | Forall Span [(Variable, K.Kind)] Type -- | Forall Span Kind; explain why we need the Variable and the Type (why are we not using Abs for the effect)
  -- Equations
  | Name Span Identifier
  -- Higher-order
  | Var Span Variable
  | App Span Type [Type]
  | Abs Span [(Variable, K.Kind)] Type
  -- Hole?
  | Hole Span
  deriving (Eq, Ord)

-- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/pattern_synonyms.html
-- Why not bidirectional?
pattern Arrow' s1 m t u <- App s1 (Arrow s2 m) [t,u] where
  Arrow' s m t u = App s (Arrow s m) [t,u]
pattern Message' s1 m p t <- App s1 (Message s2 m p) [t] where
  Message' s m p t = App s (Message s m p) [t]

isConstant :: Type -> Bool
  -- Functional types
isConstant t@Int{} = True
isConstant t@Float{} = True
isConstant t@Char{} = True
isConstant t@String{} = True
isConstant t@Arrow{} = True
-- isConstant t@Tuple{} = True -- Soon
  -- Session types
isConstant t@Skip{} = True
isConstant t@End{} = True
-- isConstant t@Semi{} = True -- Soon
isConstant t@Message{} = True
-- isConstant t@Dual{} = True -- Soon
isTypeConstant _ = False

instance Show Polarity where
  show In  = "?"
  show Out = "!"

instance Show Labelled where
  show Variant = "<>"
  show (Choice K.Lin In)  = "&"
  show (Choice K.Lin Out) = "+"
  show (Choice K.Un In)   = "*&"
  show (Choice K.Un Out)  = "*+"
  show _ = error "Syntax.Type.show: kind or multiplicity variable in Labelled"

instance Show Type where
  show (Int _)             = "Int"
  show (Float _)           = "Float"
  show (Char _)            = "Char"
  show (String _)          = "String"
  show (Arrow _ m)         = "("++show m++"->)"
  show (Labelled  _ l lts) = show l++"{"++intercalate "," (map (\(l, t) -> show l ++ ": "++ show t) lts)++"}"
  show (Tuple _ [])        = "()"
  show (Tuple _ (t:ts))    = "("++show t++(if null ts then "" else concatMap (\t -> ", "++show t) ts)++")"
  show (Message _ K.Un p)  =  "(*"++ show p++")"
  show (Message _ _ p)     = "("++show p++")"
  show (End _ In )         = "Wait"
  show (End _ Out)         = "Close"
  show (Skip _)            = "Skip"
  show (Semi _ t u)        = "("++show t++ ";" ++show u++")"
  show (Dual _ t)          = "(Dual"++ show t++")"
  show (Var _ a)           = show a
  show (Forall _ aks t)    = "(forall "++concatMap (\(a,k) -> show a++":"++show k++" ") aks++". "++show t++")"
  -- show (Rec _ k)           = "rec_"++show k
  show (App _ t as)        = foldl (\s a -> "("++s++" "++show a++")") (show t) as
  show (Abs _ aks t)       = "(\\"++concatMap (\(a,k) -> show a++":"++show k++" ") aks++"-> "++show t++")"
  show (Name _ n)          = show n
  show (Hole s)            = "_"

instance Located Type where
  getSpan (Int s)           = s
  getSpan (Float s)         = s
  getSpan (Char s)          = s
  getSpan (String s)        = s
  getSpan (Arrow s _)       = s
  getSpan (Labelled  s _ _) = s
  getSpan (Tuple s _)       = s
  getSpan (Message s _ _)   = s
  getSpan (End s _)         = s
  getSpan (Skip s)          = s
  getSpan (Semi s _ _)      = s
  getSpan (Dual s _)        = s
  getSpan (Var s _)         = s
  getSpan (Forall s _ _)    = s
  -- getSpan (Rec s _)         = s
  getSpan (App s _ _)       = s
  getSpan (Abs s _ _)       = s
  getSpan (Name s _)        = s
  getSpan (Hole s)          = s

  setSpan s (Int _)             = Int s
  setSpan s (Float _)           = Float s
  setSpan s (Char _)            = Char s
  setSpan s (String _)          = String s
  setSpan s (Arrow _ m)         = Arrow s m
  setSpan s (Labelled  _ l lts) = Labelled s l lts
  setSpan s (Tuple _ ts)        = Tuple s ts
  setSpan s (Message _ m p)     = Message s m p
  setSpan s (End _ p)           = End s p
  setSpan s (Skip _)            = Skip s
  setSpan s (Semi _ t u)        = Semi s t u
  setSpan s (Dual _ t)          = Dual s t
  setSpan s (Var _ a)           = Var s a
  setSpan s (Forall _ aks t)    = Forall s aks t
  -- setSpan s (Rec _ k)           = Rec s k
  setSpan s (App _ t1 t2)       = App s t1 t2
  setSpan s (Abs _ aks t)       = Abs s aks t
  setSpan s (Name _ n)          = Name s n
  setSpan s (Hole _)            = Hole s

