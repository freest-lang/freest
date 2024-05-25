{-# LANGUAGE InstanceSigs #-}
module Syntax.Type
  ( Polarity(..)
  , Labelled(..)
  , Type(..)
  )
where

import Syntax.Base
import Syntax.Kind (Kind, Multiplicity(..))

import Data.List (intercalate)

data Polarity = In | Out

data Labelled 
  = Variant
  -- | Record 
  | Choice Multiplicity Polarity

data Type
  -- Constants
  = Int Span
  | Float Span
  | Char Span
  | String Span
  | Arrow Span Multiplicity
  | Message Span Multiplicity Polarity
  | End Span Polarity
  | Skip Span
  | Semi Span
  | Dual Span
  | Forall Span Kind  
  | Rec Span Kind 
  -- Lambda
  | Var Span Variable
  | App Span Type [Type]
  | Abs Span [(Variable, Kind)] Type 
  -- Special cases
  | Name Span Variable 
  | Labelled Span Labelled [(Variable, Type)]
  | Tuple Span [Type]

instance Show Polarity where
  show :: Polarity -> String
  show In  = "?"
  show Out = "!"

instance Show Labelled where
  show :: Labelled -> String
  show Variant = "<>"
  show (Choice Lin In) = "&"
  show (Choice Lin Out) = "+"
  show (Choice Un In) = "*&"
  show (Choice Un Out) = "*+"
  show _ = error "Syntax.Type.show: kind or multiplicity variable in Labelled"

instance Show Type where 
  show :: Type -> String
  show (Int _) = "Int"
  show (Float _) = "Float"
  show (Char _) = "Char"
  show (String _) = "String" 
  show (Arrow _ m) = "("++show m++"->)"
  show (Labelled  _ l lts) = show l++"{"++intercalate "," (map (\(l, t) -> show l ++ ": "++ show t) lts)++"}"
  show (Tuple _ []) = "()"
  show (Tuple _ (t:ts)) = "("++show t++(if null ts then "" else concatMap (\t -> ", "++show t) ts)++")"
  show (Message _ Un p) =  "(*"++ show p++")"
  show (Message _ _ p) = "("++show p++")"
  show (End _ In ) = "Wait" 
  show (End _ Out) = "Close"
  show (Skip _) = "Skip"
  show (Semi _) = "(;)"
  show (Dual _) = "Dual"
  show (Var _ a) = show a
  show (Forall _ k) = "forall_"++show k  
  show (Rec _ k) = "rec_"++show k
  show (App _ t as) = foldl (\s a -> "("++s++" "++show a++")") (show t) as
  show (Abs _ aks t) = "(\\"++concatMap (\(a,k) -> show a++":"++show k) aks++" -> "++show t++")"
  show (Name _ n) = show n

instance Located Type where 
  getSpan :: Type -> Span
  getSpan (Int s) = s
  getSpan (Float s) = s
  getSpan (Char s) = s
  getSpan (String s) = s
  getSpan (Arrow s _) = s
  getSpan (Labelled  s _ _) = s
  getSpan (Tuple s _) = s
  getSpan (Message s _ _) = s
  getSpan (End s _) = s
  getSpan (Skip s) = s
  getSpan (Semi s) = s
  getSpan (Dual s) = s
  getSpan (Var s _) = s
  getSpan (Forall s _) = s
  getSpan (Rec s _) = s
  getSpan (App s _ _) = s
  getSpan (Abs s _ _) = s
  getSpan (Name s _) = s

  setSpan :: Span -> Type -> Type
  setSpan s (Int _) = Int s
  setSpan s (Float _) = Float s
  setSpan s (Char _) = Char s
  setSpan s (String _) = String s
  setSpan s (Arrow _ m) = Arrow s m
  setSpan s (Labelled  _ l lts) = Labelled s l lts
  setSpan s (Tuple _ ts) = Tuple s ts
  setSpan s (Message _ m p) = Message s m p
  setSpan s (End _ p) = End s p
  setSpan s (Skip _) = Skip s
  setSpan s (Semi _) = Semi s
  setSpan s (Dual _) = Dual s
  setSpan s (Var _ a) = Var s a
  setSpan s (Forall _ k) = Forall s k
  setSpan s (Rec _ k) = Rec s k
  setSpan s (App _ t1 t2) = App s t1 t2
  setSpan s (Abs _ aks t) = Abs s aks t
  setSpan s (Name _ n) = Name s n
