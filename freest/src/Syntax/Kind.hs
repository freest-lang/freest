{-# LANGUAGE InstanceSigs #-}
module Syntax.Kind
  ( Multiplicity(..)
  , Prekind(..)
  , Kind(..)
  )
where 

import Syntax.Base

data Multiplicity = Lin | Un | VarM Variable

data Prekind = Top | Session | Absorb | VarPK Variable

data Kind = Proper Span Multiplicity Prekind | Arrow Span Kind Kind

instance Show Multiplicity where 
  show :: Multiplicity -> String
  show Lin = "1"
  show Un  = "*"
  show (VarM φ) = external φ

instance Show Prekind where 
  show :: Prekind -> String
  show Top = "T"
  show Session = "S"
  show Absorb = "A"
  show (VarPK ψ) = external ψ

instance Show Kind where 
  show :: Kind -> String
  show (Proper _ m pk) = show m++show pk 
  show (Arrow _ k1 k2) = show k1++" => "++show k2 

instance Located Kind where 
  getSpan :: Kind -> Span
  getSpan (Proper s _ _) = s 
  getSpan (Arrow s _ _) = s

  setSpan :: Span -> Kind -> Kind
  setSpan s (Proper _ m pk) = Proper s m pk 
  setSpan s (Arrow _ k1 k2) = Arrow s k1 k2 