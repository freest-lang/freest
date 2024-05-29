{-# LANGUAGE InstanceSigs #-}
module Syntax.Kind
  ( Multiplicity(..)
  , Prekind(..)
  , Kind(..)
  , lt, ut, ls, us, la, ua
  )
where 

import Syntax.Base

data Multiplicity = Lin | Un | VarM Variable

data Prekind = Top | Session | Absorb | VarPK Variable

data Kind = Proper Span Multiplicity Prekind | Arrow Span Kind Kind

-- Abbreviations for the six proper kinds
lt, ut, ls, us, la, ua :: Span -> Kind
lt s = Proper s Lin Top 
ut s = Proper s Un  Top 
ls s = Proper s Lin Session 
us s = Proper s Un  Session
la s = Proper s Lin Absorb
ua s = Proper s Un  Absorb

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