{- |
Module      :  Syntax.Kind
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains data types to represent FreeST's higher-order kind system, 
which combines multiplicities (the number of times a resource may be used) with
prekinds (the context in which a resource can be used).
-}
module Syntax.Kind
  ( Multiplicity(..)
  , Prekind(..)
  , Kind(..)
  , lt, ut, ls, us, la, ua, bot
  , Subsort(..)
  , Join(..)
  , lin
  )
where 

import Syntax.Base

class Subsort a where
  (<:) :: a -> a -> Bool

class Join t where
  join :: t -> t -> t

data Multiplicity = Lin | Un | VarM Variable deriving Eq

instance Subsort Multiplicity where
  Lin <: Un = False
  _   <: _  = True

instance Join Multiplicity where
  join Un Un = Un
  join _  _  = Lin

data Prekind = Top | Session | Absorb | VarPK Variable
  deriving Eq

instance Subsort Prekind where
  Top     <: Session = False
  Top     <: Absorb  = False
  Session <: Absorb  = False
  _       <: _       = True

instance Join Prekind where
  join Absorb Absorb   = Absorb
  join Session Session = Session
  join Absorb Session  = Session
  join Session Absorb  = Session  
  join _         _     = Top

data Kind = Proper Span Multiplicity Prekind | Arrow Span Kind Kind

instance Subsort Kind where
  Proper _ m1 pk1 <: Proper _ m2 pk2 = m1 <: m2 && pk1 <: pk2
  Arrow _ k11 k12 <: Arrow _ k21 k22 = k21 <: k11 && k12 <: k22
  _               <: _               = False

instance Join Kind where
  join (Proper s m1 pk1) (Proper _ m2 pk2) = 
    Proper s (join m1 m2) (join pk1 pk2)
  join _ _ = error "(Internal error) join of non-proper kinds."

-- Abbreviations for the six proper kinds
lt, ut, ls, us, la, ua :: Span -> Kind
lt s = Proper s Lin Top 
ut s = Proper s Un  Top 
ls s = Proper s Lin Session 
us s = Proper s Un  Session
la s = Proper s Lin Absorb
ua s = Proper s Un  Absorb
-- Abbreviation for the bottom proper kind
bot :: Span -> Kind
bot = us -- (ua later)

lin :: Kind -> Bool
lin (Proper _ m _) | m <: Lin = True 
lin _ = False

instance Show Multiplicity where
  show Lin = "1"
  show Un  = "*"
  show (VarM φ) = external φ

instance Show Prekind where
  show Top = "T"
  show Session = "S"
  show Absorb = "A"
  show (VarPK ψ) = external ψ

instance Show Kind where
  show (Proper _ m pk) = show m++show pk 
  show (Arrow _ k1 k2) = show k1++" => "++show k2 

instance Located Kind where
  getSpan (Proper s _ _) = s 
  getSpan (Arrow s _ _) = s
  
  setSpan s (Proper _ m pk) = Proper s m pk 
  setSpan s (Arrow _ k1 k2) = Arrow s k1 k2 
