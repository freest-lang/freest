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
  , lt, ut, ls, us, lb, ub, bot
  , Subsort(..)
  , Join(..)
  , Meet(..)
  , isStrictlyLin
  )
where 

import Syntax.Base
import Utils

class Subsort a where
  (<:) :: a -> a -> Bool

class Join t where
  join :: t -> t -> t

class Meet t where
  meet :: t -> t -> t

data Multiplicity = Lin | Un | VarM Variable 
  deriving (Eq, Ord)

instance Subsort Multiplicity where
  Lin <: Un = False
  _   <: _  = True

instance Join Multiplicity where
  join Un Un = Un
  join _  _  = Lin

instance Meet Multiplicity where
  meet Un _  = Un
  meet _  Un = Un
  meet _  _  = Lin

data Prekind = Top | Session | Bounded | VarPK Variable
  deriving (Eq, Ord)

instance Subsort Prekind where
  Top     <: Session = False
  Top     <: Bounded = False
  Session <: Bounded = False
  _       <: _       = True

instance Join Prekind where
  join Bounded Bounded = Bounded
  join Session Session = Session
  join Bounded Session = Session
  join Session Bounded = Session  
  join _       _       = Top


instance Meet Prekind where
  meet Bounded _       = Bounded
  meet _       Bounded = Bounded
  meet Session _       = Session
  meet _       Session = Session
  meet _       _       = Top

instance Meet Kind where
  meet (Proper s m1 b1) (Proper _ m2 b2) = Proper s (meet m1 m2) (meet b1 b2)

data Kind = Proper Span Multiplicity Prekind | Arrow Span Kind Kind            
  deriving (Ord)

instance Eq Kind where
  (Proper _ m1 pk1) == (Proper _ m2 pk2) = m1 == m2 && pk1 == pk2
  (Arrow _ k11 k12) == (Arrow _ k21 k22) = k11 == k21 && k12 == k22

instance Subsort Kind where
  Proper _ m1 pk1 <: Proper _ m2 pk2 = m1 <: m2 && pk1 <: pk2
  Arrow _ k11 k12 <: Arrow _ k21 k22 = k21 <: k11 && k12 <: k22
  _               <: _               = False

instance Join Kind where
  join (Proper s m1 pk1) (Proper _ m2 pk2) = 
    Proper s (join m1 m2) (join pk1 pk2)
  join _ _ = internalError "join of non-proper kinds."

-- | Abbreviations for the six proper kinds
lt, ut, ls, us, lb, ub :: Span -> Kind
lt s = Proper s Lin Top 
ut s = Proper s Un  Top 
ls s = Proper s Lin Session 
us s = Proper s Un  Session
lb s = Proper s Lin Bounded
ub s = Proper s Un  Bounded

-- | Abbreviation for the bottom proper kind
bot :: Span -> Kind
bot = us -- (ua later)

isStrictlyLin :: Kind -> Bool
isStrictlyLin (Proper _ Lin _) = True 
isStrictlyLin _ = False

instance Show Multiplicity where
  show = \case 
    Lin    -> "1"
    Un     -> "*"
    VarM φ -> external φ

instance Show Prekind where
  show = \case 
    Top     -> "T"
    Session -> "S"
    Bounded -> "A"
    VarPK ψ -> external ψ

-- TODO: unparse me!
instance Show Kind where
  show = \case 
    Proper _ m pk -> show m++show pk 
    Arrow _ k1 k2 -> "(" ++ show k1 ++ " -> " ++ show k2 ++ ")"

instance Located Kind where
  getSpan = \case 
    Proper s _ _ -> s 
    Arrow s _ _  -> s
  
  setSpan s = \case
    Proper _ m pk -> Proper s m pk 
    Arrow _ k1 k2 -> Arrow s k1 k2 
