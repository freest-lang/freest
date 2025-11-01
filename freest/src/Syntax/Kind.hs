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
  , lt, ut, ls, us, lc, uc, bot
  , Subsort(..)
  , Join(..)
  , Meet(..)
  , isStrictlyLin
  , isStrictlySession
  , isStrictlyChannel
  , image
  , depth
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
  Un <: Lin = True
  m1 <: m2  = m1 == m2

instance Join Multiplicity where
  join φ@VarM{} _  = internalError ("join of multiplicity variable "++show φ)
  join _ φ@VarM{}  = internalError ("join of multiplicity variable "++show φ)
  join Un Un = Un
  join _  _  = Lin

instance Meet Multiplicity where
  meet φ@VarM{} _  = internalError ("meet of multiplicity variable "++show φ)
  meet _ φ@VarM{}  = internalError ("meet of multiplicity variable "++show φ)
  meet Un _  = Un
  meet _  Un = Un
  meet _  _  = Lin

data Prekind = Top | Session | Channel | VarPK Variable
  deriving (Eq, Ord)

instance Subsort Prekind where
  Session <: Top     = True
  Channel <: Top     = True
  Channel <: Session = True
  pk1     <: pk2     = pk1 == pk2

instance Join Prekind where  
  join ψ@VarPK{} _  = internalError ("join of prekind variable "++show ψ)
  join _ ψ@VarPK{}  = internalError ("join of prekind variable "++show ψ)
  join Channel Channel = Channel
  join Session Session = Session
  join Channel Session = Session
  join Session Channel = Session  
  join _       _       = Top


instance Meet Prekind where
  meet ψ@VarPK{} _  = internalError ("meet of prekind variable "++show ψ)
  meet _ ψ@VarPK{}  = internalError ("meet of prekind variable "++show ψ)
  meet Channel _       = Channel
  meet _       Channel = Channel
  meet Session _       = Session
  meet _       Session = Session
  meet _       _       = Top

data Kind 
  = Proper Span Multiplicity Prekind 
  | Arrow Span Kind Kind 
  | Var Span Variable       
  deriving (Ord)

instance Eq Kind where
  Proper _ m1 pk1 == Proper _ m2 pk2 = m1 == m2 && pk1 == pk2
  Arrow _ k11 k12 == Arrow _ k21 k22 = k11 == k21 && k12 == k22
  Var _ τ1        == Var _ τ2        = τ1 == τ2 

instance Meet Kind where
  meet (Proper s m1 b1) (Proper _ m2 b2) = 
    Proper s (meet m1 m2) (meet b1 b2)
  meet _ _ = internalError "meet of non-proper kinds."

instance Join Kind where
  join (Proper s m1 pk1) (Proper _ m2 pk2) = 
    Proper s (join m1 m2) (join pk1 pk2)
  join _ _ = internalError "join of non-proper kinds."

instance Subsort Kind where
  Proper _ m1 pk1 <: Proper _ m2 pk2 = m1 <: m2 && pk1 <: pk2
  Arrow _ k11 k12 <: Arrow _ k21 k22 = k21 <: k11 && k12 <: k22
  Var _ τ1        <: Var _ τ2        = τ1 == τ2
  _               <: _               = False

-- for debugging
instance Show Kind where
  show = \case 
    Proper _ m1 pk -> show m1 ++ show pk
    Arrow  _ k1 k2 -> "(" ++ show k1 ++ "->" ++ show k2 ++ ")"
    Var    _ τ     -> show τ

-- | Abbreviations for the six proper kinds
lt, ut, ls, us, lc, uc :: Span -> Kind
lt s = Proper s Lin Top 
ut s = Proper s Un  Top 
ls s = Proper s Lin Session 
us s = Proper s Un  Session
lc s = Proper s Lin Channel
uc s = Proper s Un  Channel

-- | Abbreviation for the bottom proper kind
bot :: Span -> Kind
bot = us -- (ua later)

isStrictlyLin, isStrictlyChannel, isStrictlySession :: Kind -> Bool

isStrictlyLin (Proper _ Lin _) = True 
isStrictlyLin _ = False

isStrictlyChannel (Proper _ _ Channel) = True
isStrictlyChannel _ = False

isStrictlySession (Proper _ _ Session) = True
isStrictlySession _ = False

instance Show Multiplicity where
  show = \case 
    Lin    -> "1"
    Un     -> "*"
    VarM φ -> external φ

instance Show Prekind where
  show = \case 
    Top     -> "T"
    Session -> "S"
    Channel -> "C"
    VarPK ψ -> external ψ

instance Located Kind where
  getSpan = \case 
    Proper s _ _ -> s 
    Arrow s _ _  -> s
  
  setSpan s = \case
    Proper _ m pk -> Proper s m pk 
    Arrow _ k1 k2 -> Arrow s k1 k2 

image :: Kind -> Kind
image = \case
  k@Proper{} -> k
  Arrow _ _ k -> image k

depth :: Kind -> Int
depth = \case
  k@Proper{} -> 0
  Arrow _ _ k -> 1 + depth k
