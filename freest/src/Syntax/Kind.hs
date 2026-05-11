{- |
Module      :  Syntax.Kind
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains data types to represent FreeST's higher-order kind system, 
which combines multiplicities (the number of times a resource may be used) with
prekinds (the context in which a resource can be used).
-}
module Syntax.Kind
  ( Multiplicity(.., Un, VarM)
  , isLin
  , Prekind(..)
  , Kind(..)
  , lt, ut, ls, us, lc, uc
  , Subsort(..)
  , Join(..)
  , Meet(..)
  , isSession
  , isChannel
  , isProper
  , image
  , depth
  )
where 

import Syntax.Base
import Utils

import Data.List qualified as List
import Data.Map qualified as Map
import Data.Set qualified as Set

class Subsort a where
  (<:) :: a -> a -> Bool

class Join t where
  join :: t -> t -> t

class Meet t where
  meet :: t -> t -> t

data Multiplicity = Lin Span | Sup Span [(VarLv, Variable)]

pattern Un :: Span -> Multiplicity
pattern Un s <- Sup s []
  where Un s = Sup s []

pattern VarM :: Span -> VarLv -> Variable -> Multiplicity
pattern VarM s lv φ <- Sup s [(lv, φ)]
  where VarM s lv φ =  Sup s [(lv, φ)]

isLin :: Multiplicity -> Bool
isLin = \case Lin _ -> True; _ -> False

instance Eq Multiplicity where
  (==) = congruent Map.empty

instance Ord Multiplicity where
  compare = \cases
    Lin{} Lin{} -> EQ
    (Sup _ lvφs1) (Sup _ lvφs2) -> compare lvφs1 lvφs2
    m1 m2 -> compare (rank m1) (rank m2)
    where 
      rank = \case 
        Lin{} -> 1
        Un{} -> 2
        Sup{} -> 3   

instance Located Multiplicity where
  getSpan = \case
    Lin s   -> s
    Sup s _ -> s
  
  setSpan = \cases
    s (Lin _)      -> Lin s
    s (Sup _ lvφs) -> Sup s lvφs

instance Congruence Multiplicity where
  congruent m = \cases
    Lin{} Lin{} -> True
    (Sup _ lvφs1) (Sup _ lvφs2) -> 
      length lvφs1 == length lvφs2 && and (zipWith congruentLvφs lvφs1 lvφs2)
      where 
        congruentLvφs (lv1, φ1) (lv2, φ2) = 
          lv1 == lv2 && (φ1 == φ2 || Just φ2 == m Map.!? φ1)
    _ _ -> False

instance Subsort Multiplicity where
  Un{} <: _     = True
  _    <: Lin{} = True
  m1   <: m2    = m1 == m2
instance Join Multiplicity where
  join = \cases
    (Lin s)         m           -> Lin s
    m             Lin{}         -> Lin (getSpan m)
    (Sup s lvφs1) (Sup _ lvφs2) -> Sup s (lvφs1 `List.union` lvφs2)

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

instance Eq Kind where
  (==) = \cases
    (Proper _ m1 pk1) (Proper _ m2 pk2) -> m1 == m2 && pk1 == pk2
    (Arrow _ k11 k12) (Arrow _ k21 k22) -> k11 == k21 && k12 == k22
    (Var _ τ1)        (Var _ τ2)        -> τ1 == τ2 
    _                 _                 -> False

instance Ord Kind where
  compare = \cases 
    (Proper _ m1 pk1) (Proper _ m2 pk2) -> compare (m1, pk1)  (m2, pk2)
    (Arrow _ k11 k12) (Arrow _ k21 k22) -> compare (k11, k12) (k21, k22)
    (Var _ τ1)        (Var _ τ2)        -> compare τ1         τ2
    k1                k2                -> compare (rank k1)  (rank k2)
    where rank = \case 
            Proper{} -> 0
            Arrow{}  -> 1
            Var{}    -> 2

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
    Proper _ m1 pk -> show m1 ++ " " ++ show pk
    Arrow  _ k1 k2 -> "(" ++ show k1 ++ "->" ++ show k2 ++ ")"
    Var    _ τ     -> show τ

-- | Abbreviations for the six proper kinds
lt, ut, ls, us, lc, uc :: Span -> Kind
lt s = Proper s (Lin s) Top 
ut s = Proper s (Un s)  Top 
ls s = Proper s (Lin s) Session 
us s = Proper s (Un s)  Session
lc s = Proper s (Lin s) Channel
uc s = Proper s (Un s)  Channel

isChannel, isSession, isProper :: Kind -> Bool

isChannel (Proper _ _ Channel) = True
isChannel _ = False

isSession (Proper _ _ pk) = pk <: Session
isSession _ = False

isProper = \case
  Proper{} -> True
  _        -> False

-- Could be snd . Expose.kindArrow, was it not for a circularity the graph of modules
image :: Kind -> Kind
image = \case
  k@Proper{} -> k
  Arrow _ _ k -> image k
  k -> internalError ("image of kind " ++ show k)

depth :: Kind -> Int
depth = \case
  k@Proper{} -> 0
  Arrow _ _ k -> 1 + depth k
  k -> internalError ("depth of kind " ++ show k)

instance Show Multiplicity where
  show = \case 
    Lin{}      -> "1"
    Un{}       -> "*"
    Sup _ lvφs -> List.intercalate "+" (map (show . snd) lvφs)

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
