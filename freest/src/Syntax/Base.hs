{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{- |
Module      :  Syntax.Base
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module defines types and classes needed by the other Syntax modules to
represent FreeST's external syntax.
-}
module Syntax.Base where

data Level a b = ExpLevel a | TypeLevel b

instance (Show a, Show b) => Show (Level a b) where
  show (ExpLevel  x) = show x
  show (TypeLevel x) = show x

instance (Located a, Located b) => Located (Level a b) where 
  getSpan (ExpLevel  x) = getSpan x
  getSpan (TypeLevel x) = getSpan x
  setSpan s (ExpLevel x) = ExpLevel (setSpan s x)
  setSpan s (TypeLevel x) = TypeLevel (setSpan s x)

type Pos = (Int, Int)

data Span 
  = Span { filepath   :: FilePath
         , startPos   :: Pos
         , endPos     :: Pos
         } 
  deriving (Eq, Ord)

class Located a where 
  getSpan :: a -> Span 
  setSpan :: Span -> a -> a 

  spanFromTo :: Located b => a -> b -> Span
  spanFromTo l1 l2 = 
    let (s1,s2) = (getSpan l1, getSpan l2)
    in s1{ startPos = min (startPos s1) (startPos s2)
         , endPos = max (endPos s1) (endPos s2)
         }

instance Located Span where 
  getSpan = id 
  setSpan = const 

instance Show Span where 
  show s = filepath s++":"++showPos (startPos s)++"-"++showPos (endPos s)
    where showPos (l,c) = show l++":"++show c

-- For nominal entities, not subject to substitution.
data Identifier = Identifier Span String

instance Located Identifier where
  getSpan (Identifier s _) = s
  setSpan s (Identifier _ i) = Identifier s i

instance Eq Identifier where
  Identifier _ i1 == Identifier _ i2 = i1 == i2

instance Ord Identifier where
  Identifier _ i1 <= Identifier _ i2 = i1 <= i2

instance Show Identifier where
  show (Identifier _ s) = s

data Variable 
  = Variable { varSpan  :: Span
             , external :: String
             , internal :: Int
             }

-- Are these the (only) Ord/Eq instances we want for Variable?
-- (We might want to order them by their position in the source code...)
instance Ord Variable where
  a <= b = internal a <= internal b

instance Eq Variable where 
  a == b = internal a == internal b

instance Show Variable where 
  show (Variable _ extl intl) = extl++"#"++show intl

instance Located Variable where 
  getSpan = varSpan
  setSpan s x = x{varSpan=s}

mkVar :: Located a => String -> a -> Variable
mkVar external l = Variable{varSpan=getSpan l, external, internal= -1}

mkId :: Located a => String -> a -> Identifier
mkId i l = Identifier (getSpan l) i
