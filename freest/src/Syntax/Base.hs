{- |
Module      :  Syntax.Base
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module defines types and classes needed by the other Syntax modules to
represent FreeST's external syntax.
-}

module Syntax.Base
-- TODO: explicit export list!
where

import qualified Data.Set                      as Set

import Data.List ((\\))
import           Data.Bifunctor

-- | Used to separate the syntax of different computational levels 
-- (expressions vs. types).
data Level a b = ExpLevel a | TypeLevel b deriving (Eq, Ord)

instance (Show a, Show b) => Show (Level a b) where
  show (ExpLevel  x) = show x
  show (TypeLevel x) = show x

instance (Located a, Located b) => Located (Level a b) where 
  getSpan (ExpLevel  x) = getSpan x
  getSpan (TypeLevel x) = getSpan x
  setSpan s (ExpLevel x) = ExpLevel (setSpan s x)
  setSpan s (TypeLevel x) = TypeLevel (setSpan s x)

-- | Similar to Either.
instance Bifunctor Level where
  bimap f _ (ExpLevel  e) = ExpLevel  $ f e
  bimap _ g (TypeLevel t) = TypeLevel $ g t

-- | The Level counterpart to @Data.Either.partitionEithers@.
partitionLevels :: [Level a b] -> ([a],[b])
partitionLevels = 
  foldr \case (ExpLevel  e) -> first  (e:) 
              (TypeLevel t) -> second (t:)
        ([],[])

-- | A position in the source code is a pair of line and column numbers.
type Pos = (Int, Int)

-- | A span in the source code is a path to a file, a starting position and an 
-- ending position.
data Span 
  = Span 
    { filepath   :: FilePath
    , startPos   :: Pos
    , endPos     :: Pos
    } 
  deriving (Eq, Ord)

-- | The null span may be used to construct syntactic objects when their 
-- positions in the source code are irrelevant.
nullSpan :: Span
nullSpan = Span "" (0,0) (0,0)

-- | The class of syntactic entities that can be tracked to the source code.
class Located a where 
  -- | Returns the span of its argument.
  getSpan :: a -> Span 
  -- | Replaces the span of the second argument by the first argument.
  setSpan :: Span -> a -> a 
  -- | Synthetises a span from two located arguments. The file path and start
  -- position are extracted from the first argument, while the end position is
  -- extracted from the second argument. 
  spanFromTo :: Located b => a -> b -> Span
  spanFromTo l1 l2 = 
    let (s1,s2) = (getSpan l1, getSpan l2)
    in s1{ startPos = min (startPos s1) (startPos s2)
         , endPos = max (endPos s1) (endPos s2)
         }

-- | For convenience, a span's span is itself.
instance Located Span where 
  getSpan = id 
  setSpan = const 

-- | A span's text representation should be in a format recognized by the 
-- most common IDEs.
instance Show Span where 
  show s = filepath s++":"++showPos (startPos s)++"-"++showPos (endPos s)
    where showPos (l,c) = show l++":"++show c

instance (Located a, Located b) => Located (Either a b) where 
  getSpan (Left x) = getSpan x
  getSpan (Right x) = getSpan x
  setSpan s (Left x) = Left (setSpan s x)
  setSpan s (Right x) = Right (setSpan s x)

-- | Identifiers are used to represent labels, type names and datatype 
-- constructors. Unlike variables, they have no internal representation.
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

-- | Variables are used to represent expression and type variables. Unlike
-- identifiers, they have an internal representation that depends on their
-- scope.
data Variable 
  = Variable 
    { varSpan  :: Span
    , external :: String
    , internal :: Int
    }

instance Ord Variable where
  a <= b = internal a <= internal b

instance Eq Variable where 
  a == b = internal a == internal b

instance Show Variable where 
  show (Variable _ extl intl) = extl++"#"++show intl

instance Located Variable where 
  getSpan = varSpan
  setSpan s x = x{varSpan=s}

-- | Construct an identifier with the span of the second argument.
mkId :: Located a => String -> a -> Identifier
mkId i l = Identifier (getSpan l) i

-- | The first internal available for scoping.
firstInternal :: Int
firstInternal = 1

-- | Reserved for renaming; represents an unreachable variable in a type.
nullInternal :: Int
nullInternal = 0

-- | The default internal. Included in variables created by the parser. Scoping
-- must eliminate all defaults.
defaultInternal :: Int
defaultInternal = -1

-- | Construct a variable given its external representation and a Located value
-- to extract the span from. The internal representation is the default.
mkVar :: Located a => String -> a -> Variable
mkVar external l = Variable{varSpan = getSpan l, external, internal = defaultInternal}

-- | The first variable in a list of internals, and not in a given set of
-- variables.
unusedVar :: [Int] -> Variable -> Set.Set Variable -> Variable
unusedVar stock a as  = a{internal = head (stock \\ map internal (Set.toList as))}

-- | The first variable not in a given set of variables, counting upwards. Used
-- in substitution, for example.
freshVar :: Variable -> Set.Set Variable -> Variable
freshVar = unusedVar [firstInternal..]

-- | The first variable not in a given set of variables, counting downwards. Used
-- in the renaming process, prior to translation to simple grammar.
firstVar :: Variable -> Set.Set Variable -> Variable
firstVar = unusedVar [defaultInternal, defaultInternal - 1 ..]
