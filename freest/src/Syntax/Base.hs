{- |
Module      :  Syntax.Base
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module defines types and classes needed by the other Syntax modules to
represent FreeST's external syntax.
-}

module Syntax.Base
  ( Parsed, Scoped, Kinded, Typed 
  -- Span
  , Span (..)
  , nullSpan
  , Located (..)
  -- Identifier
  , Identifier (..)
  , mkId
  -- Variable
  , Variable (..)
  , mkDefaultVar
  , mkFreshVar
  , firstInternal
  , defaultInternal
  -- Level
  , Level (..)
  , partitionLevels
  , void
  )
where


import Data.Bifunctor ( Bifunctor(..) )
import Data.List ( (\\) )
import Data.Set qualified as Set
import Data.Void ( Void )

-- The different phases of annotated AST's

data Parsed
data Scoped
data Kinded
data Typed

void :: Void
void = error "Attempt to evaluate void"

-- 1 _ Positions in the source code

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

instance (Located a, Located b) => Located (Either a b) where 
  getSpan = \case
    Left  x -> getSpan x
    Right x -> getSpan x
  setSpan s = \case
    Left  x -> Left (setSpan s x)
    Right x -> Right (setSpan s x)

-- | For convenience, a span's span is itself.
instance Located Span where 
  getSpan = id 
  setSpan = const 

-- | A span's text representation should be in a format recognized by the 
-- most common IDEs.
instance Show Span where 
  show s = filepath s ++ ":" ++ showPos (startPos s) 
                      ++ "–" ++ showPos (endPos s) -- Not recognized by VS Code. Is there another format for spans?
    where showPos (l,c) = show l++":"++show c

-- | The null span may be used to construct syntactic objects when their 
-- positions in the source code are irrelevant.
nullSpan :: Span
nullSpan = Span "" (0,0) (0,0)

-- 2 _ Identifiers

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
  show (Identifier _ i) = i

-- | Construct an identifier with the span of the second argument.
mkId :: Located a => String -> a -> Identifier
mkId i l = Identifier (getSpan l) i

-- 3 _ Variables

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

-- | The first internal available for scoping.
firstInternal :: Int
firstInternal = 0

-- | The default internal. Included in variables created by the parser. Scoping
-- must eliminate all defaults.
defaultInternal :: Int
defaultInternal = -1

-- | Construct a variable given its external representation and a Located value
-- to extract the span from. The internal representation is the default.
mkDefaultVar :: Located a => String -> a -> Variable
mkDefaultVar external l = Variable{varSpan = getSpan l, external, internal = defaultInternal}

-- | The a variable that does not appear in a set of given variables
mkFreshVar :: Span -> Set.Set Variable -> Variable
mkFreshVar s fvs = unusedVar [firstInternal..] (mkDefaultVar "_γ" s) fvs
  where
    -- | The first variable in a list of internals, and not in a given set of
    -- variables.
    unusedVar :: [Int] -> Variable -> Set.Set Variable -> Variable
    unusedVar stock a as  = a{internal = head (stock \\ map internal (Set.toList as))}
    
-- 4 _ Levels

-- | Used to separate the syntax of different computational levels 
-- (expressions vs. types).
data Level a b = ExpLevel a | TypeLevel b deriving (Eq, Ord)

instance (Show a, Show b) => Show (Level a b) where
  show (ExpLevel  x) = show x
  show (TypeLevel x) = show x

instance (Located a, Located b) => Located (Level a b) where 
  getSpan = \case 
    ExpLevel  x -> getSpan x
    TypeLevel x -> getSpan x
  setSpan s = \case
    ExpLevel  x -> ExpLevel  (setSpan s x)
    TypeLevel x -> TypeLevel (setSpan s x)

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
