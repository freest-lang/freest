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
  , VarLv (..)
  -- Level
  , Level (..)
  , mapLevel
  , voidLevel
  , partitionLevels
  , void
  , Congruence(..)
  )
where


import Compiler.Bug (internalError)

import Data.Bifunctor ( Bifunctor(..) )
import Data.List ( (\\) )
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Void ( Void )

-- | The different phases of annotated ASTs
data Parsed; data Scoped; data Kinded; data Typed

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
  show (Variable _ extl intl) = extl++subscript intl
    where 
      subscript = 
        map (\case '0'->'₀'; '1'->'₁'; '2'->'₂'; '3'->'₃'; '4'->'₄'
                   '5'->'₅'; '6'->'₆'; '7'->'₇'; '8'->'₈'; '9'->'₉'
                   '-' -> '₋') . show
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
mkFreshVar s = unusedVar [firstInternal..] (mkDefaultVar "_γ" s)
  where
    -- | The first variable in a list of internals, and not in a given set of
    -- variables.
    unusedVar :: [Int] -> Variable -> Set.Set Variable -> Variable
    unusedVar stock a as  = a{internal = head (stock \\ map internal (Set.toList as))}
    
-- | The level to which a variable belongs. Used to distinguish between
-- object-level variables and metavariables. The only metavariables for now are
-- instantiation variables, used during local type inference. In the future we
-- may have, e.g., unification variables for more general type inference.
data VarLv 
  = ObjLv -- ^ Object-level variable
  | InstLv -- ^ Instantiation-level variable
  deriving (Eq, Ord, Show)

-- 4 _ Levels

-- | Used to separate the syntax of different computational levels:
-- expression, types and multiplicity.
data Level a b c = ExpLevel a | TypeLevel b | MultLevel c deriving (Eq, Ord)

instance (Show a, Show b, Show c) => Show (Level a b c) where
  show (ExpLevel  x) = show x
  show (TypeLevel x) = show x
  show (MultLevel x) = show x

instance (Located a, Located b, Located c) => Located (Level a b c) where 
  getSpan = \case 
    ExpLevel  x -> getSpan x
    TypeLevel x -> getSpan x
    MultLevel x -> getSpan x
  setSpan s = \case
    ExpLevel  x -> ExpLevel  (setSpan s x)
    TypeLevel x -> TypeLevel (setSpan s x)
    MultLevel x -> MultLevel (setSpan s x)

-- | Similar to Either.
mapLevel :: (a -> a') -> (b -> b') -> (c -> c') -> Level a b c -> Level a' b' c'
mapLevel f _ _ (ExpLevel  e) = ExpLevel  $ f e
mapLevel _ f _ (TypeLevel t) = TypeLevel $ f t
mapLevel _ _ f (MultLevel m) = MultLevel $ f m

voidLevel :: Level a b c -> Level () () ()
voidLevel = \case
  ExpLevel  _ -> ExpLevel  ()
  TypeLevel _ -> TypeLevel ()
  MultLevel _ -> MultLevel ()

-- firstLevel  :: (a -> a') -> Level a b c -> Level a' b  c
-- secondLevel :: (b -> b') -> Level a b c -> Level a  b' c
-- thirdLevel  :: (c -> c') -> Level a b c -> Level a  b  c'
-- firstLevel  f = mapLevel f  id id
-- secondLevel f = mapLevel id f  id
-- thirdLevel    = mapLevel id id

-- | The Level counterpart to @Data.Either.partitionEithers@.
partitionLevels :: [Level a b c] -> ([a], [b], [c])
partitionLevels = 
  foldr \case (ExpLevel  x) -> \(xs, ys, zs) -> (x : xs, ys, zs) 
              (TypeLevel y) -> \(xs, ys, zs) -> (xs, y : ys, zs) 
              (MultLevel z) -> \(xs, ys, zs) -> (xs, ys, z : zs) 
        ([], [], [])

class Congruence t where
  congruent :: Map.Map Variable Variable -> t -> t -> Bool

instance Congruence a => Congruence [a] where
  congruent m ts us =
    length ts == length us &&
    all (uncurry (congruent m)) (zip ts us)