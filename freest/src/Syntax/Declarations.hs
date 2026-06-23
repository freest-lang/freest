{- |
Module      :  Syntax.Declarations
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The declaration environments that make up a module's signature, split along the
boundary that the validator actually consults:

  * 'TypeDecls' — the recursive type equations (type aliases and named µ-types).
    This is the sole module-level input to normalisation and type equivalence,
    which treat a named type as a µ-variable to unfold.

  * 'DataDecls' — the nominal datatype/constructor structure (which constructor
    belongs to which datatype, with what field types; which type variables a
    datatype abstracts over). This is what constructor-pattern checking needs
    and what no other context carries — datatype /kinds/ live in the 'KindCtx',
    so they are deliberately absent here.

These types are phase-parameterised exactly like the rest of a module, so
'Syntax.Module' embeds them rather than duplicating the declaration maps.
-}
module Syntax.Declarations
  ( KindSigs
  , TypeDecls, KindedTypeDecls
  , DataTypeDecls, KindedDataTypeDecls
  , DataConsDecls, KindedDataConsDecls
  , DataDecls(..), KindedDataDecls
  , emptyDataDecls
  )
where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Type.Internal qualified as T

import Data.Map qualified as Map

-- | Phased association data structure. After parsing it is an association
-- list, in subsequent phases it is a map.
type family DeclAssocs p a b where
  DeclAssocs Parsed a b = [(a, b)]
  DeclAssocs p      a b = Map.Map a b

-- | Kind signatures, e.g.
--
--   > type Tree : *T -> *T
--   > type Stream : 1T -> 1S
--
-- are represented as
--
--   > fromList [(Tree, *T -> *T), (Stream, 1T -> 1S)]
type KindSigs p = DeclAssocs p Identifier K.Kind

-- | Type constructor declarations, e.g.
--
--   > type Age = Int
--   > type Stream a = !a ; Stream a
--
-- or, in system Fµω,
--
--   > Age = Int
--   > Stream = λa. µs. !a ; s a
--
-- are represented as
--
--   > fromList [(Age, ([], Int)), (Stream, ([a], (!a ; Stream a))]
type TypeDecls p = DeclAssocs p Identifier (Bool, T.Type p)

type KindedTypeDecls = TypeDecls Kinded

-- | Datatype declarations, e.g.,
--
--   > data Tree a = Leaf | Node (Tree a) a (Tree a)
--
-- or, in system Fµω,
--
--   > Tree = λa. µt. {Leaf, Node (t a) a (t a)}
--
-- are represented as
--
--   > fromList [(Tree, ([a], fromList [Leaf, Node]))]
type DataTypeDecls p =
  DeclAssocs p Identifier ([(Variable, K.Kind)], [Identifier])

type KindedDataTypeDecls = DataTypeDecls Kinded

-- | Datatype constructor declarations, e.g.,
--
--   > data Tree a = Leaf | Node (Tree a) a (Tree a)
--
-- is represented after parsing and scoping as
--
--   > fromList [(Leaf, (Tree, [])), (Node, (Tree [Tree a, a, Tree a]))]
type DataConsDecls p =
  DeclAssocs p Identifier (Identifier, [T.Type p])

type KindedDataConsDecls = DataConsDecls Kinded

-- | Datatype and constructor declarations, bundled.
-- (Consistency must be kept as an invariant)
data DataDecls p = DataDecls
  { ddCons :: DataConsDecls p
  , ddTypes :: DataTypeDecls p
  }

type KindedDataDecls = DataDecls Kinded

-- | The empty data declarations.
emptyDataDecls :: KindedDataDecls
emptyDataDecls = DataDecls Map.empty Map.empty

instance Semigroup KindedDataDecls where
  DataDecls c1 d1 <> DataDecls c2 d2 = DataDecls (c1 `Map.union` c2) (d1 `Map.union` d2)

instance Monoid KindedDataDecls where
  mempty = emptyDataDecls
