{- |
Module      :  Syntax.Module
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains types and functions to represent and manipulate FreeST 
modules.
-}
module Syntax.Module
  ( Module(..)
  , KindSigs, TypeDecls, DataDecls, ConsDecls
  , setName
  , insertImport
  , insertKindSig
  , insertDataDecl
  , insertTypeDecl
  , insertDef
  , empty
  , ParsedModule, ScopedModule, KindedModule, TypedModule
  )
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Type qualified as T

import Data.List (intercalate)
import Data.Map qualified as Map
import Data.Bifunctor (second)
import Data.Maybe (fromJust)

type ParsedModule = Module Parsed
type ScopedModule = Module Scoped
type KindedModule = Module Kinded
type TypedModule  = Module Typed

data Module phase
  = Module { name        :: Maybe [String]
           , imports     :: [[String]]
           , kindSigs    :: KindSigs  phase
           , typeDecls   :: TypeDecls phase
           , dataDecls   :: DataDecls phase
           , consDecls   :: ConsDecls phase
           , definitions :: [E.LetDecl phase]
           }

-- | Phased association data structure. After parsing it is an association
-- list, in subsequent phases it is a map.
type family ModuleAssoc phase a b where
  ModuleAssoc Parsed a b = [(a, b)]
  ModuleAssoc phase  a b = Map.Map a b

-- | Kind signatures, e.g. 
--
--   > type Tree : *T -> *T  
--   > type Stream : 1T -> 1S   
-- 
-- are represented as
--
--   > fromList [(Tree, *T -> *T), (Stream, 1T -> 1S)]
type KindSigs x = ModuleAssoc x Identifier K.Kind

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
type TypeDecls x = ModuleAssoc x Identifier (T.Type x)

-- | Datatype constructor declarations, e.g.,
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
type DataDecls x = ModuleAssoc x Identifier ([(Variable, K.Kind)], [Identifier])


-- | Datatype constructor declarations, e.g.,
--
--   > data Tree a = Leaf | Node (Tree a) a (Tree a)
--
-- is represented after parsing and scoping as
--
--   > fromList [(Leaf, (Tree, [])), (Node, (Tree [Tree a, a, Tree a]))]
type ConsDecls x = ModuleAssoc x Identifier (Identifier, [T.Type x])

setName :: [String] -> Module x -> Module x
setName n m = m {name = Just n}

insertImport :: [String] -> Module x -> Module x
insertImport i m = m{imports = i : imports m}

insertDataDecl ::  Identifier
               -> [(Variable, K.Kind)]
               -> [(Identifier, [T.Type Parsed])]
               -> Module Parsed
               -> Module Parsed
insertDataDecl i aks cds m =
  m{ dataDecls = dataDecls m ++ [(i, (aks, map fst cds))]
   , consDecls = consDecls m ++ map (second (i,)) cds
   }

insertTypeDecl :: Identifier
               -> [(Variable, K.Kind)]
               -> T.Type Parsed
               -> Module Parsed
               -> Module Parsed
insertTypeDecl i aks t m = m{typeDecls = (i, t') : typeDecls m}
  where t' = if null aks then t else T.Abs (getSpan t) (T.getExt t) aks t

insertKindSig :: [Identifier] -> K.Kind -> Module Parsed -> Module Parsed
insertKindSig is k m = m{kindSigs = map (, k) is ++ kindSigs m}

insertDef :: E.LetDecl Parsed -> Module Parsed -> Module Parsed
insertDef d m = m{definitions = d : definitions m}

empty :: Module Parsed
empty = Module{ name        = Nothing
              , imports     = []
              , kindSigs    = []
              , typeDecls   = []
              , dataDecls   = []
              , consDecls   = []
              , definitions = []
              }

instance Semigroup (Module Parsed) where
  m1 <> m2 =
    Module{ name        = name m2
          , imports     = imports     m1 ++ imports     m2
          , kindSigs    = kindSigs    m1 ++ kindSigs    m2
          , typeDecls   = typeDecls   m1 ++ typeDecls   m2
          , dataDecls   = dataDecls   m1 ++ dataDecls   m2
          , consDecls   = consDecls   m1 ++ consDecls   m2
          , definitions = definitions m1 ++ definitions m2
          }

instance Monoid (Module Parsed) where 
  mempty = empty 

instance Show (Module Parsed) where
  show Module{name,imports,kindSigs,dataDecls,typeDecls,consDecls,definitions} =
    intercalate "\n" $ filter (not . null)
      [case name of Nothing -> "" ; Just n -> "module "++intercalate "." n++" where"
      ,intercalate "\n" (map showImport imports)
      ,intercalate "\n" (map showKindSig kindSigs)
      ,intercalate "\n" (map showTypeDecl typeDecls)
      ,intercalate "\n" (map showDataDecl dataDecls)
      ,intercalate "\n" (map show definitions)
      ]
    where showImport ss = "import "++intercalate "." ss
          showKindSig (i, k) = "type "++show i++" : "++show k
          showDataDecl (i, (aks, is)) =
            "data "++show i++" "++unwords (map show aks)++" = "++intercalate " | " (map ((++ " ...") . show) is)
          showConsDecl (i, (i', aks, ts)) =
            "cons " ++ show i ++ unwords (map (("@" ++) . show) aks) ++ unwords ts
          showTypeDecl (i, T.Abs _ _ aks t) = "type "++show i++" "++unwords (map show aks)++" = "++show t
          showTypeDecl (i, t) = "type "++show i++" = "++show t
