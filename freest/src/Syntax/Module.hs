{- |
Module      :  Syntax.Module
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains types and functions to represent and manipulate FreeST 
modules.
-}
module Syntax.Module
  ( ParsedModule, ScopedModule, KindedModule, TypedModule
  , Module(..)
  , KindSigs, TypeDecls, DataDecls, ConsDecls
  , setName
  , insertImport
  , insertKindSig
  , insertDataDecl
  , insertTypeDecl
  , insertDef
  , emptyParsedModule
  , emptyScopedModule
  , emptyKindedModule
  )
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Type.Internal qualified as T
import Syntax.Type.Unkinded qualified as TU

import Data.Bifunctor (second)
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)

type ParsedModule = Module Parsed
type ScopedModule = Module Scoped
type KindedModule = Module Kinded
type TypedModule  = Module Typed

data Module p
  = Module { name        :: Maybe [String] -- TODO: why do we need the Nothing case? Shouldn't all modules have a name? and do I need a List of Strings instead of just a String?
           , imports     :: [[String]]
           , kindSigs    :: KindSigs  p
           , typeDecls   :: TypeDecls p
           , dataDecls   :: DataDecls p
           , consDecls   :: ConsDecls p
           , definitions :: [E.LetDecl p]
           }

-- | Phased association data structure. After parsing it is an association
-- list, in subsequent phases it is a map.
type family ModuleAssoc p a b where
  ModuleAssoc Parsed a b = [(a, b)]
  ModuleAssoc p      a b = Map.Map a b

-- | Kind signatures, e.g. 
--
--   > type Tree : *T -> *T  
--   > type Stream : 1T -> 1S   
-- 
-- are represented as
--
--   > fromList [(Tree, *T -> *T), (Stream, 1T -> 1S)]
type KindSigs p = ModuleAssoc p Identifier K.Kind

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
type TypeDecls p = ModuleAssoc p Identifier (Bool, T.Type p)

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
type DataDecls p = 
  ModuleAssoc p Identifier ([(Variable, K.Kind)], [Identifier])


-- | Datatype constructor declarations, e.g.,
--
--   > data Tree a = Leaf | Node (Tree a) a (Tree a)
--
-- is represented after parsing and scoping as
--
--   > fromList [(Leaf, (Tree, [])), (Node, (Tree [Tree a, a, Tree a]))]
type ConsDecls p = 
  ModuleAssoc p Identifier (Identifier, [T.Type p])

setName :: [String] -> Module p -> Module p
setName n m = m {name = Just n}

insertImport :: [String] -> Module p -> Module p
insertImport i m = m{imports = i : imports m}

insertDataDecl ::  Identifier
               -> [(Variable, K.Kind)]
               -> [(Identifier, [TU.ParsedType])]
               -> ParsedModule
               -> ParsedModule
insertDataDecl i aks cds m = 
  m{ dataDecls = dataDecls m ++ [(i, (aks, map fst cds))]
   , consDecls = consDecls m ++ map (second (i,)) cds
   }

insertTypeDecl :: Identifier
               -> [(Variable, K.Kind)]
               -> TU.ParsedType
               -> ParsedModule
               -> ParsedModule
insertTypeDecl i aks t m = m{typeDecls = (i, (not (null aks), t')) : typeDecls m}
  where t' = if null aks then t else TU.Abs (getSpan t) aks t 

insertKindSig :: [Identifier] -> K.Kind -> ParsedModule -> ParsedModule
insertKindSig is k m = m{kindSigs = kindSigs m ++ map (, k) is}

insertDef :: E.LetDecl p -> Module p -> Module p
insertDef d m = m{definitions = d : definitions m}

emptyParsedModule :: ParsedModule
emptyParsedModule =
  Module{ name        = Nothing
        , imports     = []
        , kindSigs    = []
        , typeDecls   = []
        , dataDecls   = []
        , consDecls   = []
        , definitions = []
        }

emptyScopedModule :: ScopedModule
emptyScopedModule =
  Module{ name        = Nothing
        , imports     = []
        , kindSigs    = Map.empty
        , typeDecls   = Map.empty
        , dataDecls   = Map.empty
        , consDecls   = Map.empty
        , definitions = []
        }

emptyKindedModule :: KindedModule
emptyKindedModule =
  Module{ name        = Nothing
        , imports     = []
        , kindSigs    = Map.empty
        , typeDecls   = Map.empty
        , dataDecls   = Map.empty
        , consDecls   = Map.empty
        , definitions = []
        }

instance Semigroup ParsedModule where
  m1 <> m2 =
    Module{ name        = name m2
          , imports     = imports     m1 ++ imports     m2
          , kindSigs    = kindSigs    m1 ++ kindSigs    m2
          , typeDecls   = typeDecls   m1 ++ typeDecls   m2
          , dataDecls   = dataDecls   m1 ++ dataDecls   m2
          , consDecls   = consDecls   m1 ++ consDecls   m2
          , definitions = definitions m1 ++ definitions m2
          }

instance Monoid ParsedModule where
  mempty = emptyParsedModule

instance Semigroup ScopedModule where
  m1 <> m2 =
    Module{ name        = name m2
          , imports     = imports     m1 ++          imports     m2
          , kindSigs    = kindSigs    m1 `Map.union` kindSigs    m2
          , typeDecls   = typeDecls   m1 `Map.union` typeDecls   m2
          , dataDecls   = dataDecls   m1 `Map.union` dataDecls   m2
          , consDecls   = consDecls   m1 `Map.union` consDecls   m2
          , definitions = definitions m1 ++          definitions m2
          }

instance Monoid ScopedModule where
  mempty = emptyScopedModule

instance Semigroup KindedModule where
  m1 <> m2 =
    Module{ name        = name m2
          , imports     = imports     m1 ++          imports     m2
          , kindSigs    = kindSigs    m1 `Map.union` kindSigs    m2
          , typeDecls   = typeDecls   m1 `Map.union` typeDecls   m2
          , dataDecls   = dataDecls   m1 `Map.union` dataDecls   m2
          , consDecls   = consDecls   m1 `Map.union` consDecls   m2
          , definitions = definitions m1 ++          definitions m2
          }

instance Monoid KindedModule where
  mempty = emptyKindedModule

instance Show ParsedModule where
  show Module{name,imports,kindSigs,dataDecls,typeDecls,definitions} =
    List.intercalate "\n" $ filter (not . null)
      [ case name of 
          Nothing -> ""
          Just n -> "module "++ List.intercalate "." n++" where"
      , List.intercalate "\n" (map showImport imports)
      , List.intercalate "\n" (map showKindSig kindSigs)
      , List.intercalate "\n" (map showTypeDecl typeDecls)
      , List.intercalate "\n" (map showDataDecl dataDecls)
      , List.intercalate "\n" (map show definitions)
      ]
    where 
      showImport ss = "import " ++ List.intercalate "." ss
      showKindSig (i, k) = "type " ++ show i ++ " : " ++ show k
      showDataDecl (i, (aks, is)) =
        "data " ++ show i ++ " " ++ unwords (map show aks) ++ " = " 
        ++ List.intercalate " | " (map ((++ " ...") . show) is)
      showConsDecl (i, (i', aks, ts)) =
        "cons " ++ show i ++ unwords (map (("@" ++) . show) aks) ++ unwords ts
      showTypeDecl (i, (hasParams, T.Abs _ _ aks t)) 
        | hasParams = "type " ++ show i ++ " " ++ unwords (map show aks) ++ " = " ++ show t
        | otherwise = "type " ++ show i ++ " = " ++ show t

instance Show ScopedModule where
  show Module{name,imports,kindSigs,dataDecls,typeDecls,definitions} =
    List.intercalate "\n" $ filter (not . null)
      [ case name of 
          Nothing -> ""
          Just n -> "module "++ List.intercalate "." n++" where"
      , List.intercalate "\n" (map showImport imports)
      , List.intercalate "\n" (map showKindSig (Map.toList kindSigs))
      , List.intercalate "\n" (map showTypeDecl $ Map.toList typeDecls)
      , List.intercalate "\n" (map showDataDecl $ Map.toList dataDecls)
      , List.intercalate "\n" (map show definitions)
      ]
    where 
      showImport ss = "import " ++ List.intercalate "." ss
      showKindSig (i, k) = "type " ++ show i ++ " : " ++ show k
      showDataDecl (i, (aks, is)) =
        "data " ++ show i ++ " " ++ unwords (map show aks) ++ " = " 
        ++ List.intercalate " | " (map ((++ " ...") . show) is)
      showConsDecl (i, (i', aks, ts)) =
        "cons " ++ show i ++ unwords (map (("@" ++) . show) aks) ++ unwords ts
      showTypeDecl = \case 
        (i, (True, T.Abs _ _ aks t)) -> "type " ++ show i ++ " " ++ unwords (map show aks) ++ " = " ++ show t
        (i, (_, t)) -> "type " ++ show i ++ " = " ++ show t

instance Show KindedModule where
  show Module{name,imports,kindSigs,dataDecls,typeDecls,definitions} =
    List.intercalate "\n" $ filter (not . null)
      [ case name of 
          Nothing -> ""
          Just n -> "module "++ List.intercalate "." n++" where"
      , List.intercalate "\n" (map showImport imports)
      , List.intercalate "\n" (map showKindSig (Map.toList kindSigs))
      , List.intercalate "\n" (map showTypeDecl $ Map.toList typeDecls)
      , List.intercalate "\n" (map showDataDecl $ Map.toList dataDecls)
      , List.intercalate "\n" (map show definitions)
      ]
    where 
      showImport ss = "import " ++ List.intercalate "." ss
      showKindSig (i, k) = "type " ++ show i ++ " : " ++ show k
      showDataDecl (i, (aks, is)) =
        "data " ++ show i ++ " " ++ unwords (map show aks) ++ " = " 
        ++ List.intercalate " | " (map ((++ " ...") . show) is)
      showConsDecl (i, (i', aks, ts)) =
        "cons " ++ show i ++ unwords (map (("@" ++) . show) aks) ++ unwords ts
      showTypeDecl = \case 
        (i, (True, T.Abs _ _ aks t)) -> "type " ++ show i ++ " " ++ unwords (map show aks) ++ " = " ++ show t
        (i, (_, t)) -> "type " ++ show i ++ " = " ++ show t