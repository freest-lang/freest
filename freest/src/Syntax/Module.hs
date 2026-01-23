{-# LANGUAGE NamedFieldPuns #-}
{- |
Module      :  Syntax.Module
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains types and functions to represent and manipulate FreeST 
modules.
-}
module Syntax.Module
  ( ConsDeclList
  , DataDeclList
  , TypeDeclList
  , KindSigList
  , Module(..)
  , setName
  , insertImport
  , insertKindSig
  , insertDataDecl
  , insertTypeDecl
  , insertDef
  , empty
  , ParsedConsDeclList, ParsedDataDeclList, ParsedTypeDeclList
  , KindedConsDeclList, KindedDataDeclList, KindedTypeDeclList
  , TypedConsDeclList, TypedDataDeclList, TypedTypeDeclList
  , ParsedModule, KindedModule, TypedModule
  )
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Type qualified as T

import Data.List (intercalate)
import Data.Map qualified as Map

type ParsedConsDeclList = ConsDeclList Parsed
type KindedConsDeclList = ConsDeclList Kinded
type TypedConsDeclList = ConsDeclList Typed

type ParsedDataDeclList = DataDeclList Parsed
type KindedDataDeclList = DataDeclList Kinded
type TypedDataDeclList = DataDeclList Typed

type ParsedTypeDeclList = TypeDeclList Parsed
type KindedTypeDeclList = TypeDeclList Kinded
type TypedTypeDeclList = TypeDeclList Typed

type ParsedModule = Module Parsed
type KindedModule = Module Kinded
type TypedModule = Module Typed

-- Datatype constructor declaration list, e.g.,
--   Leaf | Node (Tree a) a (Tree a)
-- represented as
--   [ (Leaf, [])
--   , (Node , [Tree a, a, Tree a])
--   ]
type ConsDeclList x = [(Identifier, [T.Type x])]
-- Datatype constructor declaration list, e.g.,
--   data Tree a = Leaf | Node (Tree a) a (Tree a)
-- In Fµω:
--   type Tree = λa. µt. {Leaf, Node (t a) a (t a)}
-- represented as
--   [(Tree, ([a], <see above>))]
type DataDeclList x = [(Identifier, [(Variable, K.Kind)], ConsDeclList x)]
-- Type (type) constructor declaration list, e.g.
--   type Stream a = !a ; Stream a
-- In Fµω:
--   type Stream = λa. µs. !a ; s a
-- represented as
--   [(Stream, ([a], (!a ; Stream a))
type TypeDeclList x = [(Identifier, T.Type x)]
-- Kind signature list, e.g.
--   type Tree : *T -> *T
--   type Stream : 1T -> 1S
-- represented as
--   [(Tree, *T -> *T), (Stream, 1T -> 1S)]
type KindSigList = [([Identifier], K.Kind)]

data Module x
  = Module { name        :: Maybe [String]
           , imports     :: [[String]]
           , dataDecls   :: XDataDecl x
           , typeDecls   :: XTypeDecl x
           , kindSigs    :: KindSigList
           , definitions :: [E.LetDecl x]
           }

type family XDataDecl x
type family XTypeDecl x

type instance XDataDecl Parsed = DataDeclList Parsed
type instance XDataDecl Scoped = Map.Map Identifier ([(Variable, K.Kind)], ConsDeclList Scoped)
type instance XDataDecl Kinded = Map.Map Identifier ([(Variable, K.Kind)], ConsDeclList Kinded)
type instance XDataDecl Typed = Map.Map Identifier ([(Variable, K.Kind)], ConsDeclList (T.Type Typed))

type instance XTypeDecl Parsed = TypeDeclList Parsed
type instance XTypeDecl Scoped = Map.Map Identifier (T.Type Scoped)
type instance XTypeDecl Kinded = Map.Map Identifier (T.Type Kinded)
type instance XTypeDecl Typed = Map.Map Identifier (T.Type Typed)

type Prog x = [Module x]

-- Typechecking
-- 1. data & type
-- 2. verificar que nomes estao definidos

setName :: [String] -> Module x -> Module x
setName n m = m {name = Just n}

insertImport :: [String] -> Module x -> Module x
insertImport i m = m{imports = i : imports m}

insertDataDecl ::  Identifier -> [(Variable, K.Kind)] -> ConsDeclList Parsed -> Module Parsed -> Module Parsed
insertDataDecl i aks b m = m{dataDecls = (i, aks, b) : dataDecls m}

insertTypeDecl :: Identifier -> [(Variable, K.Kind)] -> T.Type Parsed -> Module Parsed -> Module Parsed
insertTypeDecl i aks t m = m{typeDecls = (i, t') : typeDecls m}
  where t' = if null aks then t else T.Abs (getSpan t) (T.getExt t) aks t 

insertKindSig :: [Identifier] -> K.Kind -> Module Parsed -> Module Parsed
insertKindSig is k m = m{kindSigs = (is, k) : kindSigs m}

insertDef :: E.LetDecl Parsed -> Module Parsed -> Module Parsed
insertDef d m = m{definitions = d : definitions m}

empty :: Module Parsed
empty = Module{ name        = Nothing
              , imports     = []
              , dataDecls   = []
              , typeDecls   = []
              , kindSigs    = []
              , definitions = []
              }

instance Semigroup (Module Parsed) where
  m1 <> m2 =
    Module{ name        = name m2
          , imports     = imports     m1 ++ imports     m2
          , dataDecls   = dataDecls   m1 ++ dataDecls   m2
          , typeDecls   = typeDecls   m1 ++ typeDecls   m2
          , kindSigs    = kindSigs    m1 ++ kindSigs    m2
          , definitions = definitions m1 ++ definitions m2
          }

-- instance Monoid (Module x) where 
--   mempty = empty 

instance Show (Module Parsed) where
  show Module{name,imports,kindSigs,dataDecls,typeDecls,definitions} =
    intercalate "\n" $ filter (not . null)
      [case name of Nothing -> "" ; Just n -> "module "++intercalate "." n++" where"
      ,intercalate "\n" (map showImport imports)
      ,intercalate "\n" (map showKindSig kindSigs)
      ,intercalate "\n" (map showTypeDecl typeDecls)
      ,intercalate "\n" (map showDataDecl dataDecls)
      ,intercalate "\n" (map show definitions)
      ]
    where showImport ss = "import "++intercalate "." ss
          showKindSig (is, k) = "type "++intercalate "," (map show is)++" : "++show k
          showDataDecl (i, aks, cds) =
            "data "++show i++" "++unwords (map show aks)++" = "++intercalate " | " (map showConsDecl cds)
            where showConsDecl (cn,ts) = show cn ++" "++ unwords (map show ts)
          showTypeDecl (i, T.Abs _ _ aks t) = "type "++show i++" "++unwords (map show aks)++" = "++show t
          showTypeDecl (i, t) = "type "++show i++" = "++show t
