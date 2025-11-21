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
  )
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Type qualified as T

import           Data.List (intercalate)
import           Data.Maybe (fromMaybe)

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
           , dataDecls   :: DataDeclList x
           , typeDecls   :: TypeDeclList x
           , kindSigs    :: KindSigList
           , definitions :: [E.LetDecl x]
           }

type Prog x = [Module x]

-- Typechecking
-- 1. data & type
-- 2. verificar que nomes estao definidos

setName :: [String] -> Module x -> Module x
setName n m = m {name = Just n}

insertImport :: [String] -> Module x -> Module x
insertImport i m = m{imports = i : imports m}

insertDataDecl ::  Identifier -> [(Variable, K.Kind)] -> ConsDeclList x -> Module x -> Module x
insertDataDecl i aks b m = m{dataDecls = (i, aks, b) : dataDecls m}

insertTypeDecl :: Identifier -> [(Variable, K.Kind)] -> T.Type x -> Module x -> Module x
insertTypeDecl i aks t m = m{typeDecls = (i, t') : typeDecls m}
  where t' = if null aks then t else T.Abs (getSpan t) (T.getExt t) aks t 

insertKindSig :: [Identifier] -> K.Kind -> Module x -> Module x
insertKindSig is k m = m{kindSigs = (is, k) : kindSigs m}

insertDef :: E.LetDecl x -> Module x -> Module x
insertDef d m = m{definitions = d : definitions m}

empty :: Module x
empty = Module{ name        = Nothing
              , imports     = []
              , dataDecls   = []
              , typeDecls   = []
              , kindSigs    = []
              , definitions = []
              }

instance Semigroup (Module x) where
  m1 <> m2 =
    Module{ name        = name m2
          , imports     = imports     m1 ++ imports     m2
          , dataDecls   = dataDecls   m1 ++ dataDecls   m2
          , typeDecls   = typeDecls   m1 ++ typeDecls   m2
          , kindSigs    = kindSigs    m1 ++ kindSigs    m2
          , definitions = definitions m1 ++ definitions m2
          }

instance Monoid (Module x) where 
  mempty = empty 

instance Show (Module x) where
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
