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

import           Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import qualified Syntax.Type as T

import           Data.List (intercalate)
import           Data.Maybe (fromMaybe)

-- Datatype constructor declaration list, e.g.,
--   Leaf | Node (Tree a) a (Tree a)
-- represented as
--   [ (Leaf, [])
--   , (Node , [Tree a, a, Tree a])
--   ]
type ConsDeclList = [(Identifier, [T.Type])]
-- Datatype constructor declaration list, e.g.,
--   data Tree a = Leaf | Node (Tree a) a (Tree a)
-- In Fµω:
--   type Tree = λa. µt. {Leaf, Node (t a) a (t a)}
-- represented as
--   [(Tree, ([a], <see above>))]
type DataDeclList = [(Identifier, ([Variable], ConsDeclList))]
-- Type (type) constructor declaration list, e.g.
--   type Stream a = !a ; Stream a
-- In Fµω:
--   type Stream = λa. µs. !a ; s a
-- represented as
--   [(Stream, ([a], (!a ; Stream a))
type TypeDeclList = [(Identifier, ([Variable], T.Type))]
-- Kind signature list, e.g.
--   type Tree : *T -> *T
--   type Stream : 1T -> 1S
-- represented as
--   [(Tree, *T -> *T), (Stream, 1T -> 1S)]
type KindSigList = [([Identifier], K.Kind)]

data Module
  = Module { name        :: Maybe [String]
           , imports     :: [[String]]
           , dataDecls   :: DataDeclList
           , typeDecls   :: TypeDeclList
           , kindSigs    :: KindSigList
           , definitions :: [E.LetDecl]
           }

type Prog = [Module]

-- Typechecking
-- 1. data & type
-- 2. verificar que nomes estao definidos

setName :: [String] -> Module -> Module
setName n m = m {name = Just n}

insertImport :: [String] -> Module -> Module
insertImport i m = m{imports = i : imports m}

insertDataDecl ::  Identifier -> [Variable] -> ConsDeclList -> Module -> Module
insertDataDecl i as b m = m{dataDecls = (i, (as, b)) : dataDecls m}

insertTypeDecl :: Identifier -> [Variable] -> T.Type -> Module -> Module
insertTypeDecl i as t m = m{typeDecls = (i, (as, t)) : typeDecls m}

insertKindSig :: [Identifier] -> K.Kind -> Module -> Module
insertKindSig is k m = m{kindSigs = (is, k) : kindSigs m}

insertDef :: E.LetDecl -> Module -> Module
insertDef d m = m{definitions = d : definitions m}

empty :: Module
empty = Module{ name        = Nothing
              , imports     = []
              , dataDecls   = []
              , typeDecls   = []
              , kindSigs    = []
              , definitions = []
              }

instance Show Module where
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
          showDataDecl (i, (as,cds)) =
            "data "++show i++" "++unwords (map show as)++" = "++intercalate " | " (map showConsDecl cds)
            where showConsDecl (cn,ts) = show cn ++" "++ unwords (map show ts)
          showTypeDecl (i, (as, t)) = "type "++show i++" "++unwords (map show as)++" = "++show t
