{-# LANGUAGE NamedFieldPuns #-}
{- |
Module      :  Syntax.Module
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains types and functions to represent and manipulate FreeST 
modules.
-}
module Syntax.Module
  ( DataDeclList
  , ConsDeclList
  , TypeDeclList
  , Module(..)
  , setName
  , insertImport
  , insertDataDecl
  , insertTypeDecl
  , insertDef
  , empty
  )
where

import           Syntax.Base
import           Syntax.Expression (Exp, Pat, LetDecl)
import           Syntax.Kind (Kind)
import           Syntax.Type (Type)

import           Data.List (intercalate)
import           Data.Maybe (fromMaybe)
import           Debug.Trace (trace)

type ConsDeclList = [(Identifier, [Type])]
type DataDeclList = [(Identifier, [(Variable, Kind)], ConsDeclList)]
type TypeDeclList = [(Identifier, [(Variable, Kind)], Type)]

data Module
  = Module { name        :: Maybe [String]
           , imports     :: [[String]]
           , dataDecls   :: DataDeclList
           , typeDecls   :: TypeDeclList
           , definitions :: [LetDecl]
           }

type Prog = [Module]

-- Typechecking
-- 1. data & type
-- 2. verificar que nomes estao definidos

setName :: [String] -> Module -> Module
setName n m = m {name = Just n}

insertImport :: [String] -> Module -> Module
insertImport i m = m{imports = i : imports m}

insertDataDecl ::  Identifier -> [(Variable, Kind)] -> ConsDeclList -> Module -> Module
insertDataDecl n aks b m = m{dataDecls = (n, aks, b) : dataDecls m}

insertTypeDecl :: Identifier -> [(Variable, Kind)] -> Type -> Module -> Module
insertTypeDecl n aks t m = m{typeDecls = (n, aks, t) : typeDecls m}

insertDef :: LetDecl -> Module -> Module
insertDef d m = m{definitions = d : definitions m}

empty :: Module
empty = Module{ name        = Nothing
              , imports     = []
              , dataDecls   = []
              , typeDecls   = []
              , definitions = []
              }

instance Show Module where
  show Module{name,imports,dataDecls,typeDecls,definitions} =
    intercalate "\n"
      [case name of Nothing -> "\n" ; Just n -> "\nmodule "++intercalate "." n++" where"
      ,"-- imports"
      ,intercalate "\n" (map showImport imports)
      ,"-- type declarations"
      ,intercalate "\n" (map showTypeDecl typeDecls)
      ,"-- data declarations"
      ,intercalate "\n" (map showDataDecl dataDecls)
      ,"-- definitions"
      ,intercalate "\n" (map show definitions)
      ]
    where showImport ss = "import "++intercalate "." ss
          showDataDecl (tn,as,cds) =
            "data "++show tn++" "++unwords (map showKindedVar as)++" = "++intercalate " | " (map showConsDecl cds)
            where showConsDecl (cn,ts) = show cn ++" "++ unwords (map show ts)
          showTypeDecl (tn,as, t) = "type "++show tn++" "++unwords (map showKindedVar as)++" = "++show t
          showKindedVar (a,k) = show a++":"++show k
