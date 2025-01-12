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
  , IdDeclList
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
import           Syntax.Expression (Exp, Pat, LetDecl)
import           Syntax.Kind (Kind)
import           Syntax.Type (Type)

import           Data.List (intercalate)
import           Data.Maybe (fromMaybe)
import           Debug.Trace (trace)

type ConsDeclList = [(Identifier, [Type])]
type DataDeclList = [(Identifier, ([Variable], ConsDeclList))]
type TypeDeclList = [(Identifier, ([Variable], Type))]
type IdDeclList  = [(Identifier, Kind)]

data Module
  = Module { name        :: Maybe [String]
           , imports     :: [[String]]
           , dataDecls   :: DataDeclList
           , typeDecls   :: TypeDeclList
           , kindSigs    :: IdDeclList
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

insertDataDecl ::  Identifier -> [Variable] -> ConsDeclList -> Module -> Module
insertDataDecl n as b m = m{dataDecls = (n, (as, b)) : dataDecls m}

insertTypeDecl :: Identifier -> [Variable] -> Type -> Module -> Module
insertTypeDecl n as t m = m{typeDecls = (n, (as, t)) : typeDecls m}

insertKindSig :: Identifier -> Kind -> Module -> Module
insertKindSig n k m = m{kindSigs = (n, k) : kindSigs m}

insertDef :: LetDecl -> Module -> Module
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
    intercalate "\n"
      [case name of Nothing -> "\n" ; Just n -> "\nmodule "++intercalate "." n++" where"
      ,"-- imports"
      ,intercalate "\n" (map showImport imports)
      ,"-- kind signatures"
      ,intercalate "\n" (map showKindSig kindSigs)
      ,"-- type declarations"
      ,intercalate "\n" (map showTypeDecl typeDecls)
      ,"-- data declarations"
      ,intercalate "\n" (map showDataDecl dataDecls)
      ,"-- definitions"
      ,intercalate "\n" (map show definitions)
      ]
    where showImport ss = "import "++intercalate "." ss
          showKindSig (i, k) = "type "++show i++" : "++show k
          showDataDecl (i, (as,cds)) =
            "data "++show i++" "++unwords (map show as)++" = "++intercalate " | " (map showConsDecl cds)
            where showConsDecl (cn,ts) = show cn ++" "++ unwords (map show ts)
          showTypeDecl (i, (as, t)) = "type "++show i++" "++unwords (map show as)++" = "++show t
