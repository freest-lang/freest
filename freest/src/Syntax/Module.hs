{-# LANGUAGE NamedFieldPuns #-}
{- |
Module      :  Syntax.Module
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains types and functions to represent and manipulate FreeST 
modules.
-}
module Syntax.Module
  ( DataDecl(..)
  , Module(..)
  , setName
  , insertImport
  , insertDataDecl
  , insertTypeDecl
  , insertDef
  , empty
  )
where

import Syntax.Base
import Syntax.Expression (Exp, Pat, LetDecl)
import Syntax.Kind (Kind)
import Syntax.Type (Type)

import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map 

type DataDecl = (Variable, [Variable], [(Variable, [Type])])

data Module
  = Module { name        :: Maybe [String]
           , imports     :: [[String]]
           , dataDecls   :: [DataDecl]
           , typeDecls   :: [(Variable, [Variable], Type)]
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

insertDataDecl ::  Variable -> [Variable] -> [(Variable, [Type])] -> Module -> Module
insertDataDecl n as b m = m{dataDecls = (n, as, b) : dataDecls m}

insertTypeDecl :: Variable -> [Variable] -> Type -> Module -> Module
insertTypeDecl n as t m = m{typeDecls = (n, as, t) : typeDecls m}

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
      ,intercalate "\n" (map showImport imports)
      ,intercalate "\n" (map showDataDecl dataDecls)
      ,intercalate "\n" (map showTypeDecl typeDecls)
      ,intercalate "\n" (map show definitions)
      ]
    where showImport ss = "import "++intercalate "." ss
          showDataDecl (n, as, cs) = "data "++show n++" "++unwords (map show as)++" = "++intercalate " | " (map showCons cs)
            where showCons (s,ts) = show s ++" "++ unwords (map show ts)
          showTypeDecl (n, as, t) = "type "++show n++" "++unwords (map show as)++" = "++show t
