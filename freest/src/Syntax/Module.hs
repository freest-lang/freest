{-# LANGUAGE NamedFieldPuns #-}
{- |
Module      :  Syntax.Module
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains types and functions to represent and manipulate FreeST 
modules.
-}
module Syntax.Module
  ( DataDecls
  , ConsDecls
  , TypeDecls
  , Lambda
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
import qualified Syntax.Kind as K (Kind)
import qualified Syntax.Type as T (Type)

import           Data.List (intercalate)
import           Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as Map 
import           Debug.Trace (trace)

type Lambda t = ([(Variable, K.Kind)], t)
type TypeDecls = Map.Map Identifier (Lambda T.Type)
type ConsDecls = Map.Map Identifier [T.Type]
type DataDecls = Map.Map Identifier (Lambda ConsDecls)

data Module
  = Module { name        :: Maybe [String]
           , imports     :: [[String]]
           , dataDecls   :: DataDecls
           , typeDecls   :: TypeDecls
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

insertDataDecl ::  Identifier -> [(Variable, K.Kind)] -> [(Identifier, [T.Type])] -> Module -> Module
insertDataDecl n aks b m = m{dataDecls = Map.insert n (aks, Map.fromList b) (dataDecls m)}

insertTypeDecl :: Identifier -> [(Variable, K.Kind)] -> T.Type -> Module -> Module
insertTypeDecl n aks t m = m{typeDecls = Map.insert n (aks, t) (typeDecls m)}

insertDef :: LetDecl -> Module -> Module
insertDef d m = m{definitions = d : definitions m}

empty :: Module
empty = Module{ name        = Nothing
              , imports     = []
              , dataDecls   = Map.empty
              , typeDecls   = Map.empty
              , definitions = []
              }

instance Show Module where
  show Module{name,imports,dataDecls,typeDecls,definitions} =
    intercalate "\n"
      [case name of Nothing -> "\n" ; Just n -> "\nmodule "++intercalate "." n++" where"
      ,"-- imports"
      ,intercalate "\n" (map showImport imports)
      ,"-- type declarations"
      ,intercalate "\n" (map showTypeDecl (Map.assocs typeDecls))
      ,"-- data declarations"
      ,intercalate "\n" (map showDataDecl (Map.assocs dataDecls))
      ,"-- definitions"
      ,intercalate "\n" (map show definitions)
      ]
    where showImport ss = "import "++intercalate "." ss
          showDataDecl (i,(as,cds)) =
            "data "++show i++" "++unwords (map showKindedVar as)++" = "++intercalate " | " (map showConsDecl (Map.assocs cds))
            where showConsDecl (cn,ts) = show cn ++" "++ unwords (map show ts)
          showTypeDecl (i, (aks, t)) = "type "++show i++" "++unwords (map showKindedVar aks)++" = "++show t
          showKindedVar (a,k) = show a++":"++show k
