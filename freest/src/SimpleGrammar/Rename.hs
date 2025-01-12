{- |
Module      :  SimpleGrammar.Rename
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Minimal (or canonical) type renaming
-}

module SimpleGrammar.Rename
  ( rename
  )
where

import           Syntax.Base
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )

import qualified Data.Map.Strict               as M
import qualified Data.Set                      as S

type Visited = S.Set Identifier

rename :: TypeDeclMap -> T.Type -> T.Type
rename = ren S.empty
  where
    ren :: Visited -> TypeDeclMap -> T.Type -> T.Type
    ren = undefined

reachable :: Visited -> T.Type -> S.Set Identifier
reachable = undefined
