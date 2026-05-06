{- |
Module      :  Syntax.Command
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Commands for the freeSTi REPL.
-}
module Syntax.Command ( Command(..), ) where

-- import Syntax.Base
-- import Syntax.Kind qualified as K
import Syntax.Type.Unkinded qualified as TU
import Syntax.Module qualified as M

data Command = Type TU.ParsedType | Decls M.ParsedModule

-- data Decl 
--   = TypeDecl Identifier [(Variable, K.Kind)] TU.ParsedType K.Kind
--   | DataDecl Identifier [(Variable, K.Kind)] K.Kind

-- type Equation = (Identifier, [(Variable, K.Kind)], TU.ParsedType, K.Kind)