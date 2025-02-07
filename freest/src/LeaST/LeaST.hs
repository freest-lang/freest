module LeaST.LeaST where

import qualified Syntax.Base as B
import qualified Syntax.Type as T
import qualified Syntax.Kind as K


data Exp 
  = Var B.Variable
  | Lit Literal
  | Abs B.Variable T.Type Exp
  | App Exp Exp
  -- | Type B.Type
  -- | Case Exp [(Alt, [B.Variable], Exp)]
  -- | Source B.Span Exp
  -- TODO Mutual recursive migh need fix point
  -- TODO uma abstração de tipos 
  -- TODO uma aplicação de tipos
  deriving Show

data Literal = LInt Int
  | LFloat Float
  | LChar Char
  deriving Show

data Alt = Con B.Identifier
  | Literal Literal
  | Default

-- type Bind = B.Level (B.Variable T.Type Exp) (B.Variable K.Kind Exp)
