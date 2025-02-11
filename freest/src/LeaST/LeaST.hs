module LeaST.LeaST where

import qualified Syntax.Base as B
import qualified Syntax.Type as T
import qualified Syntax.Kind as K


data Exp 
  = Var B.Variable
  | Lit Literal
  | Abs B.Variable T.Type Exp
  | App Exp Exp
  | Con B.Identifier
  | Case Exp [(Alt, [B.Variable], Exp)]
  | Type T.Type
  | TAbs B.Variable K.Kind Exp
  | TApp Exp Exp
  -- | Source B.Span Exp
  deriving Show

data Literal = LInt Int
  | LFloat Float
  | LChar Char
  deriving Show

data Alt = ACon B.Identifier
  | ALit Literal
  | ADefault
  deriving Show

-- type Bind = B.Level (B.Variable T.Type Exp) (B.Variable K.Kind Exp)
