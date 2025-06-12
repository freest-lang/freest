module LeaST.LeaST where

import qualified Syntax.Base as B
--qs: addEqimport qualified Syntax.Type as T  
import qualified Syntax.Type as T
import qualified Syntax.Kind as K
import qualified Syntax.Module as M

type LeastProg = (M.DataDeclList, M.TypeDeclList, M.KindSigList, Exp)

data Exp 
  = Var B.Variable
  | Lit Literal
  | Abs B.Variable T.Type Exp
  | App Exp Exp
  | Con B.Identifier
  | Case Exp [(Alt, Exp)]
  | Type T.Type  --tirar
  | TAbs B.Variable K.Kind Exp
  | TApp Exp T.Type --mudar TApp Exp T.Type
  -- | Source B.Span Exp
  deriving Show

data Literal = LInt Int
  | LFloat Double
  | LChar Char
  deriving Show

data Alt = ACon B.Identifier [B.Variable]
  | ALit Literal
  | AWildCard
  deriving Show

-- type Bind = B.Level (B.Variable T.Type Exp) (B.Variable K.Kind Exp)
