module LeaST.Interpreter where

import qualified LeaST.LeaST as L
import qualified Syntax.Base as B

import Data.List ( find )

interpret :: L.Exp -> Value
interpret exp = eval builtins exp

data Value = VInt Int
  | VFloat Float
  | VChar Char
  | VClosure Context B.Variable L.Exp
  | VBuiltin (Value -> Value)

instance Show Value where
  show (VInt int) = show int
  show (VFloat float) = show float
  show (VChar char) = show char
  show (VClosure _ _ _) = "<closure>"
  show (VBuiltin _ ) = "<builtin>"
 
eval :: Context -> L.Exp -> Value
eval ctx (L.Var var ) = getVar ctx (getStringFromVariable var)
eval _ (L.Lit (L.LInt int)) = VInt int
eval _ (L.Lit (L.LFloat float)) = VFloat float
eval _ (L.Lit (L.LChar char)) = VChar char
eval ctx (L.Abs var _ exp) = VClosure ctx var exp
eval ctx (L.App lExp rExp) = let argVal = eval ctx rExp in
  case eval ctx lExp of
    VClosure cctx var cExp -> eval ((getStringFromVariable var, argVal):cctx) cExp
    VBuiltin builtin -> builtin argVal 

getStringFromVariable :: B.Variable -> String
getStringFromVariable (B.Variable { B.varSpan=_, B.internal=_, B.external=var}) = var

type Context = [(String, Value)]

getVar :: Context -> String -> Value
getVar ctx iden = case find (\(iden2, val) -> iden == iden2) ctx of
  Just (_, val) -> val
  Nothing -> error ("Variable `" ++ iden ++ "` not found.")

builtins :: [(String, Value)]
builtins = [
  ("(+)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt $ x + y)))
  ]
