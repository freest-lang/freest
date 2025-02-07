module LeaST.Interpreter where

import qualified LeaST.LeaST as L
import qualified Syntax.Base as B

import Data.List ( find )

interpret :: L.Exp -> Value
interpret exp = eval builtins exp

data Value = VInt Int
  | VFloat Float
  | VChar Char
  | VCon String [Value]
  | VClosure Context B.Variable L.Exp
  | VBuiltin (Value -> Value)

instance Show Value where
  show (VInt int) = show int
  show (VFloat float) = show float
  show (VChar char) = show char
  show (VCon iden args) = iden ++ " " ++ unwords ( map show args)
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
    VCon iden consArgs -> VCon iden (argVal:consArgs)
    VClosure cctx var cExp -> eval ((getStringFromVariable var, argVal):cctx) cExp
    VBuiltin builtin -> builtin argVal 
eval _ (L.Con iden) = VCon (getStringFromIdentifier iden) []
eval ctx (L.Case exp alts) =
  let val = eval ctx exp in
  let (nextCtx, nextExp) = patternMatch ctx val alts in
  eval nextCtx nextExp

patternMatch :: Context -> Value -> [(L.Alt, [B.Variable], L.Exp)] -> (Context, L.Exp)
patternMatch _ _ [] = error "Pattern matching was not exhaustive"
patternMatch ctx val@(VInt int2) ((L.ALit (L.LInt int), _, exp):alts) = if int2 == int then (ctx, exp) else patternMatch ctx val alts
patternMatch ctx val@(VFloat float2) ((L.ALit (L.LFloat float), _, exp):alts) = if float2 == float then (ctx, exp) else patternMatch ctx val alts
patternMatch ctx val@(VChar char2) ((L.ALit (L.LChar char), _, exp):alts) = if char2 == char then (ctx, exp) else patternMatch ctx val alts
patternMatch ctx _ ((L.ADefault, _, exp):_) = (ctx, exp)
patternMatch ctx val@(VCon iden2 conArgs) ((L.ACon iden, vars, exp):alts) = if iden2 == getStringFromIdentifier iden then (zip (map getStringFromVariable vars) conArgs ++ ctx, exp) else patternMatch ctx val alts

getStringFromVariable :: B.Variable -> String
getStringFromVariable (B.Variable { B.varSpan=_, B.internal=_, B.external=var}) = var

getStringFromIdentifier :: B.Identifier -> String
getStringFromIdentifier (B.Identifier _ str) = str

type Context = [(String, Value)]

getVar :: Context -> String -> Value
getVar ctx iden = case find (\(iden2, val) -> iden == iden2) ctx of
  Just (_, val) -> val
  Nothing -> error ("Variable `" ++ iden ++ "` not found.")

builtins :: [(String, Value)]
builtins = [
  ("(+)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt $ x + y)))
  ]
