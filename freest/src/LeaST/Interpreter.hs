module LeaST.Interpreter where

import qualified LeaST.LeaST as L
import qualified Syntax.Base as B

import Data.List ( find )
import Data.Char (chr, ord)
import GHC.Float
import Control.Concurrent.Chan as C

interpret :: L.Exp -> IO Value
interpret exp = eval builtins exp

type ChannelEnd = (C.Chan Value, C.Chan Value)

data Value = VInt Int
  | VFloat Float
  | VChar Char
  | VCon String [Value]
  | VClosure Context B.Variable L.Exp
  | VBuiltin (Value -> Value)
  | VIO (IO Value)
  | VChan ChannelEnd

instance Show Value where
  show (VInt int) = show int
  show (VFloat float) = show float
  show (VChar char) = show char
  show (VCon iden args) = iden ++ " " ++ unwords (map show args)
  show (VClosure _ _ _) = "<closure>"
  show (VBuiltin _ ) = "<builtin>"
  show (VIO _) = "<vio>"
  show (VChan chanEnd) = "<channel end>"
 
eval :: Context -> L.Exp -> IO Value
eval ctx (L.Var var ) = return $ getVar ctx (getStringFromVariable var)
eval _ (L.Lit (L.LInt int)) = return $ VInt int
eval _ (L.Lit (L.LFloat float)) = return $ VFloat float
eval _ (L.Lit (L.LChar char)) = return $ VChar char
eval ctx (L.Abs var _ exp) = return $ VClosure ctx var exp
eval ctx (L.App lExp rExp) = do
  rVal <- eval ctx rExp
  lVal <- eval ctx lExp
  case lVal of
    VCon iden consArgs -> return $ VCon iden (consArgs++[rVal])
    VClosure cctx var cExp -> eval ((getStrinFromVariable var, rVal):cctx) cExp
    VBuiltin builtin -> return $ builtin rVal
    VIO vio -> do vio
eval _ (L.Con iden) = return $ VCon (getStringFromIdentifier iden) []
eval ctx (L.Case exp alts) = do
  val <- eval ctx exp
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
  ("chan", VIO $ do (chanL, chanR) <- chan
                    return $ VCon "(,)" [VChan chanL, VChan chanR]),
  ("receive", VBuiltin (\(VChan c) -> VIO $ receive c >>= \(val, c) -> return $ VCon "(,)" [val, VChan c])),
  ("send", VBuiltin (\val -> VBuiltin (\(VChan c) -> VIO $ VChan <$> send val c))),
  ("wait", VBuiltin wait),
  ("close", VBuiltin (VIO . close)),

  ("(+)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x + y)))),
  ("(-)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x - y)))),
  ("subtract", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x - y)))),
  ("(*)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x * y)))),
  ("(/)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (div x y)))),
  ("(^)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x ^ y)))),
  ("abs", VBuiltin (\(VInt x) -> VInt (abs x))),
  ("mod", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (mod x y)))),
  ("rem", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (rem x y)))),
  ("negate", VBuiltin (\(VInt x) -> VInt (-x))),
  ("max", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (max x y)))),
  ("min", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (min x y)))),
  ("succ", VBuiltin (\(VInt x) -> VInt (succ x))),
  ("pred", VBuiltin (\(VInt x) -> VInt (pred x))),
  ("quot", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (quot x y)))),
  ("even", VBuiltin (\(VInt x) -> hsToLstBool (even x))),
  ("odd", VBuiltin (\(VInt x) -> hsToLstBool (odd x))),
  ("gcd", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (gcd x y)))),
  ("lcm", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (lcm x y)))),

  ("(+.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x + y)))),
  ("(-.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x - y)))),
  ("(*.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x * y)))),
  ("(/.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x / y)))),
  ("negateF", VBuiltin (\(VFloat x) -> VFloat (negate x))),
  ("maxF", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (max x y)))),
  ("minF", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (min x y)))),
  ("truncate", VBuiltin (\(VFloat x) -> VInt (truncate x))),
  ("round", VBuiltin (\(VFloat x) -> VInt (round x))),
  ("ceiling", VBuiltin (\(VFloat x) -> VInt (ceiling x))),
  ("floor", VBuiltin (\(VFloat x) -> VInt (floor x))),
  ("recip", VBuiltin (\(VFloat x) -> VFloat (recip x))),
  ("pi", VFloat pi),
  ("exp", VBuiltin (\(VFloat x) -> VFloat (exp x))),
  ("log", VBuiltin (\(VFloat x) -> VFloat (log x))),
  ("sqrt", VBuiltin (\(VFloat x) -> VFloat (sqrt x))),
  ("(**)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x ** y)))),
  ("logBase", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (logBase x y)))),
  ("sin", VBuiltin (\(VFloat x) -> VFloat (sin x))),
  ("cos", VBuiltin (\(VFloat x) -> VFloat (cos x))),
  ("tan", VBuiltin (\(VFloat x) -> VFloat (tan x))),
  ("asin", VBuiltin (\(VFloat x) -> VFloat (asin x))),
  ("acos", VBuiltin (\(VFloat x) -> VFloat (acos x))),
  ("atan", VBuiltin (\(VFloat x) -> VFloat (atan x))),
  ("sinh", VBuiltin (\(VFloat x) -> VFloat (sinh x))),
  ("cosh", VBuiltin (\(VFloat x) -> VFloat (cosh x))),
  ("tanh", VBuiltin (\(VFloat x) -> VFloat (tanh x))),
  ("expm1", VBuiltin (\(VFloat x) -> VFloat (expm1 x))),
  ("log1p", VBuiltin (\(VFloat x) -> VFloat (log1p x))),
  ("log1pexp", VBuiltin (\(VFloat x) -> VFloat (log1pexp x))),
  ("log1mexp", VBuiltin (\(VFloat x) -> VFloat (log1mexp x))),
  ("fromInteger", VBuiltin (\(VInt x) -> VFloat (fromInteger (toInteger x)))),

  ("(&&)", VBuiltin (\x -> VBuiltin (\y -> hsToLstBool (lstToHsBool x && lstToHsBool y)))),
  ("(||)", VBuiltin (\x -> VBuiltin (\y -> hsToLstBool (lstToHsBool x || lstToHsBool y)))),

  ("(==)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToLstBool (x == y)))),
  ("(/=)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToLstBool (x /= y)))),
  ("(>)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToLstBool (x > y)))),
  ("(>=)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToLstBool (x >= y)))),
  ("(<)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToLstBool (x < y)))),
  ("(<=)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToLstBool (x <= y)))),
  ("(>.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToLstBool (x > y)))),
  ("(>=.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToLstBool (x >= y)))),
  ("(<.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToLstBool (x < y)))),
  ("(<=.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToLstBool (x <= y)))),

  ("chr", VBuiltin (\(VInt x) -> VChar (chr x))),
  ("ord", VBuiltin (\(VChar c) -> VInt (ord c))),

  -- ("(^^)", VBuiltin (\(VString str1) -> VBuiltin (\(VString str2) -> VString (str1++str2)))),

  -- ("show", VBuiltin (VString . show)),
  -- ("readBool", VBuiltin (\(VString str) -> hsToFstBool (read str))),
  -- ("readInt", VBuiltin (\(VString x) -> VInt (read x))),
  -- ("readInt", VBuiltin (\(VString c) -> VChar (read c))),

  -- ("putStrOut", VBuiltin (\val -> VIO $ putStr (show val) $> VUnit)),
  -- ("putStrErr", VBuiltin (\val -> VIO $ hPutStr stderr (show val) $> VUnit)),
  -- ("getChar", VIO $ getChar <&> VChar),
  -- ("getLine", VIO $ getLine <&> VString),
  -- ("getContents", VIO $ getContents <&> VString),

  -- ("openFile", VBuiltin (\(VString path) -> VBuiltin (\(VCon mode []) -> VIO $ case mode of
  --   "ReadMode" -> openFile path ReadMode <&> VCon "FileHandle" . (:[]) . VHandle
  --   "WriteMode" -> openFile path WriteMode <&> VCon "FileHandle" . (:[]) . VHandle
  --   "AppendMode" -> openFile path AppendMode <&> VCon "FileHandle" . (:[]) . VHandle
  --   _ -> undefined))),
  -- ("putFileStr", VBuiltin (\(VCon "FileHandle" [VHandle handle]) -> VBuiltin (\(VString str) -> VIO $ hPutStr handle str $> VUnit))),
  -- ("readFileChar", VBuiltin (\(VCon "FileHandle" [VHandle handle]) -> VIO $ hGetChar handle <&> VChar)),
  -- ("readFileLine", VBuiltin (\(VCon "FileHandle" [VHandle handle]) -> VIO $ hGetLine handle <&> VString)),
  -- ("isEOF", VBuiltin (\(VCon "FileHandle" [VHandle handle]) -> VIO $ hIsEOF handle <&> hsToFstBool)),
  -- ("closeFile", VBuiltin (\(VCon "FileHandle" [VHandle handle]) -> VIO $ hClose handle $> VUnit)),

  ("id", VBuiltin id)
  ]

-- haskell bool to least bool
hsToLstBool :: Bool -> Value
hsToLstBool True = VCon "True" []
hsToLstBool False = VCon "False" []

-- freeST bool to least bool
lstToHsBool :: Value -> Bool
lstToHsBool (VCon "True" []) = True
lstToHsBool (VCon "False" []) = False

chan :: IO (ChannelEnd, ChannelEnd)
chan = do
  c1 <- C.newChan
  c2 <- C.newChan
  return ((c1, c2), (c2, c1))

receive :: ChannelEnd -> IO (Value, ChannelEnd)
receive c = do
  v <- C.readChan (fst c)
  return (v, c)

send :: Value -> ChannelEnd -> IO ChannelEnd
send v c = do
  C.writeChan (snd c) v
  return c

wait :: Value -> Value
wait (VChan c) =
  VIO $ C.readChan (fst c)

close :: Value -> IO Value
close (VChan c) = do
  C.writeChan (snd c) (VCon "()" [])
  return (VCon "()" [])
