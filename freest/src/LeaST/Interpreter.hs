module LeaST.Interpreter where

import LeaST.LeaST qualified as L
import Syntax.Base qualified as B
import Utils (internalError)

import Control.Concurrent ( forkIO )
import Control.Concurrent.Chan qualified as Chan
import Data.Functor ( ($>), (<&>), void )
import Data.Char (chr, ord)
import Data.List ( find )
import Data.Map qualified as Map
import GHC.Float ( Floating(log1mexp, expm1, log1p, log1pexp) )
import System.IO ( Handle, putStr, hPutStr, getChar, getLine, getContents, stderr, openFile, IOMode(..), hGetChar, hGetLine, hIsEOF, hClose )

import Debug.Trace

interpret :: L.Exp -> IO Value
interpret = eval builtins

-- TODO: Fatbar implementation will not work because language is strict

type ChannelEnd = (Chan.Chan Value, Chan.Chan Value)

data Value = VInt Int
  | VFloat Double
  | VChar Char
  | VCon String [Value]
  | VClosure Context B.Variable L.Exp
  | VBuiltin (Value -> Value)
  | VIO (IO Value)
  | VChan ChannelEnd
  | VFork
  | VFatbar

instance Show Value where
  show = \case 
    (VInt   x)  -> show x
    (VFloat x)  -> show x
    (VChar  x)  -> show x
    (VCon c vs) -> "("++c ++ " " ++ unwords (map show vs)++")"
    VClosure{}  -> "<closure>"
    VBuiltin{}  -> "<builtin>"
    VIO{}       -> "<vio>"
    VChan{}     -> "<channel end>"
    VFork       -> "<vfork>"
    VFatbar     -> "<vfatbar>"


eval :: Context -> L.Exp -> IO Value
eval ctx = \case 
  L.Var x -> case B.external x of
    "fork"      -> return VFork
    "undefined" -> error ("undefined, called at "++show (B.getSpan x))
    "error__"   -> error "Error"
    "fatbar__"  -> return VFatbar
    _ -> return $ getVar ctx (B.external x)
  L.Lit l -> return case l of 
    L.LInt   x -> VInt   x
    L.LFloat x -> VFloat x
    L.LChar  x -> VChar  x
  L.Abs x _ e -> return $ VClosure ctx x e
  L.App e1 e2 -> do
    v1 <- eval ctx e1
    case v1 of
      VFork -> forkIO (void $ eval ctx (unpackAbs e2)) $> VCon "()" []
      VFatbar -> do
        v2 <- eval ctx e2
        print v2
        case v2 of
          -- TODO: implement this
          VCon "Fail__" [] -> undefined
          -- TODO: this is wrong
          _ -> return $ VBuiltin (const v2)
      _ -> do 
        v2 <- eval ctx e2
        case v1 of
          VCon i vs         -> return $ VCon i (vs ++ [v2])
          VClosure ctx' x e -> eval ((B.external x, v2) : ctx') e
          VBuiltin f        -> case f v2 of VIO iov -> iov
                                            v       -> return v
          VIO iov -> iov
  L.Con i -> return $ VCon (show i) []
  L.Case e as -> do
    v <- eval ctx e
    uncurry eval $ patternMatch ctx v as
  L.TAbs x _ e -> return $ VClosure ctx x e
  L.TApp e1 e2 -> do
    v1 <- eval ctx e1
    v2 <- eval ctx e2
    case v1 of
      VClosure cctx _ cExp -> eval cctx cExp
      VBuiltin b -> return $ b v2 
      _ -> undefined
  L.Type _ -> return $ VCon "()" []

patternMatch :: Context -> Value -> [(L.Alt, L.Exp)] -> (Context, L.Exp)
patternMatch _ _ [] = error "Pattern matching was not exhaustive"
patternMatch ctx val@(VInt int2) ((L.ALit (L.LInt int), exp) : alts) = if int2 == int then (ctx, exp) else patternMatch ctx val alts
patternMatch ctx val@(VFloat float2) ((L.ALit (L.LFloat float), exp) : alts) = if float2 == float then (ctx, exp) else patternMatch ctx val alts
patternMatch ctx val@(VChar char2) ((L.ALit (L.LChar char), exp) : alts) = if char2 == char then (ctx, exp) else patternMatch ctx val alts
patternMatch ctx _ ((L.AWildCard, exp) : _) = (ctx, exp)
patternMatch ctx val@(VCon iden2 conArgs) ((L.ACon iden vars, exp) : alts) = if iden2 == show iden then (zip (map B.external vars) conArgs ++ ctx, exp) else patternMatch ctx val alts


unpackAbs :: L.Exp -> L.Exp
unpackAbs (L.Abs _ _ exp) = exp
unpackAbs exp = traceShow exp undefined

type Context = [(String, Value)]

getVar :: Context -> String -> Value
getVar ctx x = case lookup x ctx of
  Just v  -> v
  Nothing -> internalError ("variable `" ++ x ++ "` not in scope.")

builtins :: Context
builtins = [
  ("chan", VIO $ do (chanL, chanR) <- chan
                    return $ VCon "(,)" [VChan chanL, VChan chanR]),
  ("receive", VBuiltin (\_ty1 -> VBuiltin (\_ty2 -> VBuiltin (\(VChan c) -> VIO $ receive c >>= \(val, c) -> return $ VCon "(,)" [val, VChan c])))),
  ("send", VBuiltin (\_ty1 -> VBuiltin (\_ty2 -> VBuiltin (\val -> VBuiltin (\(VChan c) -> VIO $ VChan <$> send val c))))),
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
  ("div", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (div x y)))),
  ("even", VBuiltin (\(VInt x) -> hsToLstBool (even x))),
  ("odd", VBuiltin (\(VInt x) -> hsToLstBool (odd x))),
  ("gcd", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (gcd x y)))),
  ("lcm", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (lcm x y)))),

  ("(+.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x + y)))),
  ("(-.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x - y)))),
  ("(*.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x * y)))),
  ("(/.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x / y)))),
  ("negateF", VBuiltin (\(VFloat x) -> VFloat (negate x))),
  ("absF", VBuiltin (\(VFloat x) -> VFloat (abs x))),
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

  ("putStrOut", VBuiltin (\_ty -> VBuiltin (\val -> VIO $ putStr (show val) $> VCon "()" []))),
  ("putStrErr", VBuiltin (\val -> VIO $ hPutStr stderr (show val) $> VCon "()" [])),
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

  ("id", VBuiltin id),
  ("undefined", VBuiltin undefined),
  ("fork", VFork)
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
  c1 <- Chan.newChan
  c2 <- Chan.newChan
  return ((c1, c2), (c2, c1))

receive :: ChannelEnd -> IO (Value, ChannelEnd)
receive c = do
  v <- Chan.readChan (fst c)
  return (v, c)

send :: Value -> ChannelEnd -> IO ChannelEnd
send v c = do
  Chan.writeChan (snd c) v
  return c

wait :: Value -> Value
wait (VChan c) =
  VIO $ Chan.readChan (fst c)

close :: Value -> IO Value
close (VChan c) = do
  Chan.writeChan (snd c) (VCon "()" [])
  return (VCon "()" [])
