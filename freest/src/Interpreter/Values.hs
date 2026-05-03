{- |
Module      :  Interpreter.Values
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's values.
-}
module Interpreter.Values 
  (
    Env,
    Value(..),
    isVUndefined,
    showTups,
    chan,
    receive,
    receiveLabel,
    send,
    wait,
    close,
    builtins,
    hsToFstBool,
    fstToHsBool
  ) where

import qualified Control.Concurrent.Chan as C (Chan, newChan, readChan, writeChan)
import Data.Char (chr, ord)
import Data.Functor (($>), (<&>))
import qualified Data.Map as Map
import GHC.Float
import System.IO (Handle, hPutStr, stderr, openFile, IOMode (..), hGetChar, hGetLine, hIsEOF, hClose)

import qualified Syntax.Base as B
import qualified Syntax.Expression as E
import Syntax.Base (nullSpan)

-- | An environment, composed of bindings from variables to values
type Env = Map.Map B.Variable Value

data Value
  = VInt Int
  | VFloat Double
  | VUnit
  | VChar Char
  | VString String
  | VCons String [Value]
  | VClosure [E.Pat] E.KindedExp Env
  | VBuiltin (Value -> Value)
  | VIO (IO Value)
  | VHandle Handle
  | VLabel String
  | VFork
  | VChan ChannelEnd
  | VSelect String
  | VUndefined

isVUndefined :: Value -> Bool
isVUndefined VUndefined = True
isVUndefined _ = False

instance Show Value where
  show VUnit = "()"
  show (VInt n) = show n
  show (VFloat n) = show n
  show (VChar c) = show c
  show (VString str) = show str
  show (VCons str vals) = str ++ " " ++ unwords (map show vals)
  show (VClosure {}) = "<closure>"
  show (VBuiltin _) = "<builtin>"
  show (VIO io) = "<IO>"
  show (VHandle _) = "<handle>"
  show (VLabel str) = "<label> string"
  show (VChan _) = "<chan>"
  show (VSelect _) = "<select>"
  show VUndefined = "<undefined>"

showTups :: [Value] -> String
showTups [val] = show val
showTups (val:vals) = show val ++ " (-1), " ++ showTups vals

type ChannelEnd = (C.Chan Value, C.Chan Value)

chan :: IO (ChannelEnd, ChannelEnd)
chan = do
  c1 <- C.newChan
  c2 <- C.newChan
  return ((c1, c2), (c2, c1))

receive :: ChannelEnd -> IO (Value, ChannelEnd)
receive c = do
  v <- C.readChan (fst c)
  return (v, c)

receiveLabel :: ChannelEnd -> IO String
receiveLabel c = do
  VLabel val <- C.readChan (fst c)
  return val

send :: Value -> ChannelEnd -> IO ChannelEnd
send v c = do
  C.writeChan (snd c) v
  return c

wait :: Value -> Value
wait (VChan c) =
  VIO $ C.readChan (fst c)

close :: Value -> IO Value
close (VChan c) = do
  C.writeChan (snd c) VUnit
  return VUnit

builtins :: Map.Map String Value
builtins = Map.fromList 
  [ -- communication primitives
    ("receive",       VBuiltin (\(VChan c) -> VIO $ receive c >>= \(val, c) -> return $ VCons "(,)" [val, VChan c]))
  , ("send",          VBuiltin (\val -> VBuiltin (\(VChan c) -> VIO $ VChan <$> send val c)))
  , ("wait",          VBuiltin wait)
  , ("close",         VBuiltin (VIO . close))
  -- operations on integers
  , ("(+)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x + y))))
  , ("(-)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x - y))))
  , ("subtract",      VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x - y))))
  , ("(*)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x * y))))
  , ("(/)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (div x y))))
  , ("(^)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x ^ y))))
  , ("abs",           VBuiltin (\(VInt x) -> VInt (abs x)))
  , ("mod",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (mod x y))))
  , ("rem",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (rem x y))))
  , ("negate",        VBuiltin (\(VInt x) -> VInt (-x)))
  , ("max",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (max x y))))
  , ("min",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (min x y))))
  , ("succ",          VBuiltin (\(VInt x) -> VInt (succ x)))
  , ("pred",          VBuiltin (\(VInt x) -> VInt (pred x)))
  , ("quot",          VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (quot x y))))
  , ("even",          VBuiltin (\(VInt x) -> hsToFstBool (even x)))
  , ("odd",           VBuiltin (\(VInt x) -> hsToFstBool (odd x)))
  , ("gcd",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (gcd x y))))
  , ("lcm",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (lcm x y))))
    -- operations on floats
  , ("(+.)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x + y))))
  , ("(-.)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x - y))))
  , ("(*.)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x * y))))
  , ("(/.)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x / y))))
  , ("negateF",       VBuiltin (\(VFloat x) -> VFloat (negate x)))
  , ("maxF",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (max x y))))
  , ("minF",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (min x y))))
  , ("truncate",      VBuiltin (\(VFloat x) -> VInt (truncate x)))
  , ("round",         VBuiltin (\(VFloat x) -> VInt (round x)))
  , ("ceiling",       VBuiltin (\(VFloat x) -> VInt (ceiling x)))
  , ("floor",         VBuiltin (\(VFloat x) -> VInt (floor x)))
  , ("recip",         VBuiltin (\(VFloat x) -> VFloat (recip x)))
  , ("pi",            VFloat pi)
  , ("exp",           VBuiltin (\(VFloat x) -> VFloat (exp x)))
  , ("log",           VBuiltin (\(VFloat x) -> VFloat (log x)))
  , ("sqrt",          VBuiltin (\(VFloat x) -> VFloat (sqrt x)))
  , ("(**)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x ** y))))
  , ("logBase",       VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (logBase x y))))
  , ("sin",           VBuiltin (\(VFloat x) -> VFloat (sin x)))
  , ("cos",           VBuiltin (\(VFloat x) -> VFloat (cos x)))
  , ("tan",           VBuiltin (\(VFloat x) -> VFloat (tan x)))
  , ("asin",          VBuiltin (\(VFloat x) -> VFloat (asin x)))
  , ("acos",          VBuiltin (\(VFloat x) -> VFloat (acos x)))
  , ("atan",          VBuiltin (\(VFloat x) -> VFloat (atan x)))
  , ("sinh",          VBuiltin (\(VFloat x) -> VFloat (sinh x)))
  , ("cosh",          VBuiltin (\(VFloat x) -> VFloat (cosh x)))
  , ("tanh",          VBuiltin (\(VFloat x) -> VFloat (tanh x)))
  , ("expm1",         VBuiltin (\(VFloat x) -> VFloat (expm1 x)))
  , ("log1p",         VBuiltin (\(VFloat x) -> VFloat (log1p x)))
  , ("log1pexp",      VBuiltin (\(VFloat x) -> VFloat (log1pexp x)))
  , ("log1mexp",      VBuiltin (\(VFloat x) -> VFloat (log1mexp x)))
  , ("fromInteger",   VBuiltin (\(VInt x) -> VFloat (fromInteger (toInteger x))))
  -- logical operators
  , ("(&&)",          VBuiltin (\x -> VBuiltin (\y -> hsToFstBool (fstToHsBool x && fstToHsBool y))))
  , ("(||)",          VBuiltin (\x -> VBuiltin (\y -> hsToFstBool (fstToHsBool x || fstToHsBool y))))
  -- comparison operators
  , ("(==)",          VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x == y))))
  , ("(/=)",          VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x /= y))))
  , ("(>)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x > y))))
  , ("(>=)",          VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x >= y))))
  , ("(<)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x < y))))
  , ("(<=)",          VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x <= y))))
  , ("(>.)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x > y))))
  , ("(>=.)",         VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x >= y))))
  , ("(<.)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x < y))))
  , ("(<=.)",         VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x <= y))))
  -- char conversion
  , ("chr",           VBuiltin (\(VInt x) -> VChar (chr x)))
  , ("ord",           VBuiltin (\(VChar c) -> VInt (ord c)))
  -- strings
  , ("(^^)",          VBuiltin (\(VString str1) -> VBuiltin (\(VString str2) -> VString (str1++str2))))
  -- IO operators
  , ("show",          VBuiltin (VString . show))
  , ("readBool",      VBuiltin (\(VString str) -> hsToFstBool (read str)))
  , ("readInt",       VBuiltin (\(VString x) -> VInt (read x)))
  , ("readInt",       VBuiltin (\(VString c) -> VChar (read c)))
  -- Parser/Lexer does not accept variables starting with __
  , ("putStrOut",     VBuiltin (\val -> VIO $ putStr (show val) $> VUnit))
  , ("putStrErr",     VBuiltin (\val -> VIO $ hPutStr stderr (show val) $> VUnit))
  , ("getChar",       VIO $ getChar <&> VChar)
  , ("getLine",       VIO $ getLine <&> VString)
  , ("getContents",   VIO $ getContents <&> VString)
  -- read and write to files
  , ("openFile",      VBuiltin (\(VString path) -> VBuiltin (\(VCons mode []) -> VIO $ case mode of
                        "ReadMode" -> openFile path ReadMode <&> VCons "FileHandle" . (:[]) . VHandle
                        "WriteMode" -> openFile path WriteMode <&> VCons "FileHandle" . (:[]) . VHandle
                        "AppendMode" -> openFile path AppendMode <&> VCons "FileHandle" . (:[]) . VHandle
                        _ -> undefined)))
  , ("putFileStr",    VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VBuiltin (\(VString str) -> VIO $ hPutStr handle str $> VUnit)))
  , ("readFileChar",  VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hGetChar handle <&> VChar))
  , ("readFileLine",  VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hGetLine handle <&> VString))
  , ("isEOF",         VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hIsEOF handle <&> hsToFstBool))
  , ("closeFile",     VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hClose handle $> VUnit))

  , ("id",            VBuiltin id)
  ]

{- builtins' :: Env
builtins' = Map.fromList 
  [ -- communication primitives
    (B.Variable nullSpan "receive" (-1), VBuiltin (\(VChan c) -> VIO $ receive c >>= \(val, c) -> return $ VCons "(,)" [val, VChan c]))
  , (B.Variable nullSpan "send" (-1), VBuiltin (\val -> VBuiltin (\(VChan c) -> VIO $ VChan <$> send val c)))
  , (B.Variable nullSpan "wait" (-1), VBuiltin wait)
  , (B.Variable nullSpan "close" (-1), VBuiltin (VIO . close))
  -- operations on integers
  , (B.Variable nullSpan "(+)" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x + y))))
  , (B.Variable nullSpan "(-)" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x - y))))
  , (B.Variable nullSpan "subtract" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x - y))))
  , (B.Variable nullSpan "(*)" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x * y))))
  , (B.Variable nullSpan "(/)" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (div x y))))
  , (B.Variable nullSpan "(^)" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x ^ y))))
  , (B.Variable nullSpan "abs" (-1), VBuiltin (\(VInt x) -> VInt (abs x)))
  , (B.Variable nullSpan "mod" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (mod x y))))
  , (B.Variable nullSpan "rem" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (rem x y))))
  , (B.Variable nullSpan "negate" (-1), VBuiltin (\(VInt x) -> VInt (-x)))
  , (B.Variable nullSpan "max" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (max x y))))
  , (B.Variable nullSpan "min" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (min x y))))
  , (B.Variable nullSpan "succ" (-1), VBuiltin (\(VInt x) -> VInt (succ x)))
  , (B.Variable nullSpan "pred" (-1), VBuiltin (\(VInt x) -> VInt (pred x)))
  , (B.Variable nullSpan "quot" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (quot x y))))
  , (B.Variable nullSpan "even" (-1), VBuiltin (\(VInt x) -> hsToFstBool (even x)))
  , (B.Variable nullSpan "odd" (-1), VBuiltin (\(VInt x) -> hsToFstBool (odd x)))
  , (B.Variable nullSpan "gcd" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (gcd x y))))
  , (B.Variable nullSpan "lcm" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (lcm x y))))
    -- operations on floats
  , (B.Variable nullSpan "(+.)" (-1), VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x + y))))
  , (B.Variable nullSpan "(-.)" (-1), VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x - y))))
  , (B.Variable nullSpan "(*.)" (-1), VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x * y))))
  , (B.Variable nullSpan "(/.)" (-1), VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x / y))))
  , (B.Variable nullSpan "negateF" (-1), VBuiltin (\(VFloat x) -> VFloat (negate x)))
  , (B.Variable nullSpan "maxF" (-1), VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (max x y))))
  , (B.Variable nullSpan "minF" (-1), VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (min x y))))
  , (B.Variable nullSpan "truncate" (-1), VBuiltin (\(VFloat x) -> VInt (truncate x)))
  , (B.Variable nullSpan "round" (-1), VBuiltin (\(VFloat x) -> VInt (round x)))
  , (B.Variable nullSpan "ceiling" (-1), VBuiltin (\(VFloat x) -> VInt (ceiling x)))
  , (B.Variable nullSpan "floor" (-1), VBuiltin (\(VFloat x) -> VInt (floor x)))
  , (B.Variable nullSpan "recip" (-1), VBuiltin (\(VFloat x) -> VFloat (recip x)))
  , (B.Variable nullSpan "pi" (-1), VFloat pi)
  , (B.Variable nullSpan "exp" (-1), VBuiltin (\(VFloat x) -> VFloat (exp x)))
  , (B.Variable nullSpan "log" (-1), VBuiltin (\(VFloat x) -> VFloat (log x)))
  , (B.Variable nullSpan "sqrt" (-1), VBuiltin (\(VFloat x) -> VFloat (sqrt x)))
  , (B.Variable nullSpan "(**)" (-1), VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x ** y))))
  , (B.Variable nullSpan "logBase" (-1), VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (logBase x y))))
  , (B.Variable nullSpan "sin" (-1), VBuiltin (\(VFloat x) -> VFloat (sin x)))
  , (B.Variable nullSpan "cos" (-1), VBuiltin (\(VFloat x) -> VFloat (cos x)))
  , (B.Variable nullSpan "tan" (-1), VBuiltin (\(VFloat x) -> VFloat (tan x)))
  , (B.Variable nullSpan "asin" (-1), VBuiltin (\(VFloat x) -> VFloat (asin x)))
  , (B.Variable nullSpan "acos" (-1), VBuiltin (\(VFloat x) -> VFloat (acos x)))
  , (B.Variable nullSpan "atan" (-1), VBuiltin (\(VFloat x) -> VFloat (atan x)))
  , (B.Variable nullSpan "sinh" (-1), VBuiltin (\(VFloat x) -> VFloat (sinh x)))
  , (B.Variable nullSpan "cosh" (-1), VBuiltin (\(VFloat x) -> VFloat (cosh x)))
  , (B.Variable nullSpan "tanh" (-1), VBuiltin (\(VFloat x) -> VFloat (tanh x)))
  , (B.Variable nullSpan "expm1" (-1), VBuiltin (\(VFloat x) -> VFloat (expm1 x)))
  , (B.Variable nullSpan "log1p" (-1), VBuiltin (\(VFloat x) -> VFloat (log1p x)))
  , (B.Variable nullSpan "log1pexp" (-1), VBuiltin (\(VFloat x) -> VFloat (log1pexp x)))
  , (B.Variable nullSpan "log1mexp" (-1), VBuiltin (\(VFloat x) -> VFloat (log1mexp x)))
  , (B.Variable nullSpan "fromInteger" (-1), VBuiltin (\(VInt x) -> VFloat (fromInteger (toInteger x))))
  -- logical operators
  , (B.Variable nullSpan "(&&)" (-1), VBuiltin (\x -> VBuiltin (\y -> hsToFstBool (fstToHsBool x && fstToHsBool y))))
  , (B.Variable nullSpan "(||)" (-1), VBuiltin (\x -> VBuiltin (\y -> hsToFstBool (fstToHsBool x || fstToHsBool y))))
  -- comparison operators
  , (B.Variable nullSpan "(==)" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x == y))))
  , (B.Variable nullSpan "(/=)" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x /= y))))
  , (B.Variable nullSpan "(>)" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x > y))))
  , (B.Variable nullSpan "(>=)" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x >= y))))
  , (B.Variable nullSpan "(<)" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x < y))))
  , (B.Variable nullSpan "(<=)" (-1), VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x <= y))))
  , (B.Variable nullSpan "(>.)" (-1), VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x > y))))
  , (B.Variable nullSpan "(>=.)" (-1), VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x >= y))))
  , (B.Variable nullSpan "(<.)" (-1), VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x < y))))
  , (B.Variable nullSpan "(<=.)" (-1), VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x <= y))))
  -- char conversion
  , (B.Variable nullSpan "chr" (-1), VBuiltin (\(VInt x) -> VChar (chr x)))
  , (B.Variable nullSpan "ord" (-1), VBuiltin (\(VChar c) -> VInt (ord c)))
  -- strings
  , (B.Variable nullSpan "(^^)" (-1), VBuiltin (\(VString str1) -> VBuiltin (\(VString str2) -> VString (str1++str2))))
  -- IO operators
  , (B.Variable nullSpan "show" (-1), VBuiltin (VString . show))
  , (B.Variable nullSpan "readBool" (-1), VBuiltin (\(VString str) -> hsToFstBool (read str)))
  , (B.Variable nullSpan "readInt" (-1), VBuiltin (\(VString x) -> VInt (read x)))
  , (B.Variable nullSpan "readInt" (-1), VBuiltin (\(VString c) -> VChar (read c)))
  -- Parser/Lexer does not accept variables starting with __
  , (B.Variable nullSpan "putStrOut" (-1), VBuiltin (\val -> VIO $ putStr (show val) $> VUnit))
  , (B.Variable nullSpan "putStrErr" (-1), VBuiltin (\val -> VIO $ hPutStr stderr (show val) $> VUnit))
  , (B.Variable nullSpan "getChar" (-1), VIO $ getChar <&> VChar)
  , (B.Variable nullSpan "getLine" (-1), VIO $ getLine <&> VString)
  , (B.Variable nullSpan "getContents" (-1), VIO $ getContents <&> VString)
  -- read and write to files
  , (B.Variable nullSpan "openFile" (-1), VBuiltin (\(VString path) -> VBuiltin (\(VCons mode []) -> VIO $ case mode of
      "ReadMode" -> openFile path ReadMode <&> VCons "FileHandle" . (:[]) . VHandle
      "WriteMode" -> openFile path WriteMode <&> VCons "FileHandle" . (:[]) . VHandle
      "AppendMode" -> openFile path AppendMode <&> VCons "FileHandle" . (:[]) . VHandle
      _ -> undefined)))
  , (B.Variable nullSpan "putFileStr" (-1), VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VBuiltin (\(VString str) -> VIO $ hPutStr handle str $> VUnit)))
  , (B.Variable nullSpan "readFileChar" (-1), VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hGetChar handle <&> VChar))
  , (B.Variable nullSpan "readFileLine" (-1), VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hGetLine handle <&> VString))
  , (B.Variable nullSpan "isEOF" (-1), VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hIsEOF handle <&> hsToFstBool))
  , (B.Variable nullSpan "closeFile" (-1), VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hClose handle $> VUnit))

  , (B.Variable nullSpan "id" (-1), VBuiltin id)
  ] -}

-- | Convert Haskell's True and False into FreeST's value representation
hsToFstBool :: Bool -> Value
hsToFstBool True = VCons "True" []
hsToFstBool False = VCons "False" []

-- | Extract True and False from FreeST's value representation 
fstToHsBool :: Value -> Bool
fstToHsBool (VCons "True" []) = True
fstToHsBool (VCons "False" []) = False