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

import Syntax.Base (Variable)
import Syntax.Expression ( KindedExp, Pat )

-- | An environment, composed of bindings from variables to values
type Env = Map.Map Variable Value

data Value
  = VInt Int
  | VFloat Double
  | VUnit
  | VChar Char
  | VString String
  | VCons String [Value]
  | VClosure [Pat] KindedExp Env
  | VBuiltin (Value -> Value)
  | VIO (IO Value)
  | VHandle Handle
  | VLabel String
  | VFork
  | VChan ChannelEnd
  | VSelect String

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

showTups :: [Value] -> String
showTups [val] = show val
showTups (val:vals) = show val ++ " (-1), " ++ showTups vals

-- | Convert Haskell's True and False into FreeST's value representation
hsToFstBool :: Bool -> Value
hsToFstBool True = VCons "True" []
hsToFstBool False = VCons "False" []

-- | Extract True and False from FreeST's value representation
fstToHsBool :: Value -> Bool
fstToHsBool (VCons "True" []) = True
fstToHsBool (VCons "False" []) = False

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
  [
  -- * Undefined
    ("undefined",     VBuiltin undefined)
  -- * Error

  -- * Standard types, classes and related functions
  -- ** Basic datatypes
  -- *** Logical operators
  , ("(&&)",          VBuiltin (\x -> VBuiltin (\y -> hsToFstBool (fstToHsBool x && fstToHsBool y))))
  , ("(||)",          VBuiltin (\x -> VBuiltin (\y -> hsToFstBool (fstToHsBool x || fstToHsBool y))))
  -- *** Strings
  , ("ord",           VBuiltin (\(VChar c) -> VInt (ord c)))
  , ("chr",           VBuiltin (\(VInt x) -> VChar (chr x)))
  , ("(^^)",          VBuiltin (\(VString str1) -> VBuiltin (\(VString str2) -> VString (str1++str2))))
  , ("show",          VBuiltin (VString . show))
  -- ** Comparison
  , ("(<)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x < y))))
  , ("(<=)",          VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x <= y))))
  , ("(==)",          VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x == y))))
  , ("(>=)",          VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x >= y))))
  , ("(>)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x > y))))
  , ("(/=)",          VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x /= y))))
  , ("(>.)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x > y))))
  , ("(<.)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x < y))))
  , ("(>=.)",         VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x >= y))))
  , ("(<=.)",         VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x <= y))))
  -- ** Numeric functions
  -- *** Int
  , ("(+)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x + y))))
  , ("(-)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x - y))))
  , ("(*)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x * y))))
  , ("(/)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (div x y))))
  , ("(^)",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x ^ y))))
  , ("subtract",      VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (x - y))))
  , ("quot",          VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (quot x y))))
  , ("rem",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (rem x y))))
  , ("div",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (div x y))))
  , ("mod",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (mod x y))))
  , ("min",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (min x y))))
  , ("max",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (max x y))))
  , ("gcd",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (gcd x y))))
  , ("lcm",           VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> VInt (lcm x y))))
  , ("succ",          VBuiltin (\(VInt x) -> VInt (succ x)))
  , ("pred",          VBuiltin (\(VInt x) -> VInt (pred x)))
  , ("abs",           VBuiltin (\(VInt x) -> VInt (abs x)))
  , ("negate",        VBuiltin (\(VInt x) -> VInt (-x)))
  , ("even",          VBuiltin (\(VInt x) -> hsToFstBool (even x)))
  , ("odd",           VBuiltin (\(VInt x) -> hsToFstBool (odd x)))
  -- *** Float
  , ("(+.)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x + y))))
  , ("(-.)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x - y))))
  , ("(*.)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x * y))))
  , ("(/.)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x / y))))
  , ("(**)",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (x ** y))))
  , ("maxF",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (max x y))))
  , ("minF",          VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (min x y))))
  , ("logBase",       VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> VFloat (logBase x y))))
  , ("absF",          VBuiltin (\(VFloat x) -> VFloat (abs x)))
  , ("negateF",       VBuiltin (\(VFloat x) -> VFloat (negate x)))
  , ("recip",         VBuiltin (\(VFloat x) -> VFloat (recip x)))
  , ("exp",           VBuiltin (\(VFloat x) -> VFloat (exp x)))
  , ("log",           VBuiltin (\(VFloat x) -> VFloat (log x)))
  , ("sqrt",          VBuiltin (\(VFloat x) -> VFloat (sqrt x)))
  , ("log1p",         VBuiltin (\(VFloat x) -> VFloat (log1p x)))
  , ("expm1",         VBuiltin (\(VFloat x) -> VFloat (expm1 x)))
  , ("log1pexp",      VBuiltin (\(VFloat x) -> VFloat (log1pexp x)))
  , ("log1mexp",      VBuiltin (\(VFloat x) -> VFloat (log1mexp x)))
  , ("sin",           VBuiltin (\(VFloat x) -> VFloat (sin x)))
  , ("cos",           VBuiltin (\(VFloat x) -> VFloat (cos x)))
  , ("tan",           VBuiltin (\(VFloat x) -> VFloat (tan x)))
  , ("asin",          VBuiltin (\(VFloat x) -> VFloat (asin x)))
  , ("acos",          VBuiltin (\(VFloat x) -> VFloat (acos x)))
  , ("atan",          VBuiltin (\(VFloat x) -> VFloat (atan x)))
  , ("sinh",          VBuiltin (\(VFloat x) -> VFloat (sinh x)))
  , ("cosh",          VBuiltin (\(VFloat x) -> VFloat (cosh x)))
  , ("tanh",          VBuiltin (\(VFloat x) -> VFloat (tanh x)))
  , ("truncate",      VBuiltin (\(VFloat x) -> VInt (truncate x)))
  , ("round",         VBuiltin (\(VFloat x) -> VInt (round x)))
  , ("ceiling",       VBuiltin (\(VFloat x) -> VInt (ceiling x)))
  , ("floor",         VBuiltin (\(VFloat x) -> VInt (floor x)))
  , ("pi",            VFloat pi)
  , ("fromInteger",   VBuiltin (\(VInt x) -> VFloat (fromInteger (toInteger x))))
  -- * Concurrency
  , ("fork",          VFork)
  , ("send",          VBuiltin (\val -> VBuiltin (\(VChan c) -> VIO $ VChan <$> send val c)))
  , ("receive",       VBuiltin (\(VChan c) -> VIO $ receive c >>= \(val, c) -> return $ VCons "(,)" [val, VChan c]))
  , ("wait",          VBuiltin wait)
  , ("close",         VBuiltin (VIO . close))
  , ("send_",         undefined)
  , ("receive_",      undefined)
  -- * I/O
  -- ** Standard I/O
  -- *** stdin
  -- **** Internal stdin functions
  , ("internalGetChar",       undefined)
  , ("internalGetLine",       undefined)
  , ("internalGetContents",   undefined)
  , ("internalPutStrOut",     undefined)

  {- -- IO operators
  , ("readBool",              VBuiltin (\(VString str) -> hsToFstBool (read str)))
  , ("readInt",               VBuiltin (\(VString x) -> VInt (read x)))
  , ("readInt",               VBuiltin (\(VString c) -> VChar (read c)))
  -- Parser/Lexer does not accept variables starting with __
  , ("putStrOut",             VBuiltin (\val -> VIO $ putStr (show val) $> VUnit))
  , ("putStrErr",             VBuiltin (\val -> VIO $ hPutStr stderr (show val) $> VUnit))
  , ("getChar",               VIO $ getChar <&> VChar)
  , ("getLine",               VIO $ getLine <&> VString)
  , ("getContents",           VIO $ getContents <&> VString) -}
  {- , ("openFile",      VBuiltin (\(VString path) -> VBuiltin (\(VCons mode []) -> VIO $ case mode of
                        "ReadMode" -> openFile path ReadMode <&> VCons "FileHandle" . (:[]) . VHandle
                        "WriteMode" -> openFile path WriteMode <&> VCons "FileHandle" . (:[]) . VHandle
                        "AppendMode" -> openFile path AppendMode <&> VCons "FileHandle" . (:[]) . VHandle
                        _ -> undefined)))
  , ("putFileStr",    VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VBuiltin (\(VString str) -> VIO $ hPutStr handle str $> VUnit)))
  , ("readFileChar",  VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hGetChar handle <&> VChar))
  , ("readFileLine",  VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hGetLine handle <&> VString))
  , ("isEOF",         VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hIsEOF handle <&> hsToFstBool))
  , ("closeFile",     VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hClose handle $> VUnit)) -}
  ]