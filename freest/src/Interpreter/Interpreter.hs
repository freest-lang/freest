module Interpreter.Interpreter where

import Data.List ( find )
import Data.Char (chr, ord)
import Data.Functor ( ($>), (<&>), void )
import System.IO ( Handle, putStr, hPutStr, getChar, getLine, getContents, stderr, openFile, IOMode(..), hGetChar, hGetLine, hIsEOF, hClose )
import Control.Concurrent ( forkIO )
import Control.Concurrent.Chan as C
import GHC.Float
-- for debuging don't forget to remove
import Debug.Trace
-- ends here

import qualified Syntax.Module as M
import qualified Syntax.Expression as E
import qualified Syntax.Base as B
import Syntax.Expression ( LetDecl )

type ChannelEnd = (C.Chan Value, C.Chan Value)

data Value = VInt Int
            | VFloat Double
            | VUnit 
            | VChar Char
            | VString String
            | VCons String [Value]
            -- | VTuple [Value]
            | VFun [([E.Pat], E.RHS)]
            | VClosure [E.Pat] E.Exp Context
            | VBuiltin (Value -> Value)
            | VIO (IO Value)
            | VHandle Handle
            | VLabel String
            | VFork
            | VChan ChannelEnd

instance Show Value where
  show VUnit = "()"
  show (VInt n) = show n
  show (VFloat n) = show n
  show (VChar c) = show c
  show (VString str) = show str
  show (VCons str vals) = str ++ " " ++ unwords (map show vals)
  -- show (VTuple tups) = "(" ++ showTups tups ++ ")"
  show (VFun _) = "<fun>"
  show (VClosure _ _ _) = "closure>"
  show (VBuiltin _) = "<builtin>"
  show (VIO io) = "<IO>"
  show (VHandle _) = "<handle>"
  show (VLabel str) = "<label> string"
  show (VChan _) = "<chan>"

showTups :: [Value] -> String
showTups [val] = show val
showTups (val:vals) = show val ++ ", " ++ showTups vals

tupToList :: (a,a) -> [a]
tupToList (x, y) = [x, y]

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
  val <- C.readChan (fst c)
  return $ (\(VLabel str) -> str) val

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

builtins :: [(String , Value)]
builtins = [
  ("receive", VBuiltin (\(VChan c) -> VIO $ receive c >>= \(val, c) -> return $ VCons "(,)" [val, VChan c])),
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
  ("even", VBuiltin (\(VInt x) -> hsToFstBool (even x))),
  ("odd", VBuiltin (\(VInt x) -> hsToFstBool (odd x))),
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
  
  ("(&&)", VBuiltin (\x -> VBuiltin (\y -> hsToFstBool (fstToHsBool x && fstToHsBool y)))),
  ("(||)", VBuiltin (\x -> VBuiltin (\y -> hsToFstBool (fstToHsBool x || fstToHsBool y)))),

  ("(==)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x == y)))),
  ("(/=)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x /= y)))),
  ("(>)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x > y)))),
  ("(>=)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x >= y)))),
  ("(<)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x < y)))),
  ("(<=)", VBuiltin (\(VInt x) -> VBuiltin (\(VInt y) -> hsToFstBool (x <= y)))),
  ("(>.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x > y)))),
  ("(>=.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x >= y)))),
  ("(<.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x < y)))),
  ("(<=.)", VBuiltin (\(VFloat x) -> VBuiltin (\(VFloat y) -> hsToFstBool (x <= y)))),

  ("chr", VBuiltin (\(VInt x) -> VChar (chr x))),
  ("ord", VBuiltin (\(VChar c) -> VInt (ord c))),

  ("(^^)", VBuiltin (\(VString str1) -> VBuiltin (\(VString str2) -> VString (str1++str2)))),

  ("show", VBuiltin (VString . show)),
  ("readBool", VBuiltin (\(VString str) -> hsToFstBool (read str))),
  ("readInt", VBuiltin (\(VString x) -> VInt (read x))),
  ("readInt", VBuiltin (\(VString c) -> VChar (read c))),

  -- Parser/Lexer does not accept variables starting with __
  ("putStrOut", VBuiltin (\val -> VIO $ putStr (show val) $> VUnit)),
  ("putStrErr", VBuiltin (\val -> VIO $ hPutStr stderr (show val) $> VUnit)),
  ("getChar", VIO $ getChar <&> VChar),
  ("getLine", VIO $ getLine <&> VString),
  ("getContents", VIO $ getContents <&> VString),

  ("openFile", VBuiltin (\(VString path) -> VBuiltin (\(VCons mode []) -> VIO $ case mode of
    "ReadMode" -> openFile path ReadMode <&> VCons "FileHandle" . (:[]) . VHandle
    "WriteMode" -> openFile path WriteMode <&> VCons "FileHandle" . (:[]) . VHandle
    "AppendMode" -> openFile path AppendMode <&> VCons "FileHandle" . (:[]) . VHandle
    _ -> undefined))),
  ("putFileStr", VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VBuiltin (\(VString str) -> VIO $ hPutStr handle str $> VUnit))),
  ("readFileChar", VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hGetChar handle <&> VChar)),
  ("readFileLine", VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hGetLine handle <&> VString)),
  ("isEOF", VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hIsEOF handle <&> hsToFstBool)),
  ("closeFile", VBuiltin (\(VCons "FileHandle" [VHandle handle]) -> VIO $ hClose handle $> VUnit)),
  
  ("id", VBuiltin id)]

-- haskell bool to freest bool
hsToFstBool :: Bool -> Value
hsToFstBool True = VCons "True" []
hsToFstBool False = VCons "False" []

-- freeST bool to haskell bool 
fstToHsBool :: Value -> Bool
fstToHsBool (VCons "True" []) = True
fstToHsBool (VCons "False" []) = False

-- Using a simple context for now for simplicity
-- TODO: change to a hashmap
type Context = [(String, Value)]

interpret :: M.Module -> IO Value
interpret m = case getMainFunction m of
  -- Assuming that the RHS of main is always in the form main = <exp>
  -- necessary to initialize the context with information from the module
  -- other modules, prelude, etc
  Just (E.ValDecl _ (E.UnguardedRHS mainExp _)) -> do initial_ctx <- initContext m
                                                      eval (initial_ctx ++ builtins, []) mainExp
  -- Return unit when main function is not present
  Nothing -> do return VUnit

getMainFunction :: M.Module -> Maybe LetDecl 
getMainFunction m = find foo (M.definitions m)
  -- main should be a ValDecl VarPat because it is the form main = <body>
  where foo funDef = case funDef of E.ValDecl (E.VarPat _ var) _ -> B.external var == "main"  
                                    _ -> False

-- For now add only definitions to the context.  
initContext :: M.Module -> IO Context
initContext m =
  -- is VarPat the only valid pattern in a valDecl??
  -- the same for the rhs UnguardedRHS
  sequence $ map (\def -> case def of E.ValDecl (E.VarPat _ var) (E.UnguardedRHS exp _) -> do initial_ctx <- eval (builtins, []) exp
                                                                                              return (B.external var,  initial_ctx)
                                      E.FnDecl var fun -> do return $ (B.external var, VFun (map (\(levels, rhs) -> ((map (\(B.ExpLevel pat) -> pat) (filterTypesFromLevels levels)), rhs)) fun))
  -- do not add main to the context
  ) (filter (\def -> case def of E.ValDecl (E.VarPat _ var) _ -> B.external var /= "main" 
                                 E.SigDecl _ _ -> False
                                 _ -> True)
    (M.definitions m))

-- TODO: eval can failed (pattern matching so the return value should be Either [IOE.Error] Value)
-- Global and local context
eval :: (Context, Context) -> E.Exp -> IO Value
eval _ (E.Int _ n) = return $ VInt n 
eval _ (E.Float _ n) = return $ VFloat n
eval _ (E.Char _ c) = return $ VChar c
-- eval _ (E.String _ str) = return $ VString str
-- [Exp] -> [Value]
-- eval ctx (E.Tuple _ tup) = do
--   vals <- sequence $ map (eval ctx) tup
--   return $ VTuple vals 
eval _ (E.Cons _ (B.Identifier _ str)) = return $ VCons str []
eval ctx (E.Var _ var) = case getVar ctx var of VIO io -> io
                                                val -> return val
eval (global, local) (E.App _ exp levels) = do
  args <- sequence $ map (\(B.ExpLevel exp) -> eval (global, local) exp) (filterTypesFromLevels levels)
  left <- (eval (global, local) exp)
  case left of
    VFork -> forkIO (void $ consumeAllArgs (global, []) (head args) [VUnit]) $> VUnit
    _ -> do res <- consumeAllArgs (global, local) left args
            case res of
              VIO io -> io
              _ -> return res
eval (_, local) (E.Abs _ levels _ exp) = return $ VClosure (map (\(B.ExpLevel (pat, _)) -> pat) (filterTypesFromLevels levels)) exp local
eval (global, local) (E.Let _ letDecls exp) = do
  letDeclsCtx <- resolveLetDecls global (filterTypesFromLetDecls letDecls)
  eval (global, letDeclsCtx ++ local) exp
eval (global, local) (E.Case _ exp pats) = do
  val <- (eval (global, local) exp)
  labels <- mapM receiveLabel $ getInternalChoiceChannels [fst $ head pats] [val]
  case chooseCase pats val labels of
    Just (exp, matched) -> eval (global, matched ++ local) exp 
  -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
    Nothing -> undefined
eval ctx (E.If _ ifExp thenExp elseExp) = do
  ifVal <- (eval ctx ifExp)
  thenVal <- eval ctx thenExp
  elseVal <- eval ctx elseExp
  if fstToHsBool ifVal then return thenVal else return elseVal
eval _ (E.Channel _ _) = do
  (chanL, chanR) <- chan
  return $ VCons ("(,)") [VChan chanL, VChan chanR]
eval ctx (E.Select _ (B.Identifier _ iden) chan) = do
  VChan chan2 <- eval ctx chan
  chan3 <- send (VLabel iden) chan2
  return $ VChan chan3

getVar :: (Context, Context) -> B.Variable -> Value
getVar _ (B.Variable {B.varSpan=_, B.internal=_, B.external="fork"}) = VFork
getVar (global, local) var = case find (\(var2, val) -> B.external var == var2) local of
  Just (var, val) -> val
  Nothing -> case find (\(var2, val) -> B.external var == var2) global of
    Just (var, val) -> val
    Nothing -> error ("Variable `" ++ show var ++ "`not found in the context. This should not happen. This is a bug in the compiler")

-- removes the type arguments (i.e. @Int) from arguments
filterTypesFromLevels :: [B.Level a b] -> [B.Level a b]
filterTypesFromLevels = filter (\level -> case level of B.ExpLevel a -> True
                                                        B.TypeLevel b -> False) 

filterTypesFromLetDecls :: [LetDecl] -> [LetDecl]
filterTypesFromLetDecls = filter (\letDecl -> case letDecl of E.ValDecl _ _ -> True
                                                              E.FnDecl _ _ -> True
                                                              E.SigDecl _ _ -> False)

-- Here is where the function application is done.
-- Because of how the parser parses function applications (f a b c d => f [a, b, c, d] even if f only takes one arg)
-- is necessary to repeat the evaluation until [arg] is empty.
-- TODO: context is a mess must check if it is correct, don't like that there is a lot of repetition
consumeAllArgs :: (Context, Context) -> Value -> [Value] -> IO Value
consumeAllArgs (global, local) (VClosure pats exp local_ctx) args = case sequence (doPatternMatching pats args []) of
  Just patternMatching ->
    if length pats == length args then eval (global, patternMatching ++ local_ctx ++ local) exp
    else if length pats < length args then do val <- (eval (global, patternMatching ++ local_ctx ++ local) exp)
                                              consumeAllArgs (global, patternMatching ++ local_ctx ++ local) val (drop (length pats) args)
    else return $ VClosure (drop (length args) pats) exp (patternMatching ++ local_ctx) 
  -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
  Nothing -> undefined
consumeAllArgs (global, local) (VFun patExps) args = do
  labels <- mapM receiveLabel $ getInternalChoiceChannels (fst $ head patExps) args
  case chooseRhs patExps args labels of
    Just (rhs, matched, pats) ->
      do (exp, whereDecls) <- (case rhs of E.UnguardedRHS exp whereDecls -> return (exp, whereDecls)
                                           E.GuardedRHS predExps whereDecls -> do guardsCtx <- chooseGuard (global, matched) predExps
                                                                                  return (guardsCtx, whereDecls))
         let whereCtx = (case whereDecls of Just letDecls -> resolveLetDecls global letDecls
                                            Nothing -> return [])
         whereCtx2 <- whereCtx
         if length pats == length args then eval (global, matched++whereCtx2) exp 
         else if length pats < length args then do val <- (eval (global, matched++whereCtx2) exp)
                                                   consumeAllArgs (global, matched++whereCtx2) val (drop (length pats) args)
         else return $ VClosure (drop (length args) pats) exp (matched++whereCtx2)
    -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
    Nothing -> undefined
-- Is there builtins that take no arguments?
consumeAllArgs ctx (VBuiltin builtin) [] = return $ builtin VUnit
consumeAllArgs ctx (VBuiltin builtin) [arg] = return $ builtin arg
consumeAllArgs ctx (VBuiltin builtin) (arg:args) = consumeAllArgs ctx (builtin arg) args

consumeAllArgs ctx (VCons str vals) args = return $ VCons str (vals++args) 

-- TODO: think of a better name for this function
resolveLetDecls :: Context -> [LetDecl] -> IO [(String, Value)]
resolveLetDecls _ [] = return []
resolveLetDecls global ((E.ValDecl pat rhs):letDecls) = do
  (exp, whereDecls) <- case rhs of E.UnguardedRHS exp whereDecls -> return (exp, whereDecls)
                                   E.GuardedRHS predExps whereDecls -> do guardsCtx <- chooseGuard (global, []) predExps
                                                                          return (guardsCtx, whereDecls)
  whereCtx2 <- (case whereDecls of Just letDecls -> resolveLetDecls global letDecls
                                   Nothing -> return [])
  val <- eval (global, whereCtx2) exp
  letDeclsCtx <- resolveLetDecls global letDecls
  return $ case sequence $ doPatternMatching [pat] [val] [] of
    Just matched -> matched ++ letDeclsCtx
  -- TODO: use freeST error handling to tell the user that that pattern mathcing was not exhautive
    Nothing -> undefined

resolveLetDecls global ((E.FnDecl var levelRhss):letDecls) = do
  letDeclsCtx <- resolveLetDecls global letDecls 
  return $ (B.external var, VFun (map (\(levels, rhs) -> (map (\(B.ExpLevel pat) -> pat) (filterTypesFromLevels levels), rhs)) levelRhss)) : letDeclsCtx

-- TODO: create a resolveWhereDecls for more readable code (Context -> Maybe [LetDecl] -> [(String, Value)])

-- TODO: refactor to use map and filter?
-- do i need to do Nothing : doPatternMatching pats args or can i just return Nothing
doPatternMatching :: [E.Pat] -> [Value] -> [String] -> [Maybe (String, Value)]
doPatternMatching [] [] _ = []
doPatternMatching pats [] _ = []
doPatternMatching [] args _ = []
doPatternMatching (pat:pats) (arg:args) labels = case pat of
  E.WildPat _ _ -> doPatternMatching pats args labels
  E.VarPat _ var -> Just (B.external var, arg) : doPatternMatching pats args labels
  E.ConsPat _ (B.Identifier _ patIden) consPats -> case arg of
    VCons iden consArgs -> if iden == patIden then doPatternMatching consPats consArgs labels ++ doPatternMatching pats args labels else Nothing : doPatternMatching pats args labels
    VChan chan -> if patIden == head labels then Just (B.external $ (\[E.VarPat _ var] -> var) consPats, VChan chan) : doPatternMatching pats args (tail labels) else Nothing : doPatternMatching pats args (tail labels)
  -- E.TuplePat _ tupPats -> doPatternMatching tupPats ((\(VTuple tupVals) -> tupVals) arg) ++ doPatternMatching pats args
  E.IntPat _ n -> if (\(VInt n) -> n) arg == n then doPatternMatching pats args labels else Nothing : doPatternMatching pats args labels
  E.FloatPat _ n -> if (\(VFloat n) -> n) arg == n then doPatternMatching pats args labels else Nothing : doPatternMatching pats args labels
  E.CharPat _ c -> if (\(VChar c) -> c) arg == c then doPatternMatching pats args labels else Nothing : doPatternMatching pats args labels
  -- E.StringPat _ str -> if (\(VString str) -> str) arg == str then doPatternMatching pats args else Nothing : doPatternMatching pats args
  E.AsPat _ var pat2 -> Just (B.external var, arg) : doPatternMatching [pat2] [arg] labels ++ doPatternMatching pats args labels

-- necessary to find out if there is an internal choice in the pattern matching to pre receive the label
getInternalChoiceChannels :: [E.Pat] -> [Value] -> [ChannelEnd]
getInternalChoiceChannels [] [] = []
getInternalChoiceChannels pats [] = []
getInternalChoiceChannels [] args = []
getInternalChoiceChannels (pat:pats) (arg:args) = case pat of
  E.ConsPat _ (B.Identifier _ patIden) patCons -> case arg of
    VCons _ consArgs -> getInternalChoiceChannels patCons consArgs ++ getInternalChoiceChannels pats args
    VChan chan -> chan : getInternalChoiceChannels pats args
  _  -> getInternalChoiceChannels pats args

chooseRhs :: [([E.Pat], E.RHS)] -> [Value] -> [String] -> Maybe (E.RHS, [(String, Value)], [E.Pat])
chooseRhs [] _ _ = Nothing
chooseRhs ((pats, rhs):rest) args labels = case sequence $ doPatternMatching pats args labels of
  Just matching -> Just (rhs, matching, pats)
  Nothing -> chooseRhs rest args labels

chooseCase :: [(E.Pat, E.Exp)] -> Value -> [String] -> Maybe (E.Exp, [(String, Value)])
chooseCase [] _ _ = Nothing
chooseCase ((pat, exp):patsExps) val labels = case doPatternMatching [pat] [val] labels of
  [] -> Just (exp, [])
  [Just (var, val)] -> Just (exp, [(var, val)])
  [Nothing] -> chooseCase patsExps val labels

chooseGuard :: (Context, Context) -> [(E.Exp, E.Exp)] -> IO E.Exp
-- TODO: error for no exaustive guards
chooseGuard _ [] = undefined 
chooseGuard ctx ((pred, exp):predExps) = do
  val <- eval ctx pred
  if fstToHsBool val then return exp else chooseGuard ctx predExps
