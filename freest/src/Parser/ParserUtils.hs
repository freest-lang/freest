module Parser.ParserUtils where

import Parser.Token
import Parser.LexerUtils
import Syntax.Base
import Syntax.Names
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import qualified Syntax.Type as T

freshKVar :: Located a => a -> Lexer K.Kind
freshKVar l = do
  i1 <- incCounter
  i2 <- incCounter
  let s = getSpan l 
  return $ K.Proper s (K.VarM  (Variable s ("φ"++show i1) i1)) 
                      (K.VarPK (Variable s ("ψ"++show i2) i2))

split :: Eq a => a -> [a] -> [[a]]
split d str =
  case break (==d) str of
    (a, _:b) -> a : split d b
    (a, _)   -> [a]

mkVarTk :: Token -> Variable
mkVarTk t = mkVar t (getText t)

infixApp :: T.Type -> T.Type -> T.Type -> T.Type
infixApp t1 op t2 = T.App (spanFromTo t1 t2) op [t1, t2]

tupleAppType :: Span -> [T.Type] -> T.Type
tupleAppType s ts =
  T.App s (T.Name s (Variable s ("("++replicate (length ts) ',' ++")") (-1))) ts

binOp :: E.Exp -> Variable -> E.Exp -> E.Exp
binOp l op r = E.App (spanFromTo l r) (E.Var (getSpan op) op) [E.EArg l, E.EArg r]

unOp :: Variable -> E.Exp -> E.Exp
unOp op x = E.App (spanFromTo op x) (E.Var (getSpan op) op) [E.EArg x]

tupleAppExp :: Span -> [E.Exp] -> E.Exp
tupleAppExp s es = E.App s (E.Var s (mkTupleCons (length es) s)) (map E.EArg es)

consAppExp :: Span -> [E.Exp] -> E.Exp
consAppExp s = foldr (\e l -> E.App s (E.Var s $ mkCons s) (map E.EArg [e,l])) (E.Var s (mkNil s))

addArgExp :: E.Arg -> E.Exp -> E.Exp 
addArgExp a (E.App s e as) = E.App s e (as++[a])
addArgExp a e              = E.App (spanFromTo e a) e [a]

addArgType :: T.Type -> T.Type -> T.Type
addArgType a (T.App s t as) = T.App s t (as++[a])
addArgType a t              = T.App (spanFromTo t a) t [a]