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
infixApp t1 op t2 = T.App (spanFromTo t1 t2) (T.App (spanFromTo t1 op) op t1) t2

tupleAppType :: Span -> [T.Type] -> T.Type
tupleAppType s (t:ts) =
  foldr (\t a -> T.App (spanFromTo a t) a t)
        (T.App s (T.Name s (Variable s ("("++replicate (length ts) ',' ++")") (-1))) t)
        ts
tupleAppType _ _ = error "empty list"

binOp :: E.Exp -> Variable -> E.Exp -> E.Exp
binOp l op r = E.App (spanFromTo l r) (E.App (spanFromTo l op) (E.Var (getSpan op) op) l) r

unOp :: Variable -> E.Exp -> E.Exp
unOp op x = E.App (spanFromTo op x) (E.Var (getSpan op) op) x

tupleAppExp :: Span -> [E.Exp] -> E.Exp
tupleAppExp s (e:es) =
  foldl (\a e -> E.App (spanFromTo a e) a e)
        (E.App s (E.Var s (mkTupleCons (length es) s)) e)
        es
tupleAppExp _ _ = error "empty list"

consAppExp :: Span -> [E.Exp] -> E.Exp
consAppExp s = foldr (E.App s . E.App s (E.Var s (mkCons s))) (E.Var s (mkNil s))
