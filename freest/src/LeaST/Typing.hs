module LeaST.Typing where

import LeaST.LeaST qualified as L
import qualified Syntax.Base as B
import Validation.Kinding qualified as Kinding

import qualified Data.Map.Strict as Map
import Debug.Trace

-- The type context. It keeps track of the variables and constructors in scope
-- and their types.
type TypeCtx = Map.Map (Either Variable Identifier) T.Type

-- The kind context. It keeps track of the type variables in scope and their 
-- kinds.
type KindCtx = Map.Map Variable K.Kind

type Error = String

-- Var B.Variable   --x
-- Lit Literal      --1
-- Abs B.Variable T.Type Exp --\x:Int -> x 
-- App Exp Exp  -- (\x:Int -> + x x) 2
-- Con B.Identifier --n fazer
-- Case Exp [(Alt, Exp)] --n fazer
-- Type T.Type --n fazer
-- TAbs B.Variable K.Kind Exp   --  (\@a:*T -> (\x:B -> x))
-- TApp Exp Type  -- (\@a:*T -> (\x:B -> x)) @Int


-- TODO Funcção copiada do FreeST, trocar
-- | Synthesis for expressions. Given kind and type contexts, it synthesizes 
-- the type of an expression, returning its type and the updated type context 
-- without the linear variables consumed in it.
synth :: KindCtx -> TypeCtx -> Exp -> Validation (T.Type, TypeCtx)
synth kctx tctx = \case
-- Lit Literal
  Lit l         -> (typeOf l, tctx)   -- este typeOf ou outra função? (TODO prob outra)
{- maneira em Fst
  Int s _       -> pure (T.Int s   , tctx)
  Float s _     -> pure (T.Float s , tctx)
  Char s _      -> pure (T.Char s  , tctx)
-}
-- Var B.Variable
  Var s x       -> lookupType kctx tctx (Left  x)
  --TODO Tlin e Tun ?
-- Abs B.Variable T.Type Exp
  Abs x t e     -> do
    Kinding.checkProper kctx t
    (u, tctx') <- synth kctx tctx e -- TODO ?n sei se é x ou e
    return (t, typeCtxDifference kctx tctx tctx')  --como construir t->u? criar um Expose.typeArrow? + estou a fazer o cnt%x bem?
-- App Exp Exp --fazer
  App e f    -> do
    (t, tctx') <- synth kctx tctx e
    AppArrow _ _ t' u <- Expose.typeArrow e t
    -- e:T? alterar o Map? (ou seja, tctx)
    return (u, tctx'')  --TODO tctx'' é criado na linha acima, ainda n feito
-- Con B.Identifier --n fazer
-- Case Exp [(Alt, Exp)] --n fazer
-- Type T.Type --n fazer
-- TAbs B.Variable K.Kind Exp  --fazer
  TAbs a k e -> do
    (t, tctx') <- synth kctx tctx e --ñ sei se é isto
    return (t, tctx') --isto também está mal
-- TApp Exp Type  --fazer
  --NOTA: Ainda não está feito na main


-- | Check-against for expressions. Given kind and type contexts, it checks
-- whether an expression has a given type, throwing an error if it does not.
-- Returns the updated type context without the linear variables consumed in 
-- the expression.
check :: KindCtx -> TypeCtx -> Exp -> T.Type -> Validation TypeCtx
check kctx tctx e t = gets typeDecls >>= \tds -> case e of
-- Abs B.Variable T.Type Exp 
  Abs x t' e'  -> do
    Kinding.checkProper kctx t'   --TODO Verificar se isto está bem
    AppArrow _ _ t1 t2 <- Expose.typeArrow e t
    -- TODO, ver como mandar o erro correto, ou se ser Validation chega
    -- case Expose.typeArrow e t of
    --  _ -> throwE (TypeMismatch s t u (Left e))
    checkEquivTypes t' t1
    (t3, tctx') <- synth kctx tctx x 
    checkEquivTypes t2 t3
    return typeCtxDifference kctx tctx tctx' --TODO como assim %x? estou a usar isto bem?
-- TAbs B.Variable K.Kind Exp
  TAbs a k e'  -> do
    AppForall _ t' <- Expose.typeArrow e t  --[(Variable, K.Kind)]
    -- tctx' <- ? chamada ao check e'? o que é o Q:k?
    return tctx'
-- remaining cases
  _ -> do
    (u, tctx') <- synth kctx tctx e
    checkEquivTypes e t u
    return tctx'


-- NOTA: Tirado do Fst, adaptado
-- | Type equivalence. Checks if two types are equivalent, throwing an error
-- if they are not. An expression or pattern is provided to locate the error.
checkEquivTypes :: Exp -> T.Type -> T.Type -> Validation ()
checkEquivTypes eop t1 t2 = do
  tds <- gets typeDecls
  unless (equivalent tds t1 t2) $
    throwE (TypeMismatch (getSpan eop) t1 t2 (Left eop))



-- NOTA: usar para o %, mas de contextos
-- | The context difference operation. Removes the variables in the first type 
-- context from the second type context, throwing an error for any strictly
-- linear variable it encounters. To be used at the end of a scope.
typeCtxDifference :: KindCtx -> TypeCtx -> TypeCtx -> Validation TypeCtx
typeCtxDifference kctx tctx1 tctx2 = do
  foldM (\tctx1' x -> case tctx1 Map.!? x of
      Just t  -> do
        whenM (K.isStrictlyLin <$> Kinding.synth kctx t) $
          throwE (LinVarAtEndOfScope (getSpan x) x t)
        return (Map.delete x tctx1')
      Nothing -> return tctx1'
    ) tctx1 (Map.keys tctx2)

-- NOTA: usar para o % em tipos
-- | Looks up the type of a variable or identifier in a type context,
-- returning its type and the updated type context. If the type is strictly
-- linear, then the variable or identifier will not be present in the updated 
-- type context. If the variable or identifier is not present in the type 
-- context, an error is thrown.
lookupType :: KindCtx -> TypeCtx -> Either Variable Identifier -> Validation (T.Type, TypeCtx)
lookupType kctx tctx xi = case tctx Map.!? xi of
  Just t -> do
    k <- Kinding.synth kctx t
    return (t, if K.isStrictlyLin k then Map.delete xi tctx else tctx)
  Nothing -> case xi of
    Left  x -> throwE (VarOutOfScope (getSpan x) x)
    Right i -> throwE (ConsOutOfScope (getSpan i) i)