module LeaST.Typing where

import LeaST.LeaST qualified as L
import Syntax.Kind qualified as K
import qualified Syntax.Type as T
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

-- Var B.Variable   --x
-- Lit Literal      --1
-- Abs B.Variable T.Type Exp --\x:Int -> x 
-- App Exp Exp  -- (\x:Int -> + x x) 2
-- Con B.Identifier --n fazer
-- Case Exp [(Alt, Exp)] --n fazer
-- Type T.Type --n fazer
-- TAbs B.Variable K.Kind Exp   --  (\@a:*T -> (\x:B -> x))
-- TApp Exp Type  -- (\@a:*T -> (\x:B -> x)) @Int


-- | Synthesis for expressions. Given kind and type contexts, it synthesizes 
-- the type of an expression, returning its type and the updated type context 
-- without the linear variables consumed in it.
synth :: KindCtx -> TypeCtx -> Exp -> Validation (T.Type, TypeCtx)
synth kctx tctx = \case
-- Lit Literal
  Lit l         -> (typeOf l, tctx) 
-- Var B.Variable
  Var s x       -> lookupType kctx tctx (Left  x)
-- Abs B.Variable T.Type Exp
  Abs x t e     -> do
    Kinding.checkProper kctx t
    (u, tctx') <- synth kctx (Map.insert x t tctx) e 
    return (AppArrow B.nullSpan K.Un t u, difference kctx tctx x) --NOTA abstração 
-- App Exp Exp   
  App e f    -> do
    (t, tctx') <- synth kctx tctx e
    AppArrow _ _ t' u <- Expose.typeArrow e t
    tctx'' <- check kctx tctx' f t'  
    return (u, tctx'')  
-- Con B.Identifier --n fazer
-- Case Exp [(Alt, Exp)] --n fazer
-- Type T.Type --n fazer
-- TAbs B.Variable K.Kind Exp  
  TAbs a k e -> do
    (t, tctx') <- synth (Map.insert a k kctx) tctx e
    return (AppForall B.nullSpan [(a, k)] t, tctx')
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
    Kinding.checkProper kctx t'   
    AppArrow _ _ t1 t2 <- Expose.typeArrow e t
    checkEquivTypes t' t1
    (t3, tctx') <- synth kctx tctx x 
    checkEquivTypes t2 t3
    return difference kctx tctx x 
-- TAbs B.Variable K.Kind Exp
  TAbs a k e'  -> do
    AppForall _ ts t' <- Expose.typeArrow e' t  
    tctx' <- check (Map.insert a k kctx) tctx e' t'
    return tctx'
-- remaining cases
  _ -> do
    (u, tctx') <- synth kctx tctx e
    checkEquivTypes e t u
    return tctx'


typeOf :: Literal -> T.Type
typeOf (LInt _)   = Int B.nullSpan
typeOf (LFloat _) = Float B.nullSpan
typeOf (LChar _)  = Char B.nullSpan

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


difference :: KindCtx -> TypeCtx -> B.Variable -> Validation TypeCtx
difference kctx tctx v = case tctx Map.!? v of
  Just t -> do
    k <- Kinding.synth kctx t
    return (if K.isStrictlyLin k then Map.delete v tctx else tctx)
  Nothing -> throwE (VarOutOfScope (getSpan v) v)   
--TODO deixo o getSpan ou troco já por nullSpan?

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