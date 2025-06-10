module LeaST.Typing where

import LeaST.LeaST qualified as L
import Syntax.Kind qualified as K
import qualified Syntax.Type as T
import qualified Syntax.Base as B
import Validation.Base
import Utils
import Validation.Expose qualified as Expose
import Validation.Kinding qualified as Kinding
import Validation.Typing qualified as Typing
import Validation.Substitution ( subs, subsAll )
import Control.Monad.Trans.Except ( catchE, throwE )


import UI.Error

import qualified Data.Map.Strict as Map
import Debug.Trace


--TODO importar isto
-- The type context. It keeps track of the variables and constructors in scope
-- and their types.
type TypeCtx = Map.Map (Either B.Variable B.Identifier) T.Type

-- The kind context. It keeps track of the type variables in scope and their 
-- kinds.
type KindCtx = Map.Map B.Variable K.Kind

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
synth :: KindCtx -> TypeCtx -> L.Exp -> Validation (T.Type, TypeCtx)
synth kctx tctx = \case
-- Lit Literal
  L.Lit l         -> pure (typeOf l, tctx)
-- Var B.Variable
  L.Var x       -> Typing.lookupType kctx tctx (Left  x)
-- Abs B.Variable T.Type Exp
  L.Abs x t e     -> do
    Kinding.checkProper kctx t
    (u, tctx') <- synth kctx (Map.insert (Left x) t tctx) e 
    return (T.AppArrow B.nullSpan K.Un t u, difference kctx tctx x) --NOTA abstração 
-- App Exp Exp   
  L.App e f    -> do
    (t, tctx') <- synth kctx tctx e
    T.AppArrow _ _ t' u <- Expose.typeArrow e t
    tctx'' <- check kctx tctx' f t'  
    return (u, tctx'')  
-- Con B.Identifier 
  L.Con i        -> do
    (i', vsks, ts) <- Typing.lookupDConsDecl i --vsks = [(var,kind)] 
    return (T.DName B.nullSpan i', tctx) --TODO i? i'? o 1º tipo?
-- Case Exp [(Alt, Exp)]
  L.Case e ((a, e') : rest) -> do
    (t, tctx') <- synth kctx tctx e
    -- TODO tenho de tirar o identifier do alt?
    (i', vsks, ts) <- Typing.lookupDConsDecl i
    -- extract  lookupDConsDecl
    -- data  E.DConsPat
    -- check várias vezes? e T[U/a] 
    -- synth com o ctx anterior
    -- fold a comparar o 1 elem dos tipos com os restantes
    -- fold a comparar o 1 elem dos ctxs com os restantes
    -- return (1elem tipos, 1elem ctxs)
    return (t, tctx')
-- TAbs B.Variable K.Kind Exp  
  L.TAbs a k e -> do
    (t, tctx') <- synth (Map.insert (Left a) k kctx) tctx e
    return (T.AppForall B.nullSpan [(a, k)] t, tctx')
-- TApp Exp Type 
  L.TApp e t -> do
    (t', tctx') <- synth kctx tctx e
    T.AppForall _ [(v,k)] t'' <- Expose.typeArrow e t'  --[(var,kind)] 
    Kinding.check kctx k t 
    return (subs v t t'', tctx')  --TODO verificar se estou a usar bem T3[a->T1]


-- | Check-against for expressions. Given kind and type contexts, it checks
-- whether an expression has a given type, throwing an error if it does not.
-- Returns the updated type context without the linear variables consumed in 
-- the expression.
check :: KindCtx -> TypeCtx -> L.Exp -> T.Type -> Validation TypeCtx
check kctx tctx e t = case e of 
-- Abs B.Variable T.Type Exp 
  L.Abs x t' e'  -> do
    Kinding.checkProper kctx t'   
    T.AppArrow _ _ t1 t2 <- Expose.typeArrow e t
    Typing.checkEquivTypes (Left e') t' t1   
    (t3, tctx') <- synth kctx tctx x 
    Typing.checkEquivTypes (Left e') t2 t3   
    return $ difference kctx tctx x 
-- TAbs B.Variable K.Kind Exp
  L.TAbs a k e'  -> do
    T.AppForall _ _ t' <- Expose.typeArrow e' t  --[(var,kind)]
    tctx' <- check (Map.insert a k kctx) tctx e' t'
    return tctx'
-- remaining cases
  _ -> do
    (u, tctx') <- synth kctx tctx e
    Typing.checkEquivTypes (Left e) t u
    return tctx'


checkAlt :: KindCtx -> TypeCtx -> L.Alt -> T.Type -> Validation TypeCtx
check kctx tctx e t = case e of 
-- ACon B.Identifier [B.Variable]
  L.ACon i vs -> do
    -- TODO x distinct
    (i', vsks, ts) <- Typing.lookupDConsDecl i --vsks = [(var,kind)] 
    -- TODO comparar tamanho entre x e ts?
    return tctx -- TODO tctx|x:T ??
-- ALit Literal
  L.ALit l -> do
    (t', tctx') <- synth l
    Typing.checkEquivTypes (Left e) t t'
    return tctx' 
-- AWildCard
  L.AWildCard -> return (tctx)


typeOf :: L.Literal -> T.Type
typeOf (L.LInt _)   = T.Int B.nullSpan
typeOf (L.LFloat _) = T.Float B.nullSpan
typeOf (L.LChar _)  = T.Char B.nullSpan


-- NOTA: usar para o %, mas de contextos
-- typeCtxDifference :: KindCtx -> TypeCtx -> TypeCtx -> Validation TypeCtx
-- typeCtxDifference kctx tctx1 tctx2 = do
--   foldM (\tctx1' x -> case tctx1 Map.!? x of
--       Just t  -> do
--         whenM (K.isStrictlyLin <$> Kinding.synth kctx t) $
--           throwE (LinVarAtEndOfScope (getSpan x) x t)
--         return (Map.delete x tctx1')
--       Nothing -> return tctx1'
--     ) tctx1 (Map.keys tctx2)


-- -- NOTA: Tirado do Fst, adaptado
-- -- | Type equivalence. Checks if two types are equivalent, throwing an error
-- -- if they are not. An expression or pattern is provided to locate the error.
-- checkEquivTypes :: Exp -> T.Type -> T.Type -> Validation ()
-- checkEquivTypes eop t1 t2 = do
--   tds <- gets typeDecls
--   unless (equivalent tds t1 t2) $
--     throwE (TypeMismatch (getSpan eop) t1 t2 (Left eop))



difference :: KindCtx -> TypeCtx -> B.Variable -> Validation TypeCtx
difference kctx tctx v = case tctx Map.!? (Left v) of
  Just t -> do
    k <- Kinding.synth kctx t
    return (if K.isStrictlyLin k then Map.delete (Left v) tctx else tctx)
  Nothing -> throwE (VarOutOfScope (B.getSpan v) v)   

-- NOTA: usar para o % em tipos
-- lookupType :: KindCtx -> TypeCtx -> Either Variable Identifier -> Validation (T.Type, TypeCtx)
-- lookupType kctx tctx xi = case tctx Map.!? xi of
--   Just t -> do
--     k <- Kinding.synth kctx t
--     return (t, if K.isStrictlyLin k then Map.delete xi tctx else tctx)
--   Nothing -> case xi of
--     Left  x -> throwE (VarOutOfScope (getSpan x) x)
--     Right i -> throwE (ConsOutOfScope (getSpan i) i)