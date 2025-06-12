module LeaST.Typing where

import LeaST.LeaST qualified as L
import Syntax.Kind qualified as K
import qualified Syntax.Type as T
import qualified Syntax.Base as B
import qualified Syntax.Expression as E
import Validation.Base
import Utils
import Validation.Expose qualified as Expose
import Validation.Kinding qualified as Kinding
import Validation.Typing qualified as Typing
import Validation.Typing ( TypeCtx, KindCtx )
import Validation.Normalisation ( normalise )
import Validation.Substitution ( subs, subsAll )
import Control.Monad.Trans.Except ( catchE, throwE )
import Control.Monad (forM_, when)
import Control.Monad.State


import UI.Error

import qualified Data.Map.Strict as Map
import Debug.Trace

--type TypeCtx = Map.Map (Either Variable Identifier) T.Type
--type KindCtx = Map.Map Variable K.Kind

-- Var B.Variable   --x
-- Lit Literal      --1
-- Abs B.Variable T.Type Exp --\x:Int -> x 
-- App Exp Exp  -- (\x:Int -> + x x) 2
-- Con B.Identifier --n fazer
-- Case Exp [(Alt, Exp)] --n fazer
-- Type T.Type --n fazer
-- TAbs B.Variable K.Kind Exp   --  (\@a:*T -> (\x:B -> x))
-- TApp Exp Type  -- (\@a:*T -> (\x:B -> x)) @Int

-- typeModule
-- checkLeastModule :: L.Exp -> Validation L.Exp 
-- checkLeastModule e = check Map.empty Map.empty e 

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
    tctx'' <- difference kctx tctx x
    return (T.AppArrow B.nullSpan K.Un t u, tctx'') --NOTA abstração  
-- App Exp Exp   
  L.App e f    -> do
    (t, tctx') <- synth kctx tctx e
    (_, t', u) <- Expose.function B.nullSpan t
    tctx'' <- check kctx tctx' f t'  
    return (u, tctx'')  
-- Con B.Identifier 
  L.Con i        ->  Typing.lookupType kctx tctx (Right i)
-- Case Exp [(Alt, Exp)]
  L.Case e ((a, e') : rest) -> do
    (t, tctx') <- synth kctx tctx e
    ds <- gets typeDecls
    case normalise ds t of
      t'@(T.AppDName s d us) -> do  --extract
        dds <- gets dataDecls
        case Map.lookup d dds of  --data 
          Just dd -> do
            (i, aks, ts) <- Typing.lookupDConsDecl d --TODO ver se é mesmo d
            let as = map fst aks
            (tctx'') <- checkAlt kctx tctx a (subsAll as us t)
            (v1, tctx'''1) <- synth kctx tctx'' e'
            forM_ rest $ \(ai, ei) -> do
              (tctx'') <- checkAlt kctx tctx ai (subsAll as us t)
              (vi, tctx'''i) <- synth kctx tctx'' ei 
              Typing.checkEquivTypes (Left (E.Int B.nullSpan 0)) v1 vi
              Typing.checkEquivTypeCtxs (E.Int B.nullSpan 0) tctx'''1 tctx'''i
            return (v1, tctx'''1)
          Nothing -> throwE (ExposeError B.nullSpan "a case expression" t)
      _ -> throwE (ExposeError B.nullSpan "a case expression" t)
-- TAbs B.Variable K.Kind Exp  
  L.TAbs a k e -> do
    (t, tctx') <- synth (Map.insert a k kctx) tctx e
    return (T.AppForall B.nullSpan [(a, k)] t, tctx')
-- TApp Exp Type 
  L.TApp e t -> do
    (t', tctx') <- synth kctx tctx e
    (vks, t'') <- Expose.polyExp B.nullSpan t' 
    Kinding.check kctx t (snd $ head vks)
    return (subs (fst $ head vks) t t'', tctx') 


-- | Check-against for expressions. Given kind and type contexts, it checks
-- whether an expression has a given type, throwing an error if it does not.
-- Returns the updated type context without the linear variables consumed in 
-- the expression.
check :: KindCtx -> TypeCtx -> L.Exp -> T.Type -> Validation TypeCtx
check kctx tctx e t = case e of 
-- Abs B.Variable T.Type Exp 
  L.Abs x t' e'  -> do
    Kinding.checkProper kctx t'   
    (_, t1, t2) <- Expose.function B.nullSpan t
    Typing.checkEquivTypes (Left (E.Int B.nullSpan 0)) t' t1   --NOTA Exp FreeST trocado por dummy: (E.Int B.nullSpan 0)
    (t3, tctx') <- synth kctx tctx (L.Var x)
    Typing.checkEquivTypes (Left (E.Int B.nullSpan 0)) t2 t3  
    tctx'' <- difference kctx tctx x
    return (tctx'') 
-- TAbs B.Variable K.Kind Exp
  L.TAbs a k e'  -> do
    (_, t') <- Expose.polyExp B.nullSpan t
    tctx' <- check (Map.insert a k kctx) tctx e' t'
    return tctx'
-- remaining cases
  _ -> do
    (u, tctx') <- synth kctx tctx e
    Typing.checkEquivTypes (Left (E.Int B.nullSpan 0)) t u
    return tctx'


checkAlt :: KindCtx -> TypeCtx -> L.Alt -> T.Type -> Validation TypeCtx
checkAlt kctx tctx e t = case e of 
-- ACon B.Identifier [B.Variable]
  L.ACon i vs -> do
    forM_ vs \v -> do
      when (head vs /= v) $ throwE (ExposeError B.nullSpan "a case expression" t)  --TODO trocar erro
    (i', vks, ts) <- Typing.lookupDConsDecl i 
    when (length vs /= length ts) $ throwE (ExposeError B.nullSpan "a case expression" t)    --TODO trocar erro
    return (foldl insertOne tctx (zip vs ts)) -- TODO simplificar
    where
      insertOne acc (v, t) = Map.insert (Left v) t acc
-- ALit Literal
  L.ALit l -> do
    (t', tctx') <- synth kctx tctx (L.Lit l)
    Typing.checkEquivTypes (Left (E.Int B.nullSpan 0)) t t'
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