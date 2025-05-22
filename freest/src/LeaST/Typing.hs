module LeaST.Typing where

import LeaST.LeaST qualified as L
import qualified Syntax.Base as B

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
  Int s _       -> pure (T.Int s   , tctx)
  Float s _     -> pure (T.Float s , tctx)
  Char s _      -> pure (T.Char s  , tctx)
-- Var B.Variable
  Var s x       -> lookupType kctx tctx (Left  x)
-- Abs B.Variable T.Type Exp
  Abs s ps m e'  -> do
    (kctxps, tctxps) <- synthParams kctx ps
    let kctx' = kctxps `Map.union` kctx
    (t, tctxe) <- synth kctx' (tctxps `Map.union` tctx) e'
    tctx' <- typeCtxDifference kctx' tctxe tctxps
    unless (m /= K.Un) $ checkEquivTypeCtxs e' tctx' tctx
    return (foldr (\cases (ExpLevel  (_, u)) t' -> T.AppArrow s m u t'
                          (TypeLevel (a, k)) (T.AppForall s aks t') -> 
                            T.AppForall s ((a, k) : aks) t'
                          (TypeLevel (a, k)) t' -> T.AppForall s [(a, k)] t')
                  t ps
           ,tctx')
    where
      synthParams :: KindCtx -> [Level (Pat, T.Type) (Variable, K.Kind)] -> Validation (KindCtx, TypeCtx)
      synthParams kctx = \case
        ExpLevel  (p,t) : ps -> do
          Kinding.checkProper kctx t
          tctxp <- checkPat kctx p t
          second (Map.union tctxp) <$> synthParams kctx ps
        TypeLevel (a,k) : ps ->
          first  (Map.insert a k) <$> synthParams (Map.insert a k kctx) ps
        [] -> return (Map.empty, Map.empty)
-- App Exp Exp --fazer?
  App s f as    -> do
    (t, tctx') <- synth kctx tctx f
    t' <- Expose.typeArrow f t
    checkArgs f kctx tctx' t' (as, t')
-- Con B.Identifier
  Con s e1 e2 -> do  --é o mesmo?
    (t', tctx') <- synth kctx tctx e1
    let t = T.List s t'
    (t,) <$> check kctx tctx' e2 t
-- Case Exp [(Alt, Exp)] --n fazer
-- Type T.Type --n fazer
-- TAbs B.Variable K.Kind Exp  --fazer
-- TApp Exp Exp  --fazer


-- TODO Funcção copiada do FreeST, trocar
-- | Check-against for expressions. Given kind and type contexts, it checks
-- whether an expression has a given type, throwing an error if it does not.
-- Returns the updated type context without the linear variables consumed in 
-- the expression.
check :: KindCtx -> TypeCtx -> Exp -> T.Type -> Validation TypeCtx
check kctx tctx e t = gets typeDecls >>= \tds -> case e of
-- Lit Literal 
  Int s _   -> checkEquivTypes (Left e) t (T.Int s)   >> pure tctx
  Float s _ -> checkEquivTypes (Left e) t (T.Float s) >> pure tctx
  Char s _  -> checkEquivTypes (Left e) t (T.Char s)  >> pure tctx
-- Con B.Identifier -- n fazer
-- Var B.Variable 
  Var s x       -> do
    (u, tctx') <- lookupType kctx tctx (Left x) 
    checkEquivTypes (Left e) t u
    return tctx'
-- App Exp Exp --fazer?
  App s f as -> do
    (u, tctx') <- synth kctx tctx f
    (v, tctx'') <- checkArgs f kctx tctx' u (as, u) --TODO trocar, App funciona diferente no LeaST
    checkEquivTypes (Left e) t v
    return tctx''
-- Abs B.Variable T.Type Exp 
  Abs s ps m e'  -> do
    (u, kctxps, tctxps) <- checkParams e t kctx tctx (prepareParams ps) t
    let kctx' = kctxps `Map.union` kctx
    tctxe' <- check kctx' (tctxps `Map.union` tctx) e' u
    tctx' <- typeCtxDifference kctx' tctxe' tctxps
    unless (m /= K.Un) $ checkEquivTypeCtxs e tctx' tctx
    return tctx'
    where
      prepareParams = map (bimap (second Just) (second Just))
--  _ -> do
-- TODO existe remaining cases pq é suposto tirar os outros?

-- Case Exp [(Alt, Exp)] --n fazer
-- Type T.Type --n fazer
-- TAbs B.Variable K.Kind Exp  --fazer
-- TApp Exp Type  --fazer


-- | Type equivalence. Checks if two types are equivalent, throwing an error
-- if they are not. An expression or pattern is provided to locate the error.
checkEquivTypes :: Exp -> T.Type -> T.Type -> Validation ()
checkEquivTypes eop t1 t2 = do
  tds <- gets typeDecls
  unless (equivalent tds t1 t2) $
    throwE (TypeMismatch (getSpan eop) t1 t2 (Left eop))


lookupType :: KindCtx -> TypeCtx -> Either Variable Identifier -> Validation (T.Type, TypeCtx)
lookupType kctx tctx xi = case tctx Map.!? xi of
  Just t -> do
    k <- Kinding.synth kctx t
    return (t, if K.isStrictlyLin k then Map.delete xi tctx else tctx)
  Nothing -> case xi of
    Left  x -> throwE (VarOutOfScope (getSpan x) x)
    Right i -> throwE (ConsOutOfScope (getSpan i) i)


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