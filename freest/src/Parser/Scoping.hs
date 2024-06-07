{- |
Module      :  Parser.Scoping
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements the scoping phase, which processes the AST produced 
by the parser to yield one that is correct by construction.
This consists mainly of renaming the variables internally according to their
scope (which, in turn, requires grouping function equations, detecting 
duplicate variable declarations, etc.).
-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BlockArguments #-}
module Parser.Scoping
  (runScoping)
where

import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import Syntax.Module (DataDecl, Module(..))
import Syntax.Substitution (freeVars)
import qualified Syntax.Type as T
import Utils.Error (Error(..))

import Control.Monad (replicateM, forM, void, forM_, unless)
import Control.Monad.State ( gets, modify, State, runState)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Bifunctor (first, second, bimap)
import Data.Bitraversable (bisequence, bimapM)
import Data.Foldable (foldrM)

type Scoping = State ScopingState

data ScopingState = ScopingState{counter :: Int, errors :: [Error]}

type ScopingCtx = Map.Map (Either String String) Int

runScoping :: Module -> Either [Error] Module
runScoping m =
  let ((_,m'),s) = runState (scopeModule Map.empty m) (ScopingState 0 [])
  in if null (errors s) then Right m' else Left (errors s)

incCounter :: Scoping Int
incCounter = do
  c <- gets counter
  modify (\s -> s{counter=succ (counter s)})
  return c

insertError :: Error -> Scoping ()
insertError e = modify (\s -> s{errors = e : errors s})

freshInternal :: Variable -> Scoping Variable
freshInternal x = incCounter >>= \i -> return x{internal=i}

scopeModule :: ScopingCtx -> Module -> Scoping (ScopingCtx, Module)
scopeModule ctx m = do
  (ctx',dataDecls') <- scopeDataDecls ctx (dataDecls m)
  typeDecls' <- scopeTypeDecls (typeDecls m)
  (ctx'', defs') <- scopeDefs ctx' $ definitions m
  return (ctx'', Module (name m) (imports m) dataDecls' typeDecls' defs')

scopeDataDecls :: ScopingCtx -> [DataDecl] -> Scoping (ScopingCtx, [DataDecl])
scopeDataDecls ctx = foldrM (\d (ctx',ds') -> do (ctx'',d') <- scopeDataDecl ctx' d; return (ctx'',d':ds')) (ctx,[])
  where 
    scopeDataDecl :: ScopingCtx -> DataDecl -> Scoping (ScopingCtx, DataDecl)
    scopeDataDecl ctx (n, as, cs) = do
      as' <- mapM freshInternal as
      let ctx' = Map.fromList $ map (\a -> (Right $ external a, internal a)) as'
      (ctx'',cs') <- foldrM (\d (ctx',ds') -> do (ctx'',d') <- scopeConsDecl ctx' d; return (ctx'',d':ds')) (ctx',[]) cs
      return (ctx'', (n,as',cs'))
    scopeConsDecl :: ScopingCtx -> (Variable, [T.Type]) -> Scoping (ScopingCtx, (Variable, [T.Type]))
    scopeConsDecl ctx (c, ts) = 
      case ctx Map.!? Left (external c) of 
        Nothing -> do
          c' <- freshInternal c
          ts' <- mapM (scopeType ctx) ts 
          let ctx' = Map.insert (Left $ external c') (internal c') ctx 
          (ctx',) . (c',) <$> mapM (scopeType ctx) ts
        Just internal -> do 
          insertError (MultipleDecls (getSpan c) c)
          return (ctx, (c,ts))
      

scopeTypeDecls :: [(Variable, [Variable], T.Type)] -> Scoping [(Variable, [Variable], T.Type)]
scopeTypeDecls = mapM scopeTypeDecl
  where scopeTypeDecl (n, as, t) = do
          as' <- mapM freshInternal as
          (n, as',) <$> scopeType (Map.fromList $ map (\a -> (Right $ external a, internal a)) as') t

scopeDefs :: ScopingCtx -> [E.LetDecl] -> Scoping (ScopingCtx, [E.LetDecl])
scopeDefs ctx = scopeDefs' ctx Map.empty . groupEquations
  where 
    groupEquations :: [E.LetDecl] -> [E.LetDecl]
    groupEquations [ ] = [ ]
    groupEquations [d] = [d]
    groupEquations (E.FnDecl f1 psrhss1 : E.FnDecl f2 psrhss2 : ds)
      | external f1 == external f2 = groupEquations (E.FnDecl f1 (psrhss1 ++ psrhss2) : ds)
    groupEquations (d1:d2:ds) = d1 : groupEquations (d2:ds)

    scopeDefs' :: ScopingCtx -> ScopingCtx -> [E.LetDecl] -> Scoping (ScopingCtx, [E.LetDecl])
    scopeDefs' ctx _ [] = return (ctx, [])
    scopeDefs' ctx ictx (E.ValDecl p rhs : ds) = do
      checkConflictingDefs [p]
      (ictx', p') <- scopePat ctx ictx p
      rhs' <- scopeRHS ctx rhs
      let ctx'' = Map.fromList $ map (\x -> (Left $ external x, internal x)) (Set.toList $ patVars p')
      let ctx' = ctx'' `Map.union` ctx
      second (E.ValDecl p' rhs':) <$> scopeDefs' ctx' ictx' ds
    scopeDefs' ctx ictx (E.FnDecl x psrhss : ds) = do 
      (ictx', x') <- case ictx Map.!? Left (external x) of 
        Nothing -> (ictx,) <$> freshInternal x
        Just internal -> pure (Left (external x) `Map.delete` ictx, x{internal})
      let ctx' = Map.insert (Left $ external x') (internal x') ctx
      psrhss' <- forM psrhss \(ps,rhs) -> do
        checkConflictingDefs ps
        ps' <- map snd <$> mapM (scopePat ctx Map.empty) ps
        let pctx'' = Map.fromList $ concatMap (map (\x -> (Left $ external x, internal x)) . Set.toList . patVars) ps'
            ctx''  = pctx'' `Map.union` ctx'
        (ps',) <$> scopeRHS ctx'' rhs
      second (E.FnDecl x' psrhss' :) <$> scopeDefs' ctx' ictx' ds
    scopeDefs' ctx ictx (E.SigDecl xs t : ds) = do 
      checkConflictingDefs $ map (\x -> E.VarPat (getSpan x) x) xs
      (ictx', xs') <- foldrM (\x (ictx'',xs'') -> 
          case ictx'' Map.!? Left (external x) of
            Nothing -> do 
              x' <- freshInternal x 
              return (Map.insert (Left $ external x') (internal x') ictx'',x':xs'')
            Just internal -> do
              insertError (MultipleDecls (getSpan x) x) -- TODO: better error
              return (ictx'',x:xs'')
        ) (ictx,[]) xs
      t' <- quantifyScopeType ctx t
      second (E.SigDecl xs' t':) <$> scopeDefs' ctx ictx' ds
    
    scopeRHS :: ScopingCtx -> E.RHS -> Scoping E.RHS
    scopeRHS ctx (E.GuardedRHS ges Nothing) =
      E.GuardedRHS <$> mapM (bimapM (scopeExp ctx) (scopeExp ctx)) ges <*> pure Nothing
    scopeRHS ctx (E.GuardedRHS ges (Just ds)) = do
      (ctx',ds') <- scopeDefs ctx ds
      E.GuardedRHS <$> mapM (bimapM (scopeExp ctx') (scopeExp ctx')) ges <*> pure (Just ds')
    scopeRHS ctx (E.UnguardedRHS e Nothing) =
      E.UnguardedRHS <$> scopeExp ctx e <*> pure Nothing
    scopeRHS ctx (E.UnguardedRHS e (Just ds)) = do
      (ctx',ds') <- scopeDefs ctx ds
      E.UnguardedRHS <$> scopeExp ctx' e <*> pure (Just ds')


scopeExp :: ScopingCtx -> E.Exp -> Scoping E.Exp
scopeExp ctx (E.Tuple s es) = E.Tuple s <$> mapM (scopeExp ctx) es
scopeExp ctx e@(E.Var s x) =
  case ctx Map.!? Left (external x) of
    Nothing -> {- insertError (OutOfScope (getSpan x) x) -} -- leaving this for the typechecker
      pure e
    Just internal -> pure $ E.Var s x{internal}
scopeExp ctx (E.App s e args) =
  E.App s
  <$> scopeExp ctx e
  <*> mapM (\case E.EArg e -> E.EArg <$> scopeExp ctx e
                  E.TArg t -> E.TArg <$> scopeType ctx t)
           args
scopeExp ctx (E.Abs s (unzip -> (ps,ts)) m e) = do
  checkConflictingDefs ps
  ps' <- mapM (fmap snd . scopePat ctx Map.empty) ps
  ts' <- mapM (scopeType ctx) ts
  let pvs = Set.toList $ Set.unions $ map patVars ps'
  let ctx' = Map.fromList (map (\x -> (Left $ external x, internal x)) pvs) `Map.union` ctx
  E.Abs s (zip ps' ts') m <$> scopeExp ctx' e
scopeExp ctx (E.Let s ds e) = do
  (ctx', ds') <- scopeDefs ctx ds
  E.Let s ds' <$> scopeExp ctx' e
scopeExp ctx (E.Case s e pes) = do
  e' <- scopeExp ctx e
  E.Case s e' <$> mapM scopePatExp pes
  where
    scopePatExp :: (E.Pat, E.Exp) -> Scoping (E.Pat, E.Exp)
    scopePatExp (p,e) = do
      checkConflictingDefs [p]
      (_,p') <- scopePat ctx Map.empty p
      let pvs = Set.toList $ patVars p'
      let ctx' = Map.fromList (map (\x -> (Left $ external x, internal x)) pvs) `Map.union` ctx
      (p',) <$> scopeExp ctx' e
scopeExp ctx (E.If s e1 e2 e3) =
  E.If s <$> scopeExp ctx e1 <*> scopeExp ctx e2 <*> scopeExp ctx e3
scopeExp ctx (E.TAbs s (unzip -> (as,ks)) e) = do
  checkConflictingDefs $ map (\a -> E.VarPat (getSpan a) a) as -- a little hacky
  as' <- mapM freshInternal as 
  let ctx' = Map.fromList (map (\a -> (Right $ external a, internal a)) as') `Map.union` ctx
  E.TAbs s (zip as' ks) <$> scopeExp ctx' e
scopeExp _ e = pure e

scopePat :: ScopingCtx -> ScopingCtx -> E.Pat -> Scoping (ScopingCtx, E.Pat)
scopePat _ ictx (E.WildPat s w) = (ictx,) . E.WildPat s <$> freshInternal w
scopePat _ ictx (E.VarPat s x) =
  case ictx Map.!? Left (external x) of
    Nothing -> (ictx,) . E.VarPat s <$> freshInternal x
    Just internal -> pure (Map.delete (Left $ external x) ictx, E.VarPat s x{internal})
scopePat ctx ictx p@(E.ConsPat s c ps) =
  case ctx Map.!? Left (external c) of
    Nothing -> 
      {- insertError (OutOfScope (getSpan c) c) >> pure (ictx, p)-} -- leaving this for the typechecker
      pure (ictx, p)
    Just internal -> do
      (ictx', ps') <- foldrM (\p (ictx'',ps'') -> second (:ps'') <$> scopePat ctx ictx'' p)
                           (Map.empty, [])
                           ps
      return (ictx', E.ConsPat s c{internal} ps')
scopePat ctx ictx (E.TuplePat s ps) = do
  (ictx', ps') <- foldrM (\p (ictx'',ps'') -> second (:ps'') <$> scopePat ctx ictx'' p)
                       (Map.empty, [])
                       ps
  return (ictx', E.TuplePat s ps')
scopePat ctx ictx (E.AsPat s x p) =
  case ictx Map.!? Left (external x) of
    Nothing -> do
      x' <- freshInternal x
      second (E.AsPat s x') <$> scopePat ctx ictx p
    Just internal -> second (E.AsPat s x{internal}) <$> scopePat ctx (Map.delete (Left $ external x) ictx) p
scopePat ctx ictx p = pure (ictx, p)

checkConflictingDefs :: [E.Pat] -> Scoping ()
checkConflictingDefs ps = do 
  let vos = Map.filter ((>1) . length) $ Map.unions (map varOccs ps)
  unless (Map.null vos) (insertError (ConflictingDef vos))
  where 
    varOccs :: E.Pat -> Map.Map String [Span]
    varOccs (E.VarPat s x)     = Map.singleton (external x) [getSpan x]
    varOccs (E.ConsPat _ _ ps) = Map.unionsWith (++) (map varOccs ps)
    varOccs (E.TuplePat _ ps)  = Map.unionsWith (++) (map varOccs ps)
    varOccs (E.AsPat _ x p)    = Map.insertWith (++) (external x) [getSpan x] (varOccs p)
    varOccs _                  = Map.empty

patVars :: E.Pat -> Set.Set Variable
patVars (E.WildPat _ _) = Set.empty
patVars (E.VarPat _ x) = Set.singleton x
patVars (E.ConsPat s _ ps) = Set.unions (map patVars ps)
patVars (E.TuplePat s ps) = Set.unions (map patVars ps)
patVars (E.AsPat _ x p) = Set.insert x (patVars p)
patVars _ = Set.empty

freshKVar :: Located a => a -> Scoping K.Kind
freshKVar l = do
  phi <- incCounter >>= \i -> return (Variable (getSpan l) ("φ"++show i) i)
  psi <- incCounter >>= \i -> return (Variable (getSpan l) ("ψ"++show i) i)
  return $ K.Proper (getSpan l) (K.VarM phi) (K.VarPK psi)

scopeType :: ScopingCtx -> T.Type -> Scoping T.Type
scopeType ctx (T.Labelled  s l lts) =
  let lts' = mapM (\(l,t) -> (l,) <$> scopeType ctx t) lts
  in T.Labelled s l <$> lts'
scopeType ctx (T.Tuple s ts) =
  T.Tuple s <$> mapM (scopeType ctx) ts
scopeType ctx t@(T.Var s a) =
  case ctx Map.!? Right (external a) of
    Just i  -> return $ T.Var s a{internal=i}
    Nothing -> {- insertError (OutOfScope (getSpan a) a) >> -} -- leaving this for the typechecker
      return t 
scopeType ctx (T.App s t ts) =
  T.App s <$> scopeType ctx t <*> mapM (scopeType ctx) ts
scopeType ctx (T.Abs s aks t) = do
  aks' <- mapM (\(a,k) -> incCounter >>= \i -> return (a{internal=i},k)) aks
  let ctx' = Map.fromList (map (\(a,_) -> (Right $ external a, internal a)) aks') `Map.union` ctx
  T.Abs s aks' <$> scopeType ctx' t
scopeType ctx t = return t

quantifyScopeType :: ScopingCtx -> T.Type -> Scoping T.Type
quantifyScopeType ctx t = do
  let fvt = Set.map (Right . external) (freeVars t) `Set.difference` Map.keysSet ctx
  fvt' <- mapM freshInternal $ List.sort $ Set.toList $ freeVars t
  t' <- foldrM quantify t fvt'
  scopeType ctx t'
  where
    quantify a t' = do
      k <- freshKVar a
      return $ T.App (getSpan t') (T.Forall (getSpan t) k) [T.Abs (getSpan t') [(a, k)] t']
