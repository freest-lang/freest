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

import           Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import qualified Syntax.Module as M
import           Syntax.Substitution (freeVars)
import qualified Syntax.Type as T
import           UI.Error (Error(..))

import           Control.Monad (replicateM, forM, void, forM_, unless, foldM)
import           Control.Monad.State ( gets, modify, State, runState)
import           Data.Bifunctor (first, second, bimap)
import           Data.Bitraversable (bisequence, bimapM)
import           Data.Foldable (foldrM)
import           Data.Function (on)
import qualified Data.List as List
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Debug.Trace (trace)
import           Control.Monad.Extra (ifM)

data ScopingKey 
  = TVar String 
  | EVar String 
  | TId String 
  | DId String
  | CId String 
  deriving (Eq,Ord,Show)

type ScopingCtx = Map.Map ScopingKey Int

lookupTVar, lookupEVar :: Variable -> ScopingCtx -> Maybe Int
lookupTVar a = Map.lookup $ TVar $ external a
lookupEVar x = Map.lookup $ EVar $ external x

memberCId, memberTId, memberDId :: Identifier -> ScopingCtx -> Bool
memberCId ci ctx = CId (show ci) `Map.member` ctx
memberTId ti ctx = TId (show ti) `Map.member` ctx
memberDId di ctx = DId (show di) `Map.member` ctx

fromTVarList, fromEVarList :: [Variable] -> ScopingCtx
fromTVarList = Map.fromList . map (\a -> (TVar $ external a, internal a))
fromEVarList = Map.fromList . map (\x -> (EVar $ external x, internal x))

insertTVar, insertEVar, deleteTVar, deleteEVar :: Variable -> ScopingCtx -> ScopingCtx
insertTVar a = Map.insert (TVar $ external a) (internal a)
insertEVar x = Map.insert (EVar $ external x) (internal x)
deleteTVar a = Map.delete (TVar $ external a)
deleteEVar x = Map.delete (EVar $ external x)

insertCId, insertTId, insertDId :: Identifier -> ScopingCtx -> ScopingCtx
insertCId ci = Map.insert (CId $ show ci) (-1)
insertTId ti = Map.insert (TId $ show ti) (-1)
insertDId di = Map.insert (DId $ show di) (-1)

type Scoping = State ScopingState

data ScopingState = ScopingState{counter :: Int, errors :: [Error]}

runScoping :: M.Module -> Either [Error] M.Module
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

scopeModule :: ScopingCtx -> M.Module -> Scoping (ScopingCtx, M.Module)
scopeModule ctx m = do
  (ctx'  , dataDecls'  ) <- scopeDataDecls ctx   (M.dataDecls   m)
  (ctx'' , typeDecls'  ) <- scopeTypeDecls ctx'  (M.typeDecls   m)
  (ctx''', definitions') <- scopeDefs      ctx'' (M.definitions m)
  return (ctx''', m{ M.dataDecls   = dataDecls'
                   , M.typeDecls   = typeDecls'
                   , M.definitions = definitions'
                   })

scopeDataDecls :: ScopingCtx -> M.DataDecls -> Scoping (ScopingCtx, M.DataDecls)
scopeDataDecls ctx dds =
  foldM scopeDataDecl (ctx, Map.empty) (Map.assocs dds)
  where
    scopeDataDecl :: (ScopingCtx, M.DataDecls) -> (Identifier, M.Lambda M.ConsDecls) -> Scoping (ScopingCtx, M.DataDecls)
    scopeDataDecl (ctx',dds') (ti, dd@(unzip -> (as,ks), cds)) =
      if memberTId ti ctx' || memberDId ti ctx'
        then do 
          insertError (MultipleTypeDecls (getSpan ti) ti)
          return (ctx', Map.insert ti dd dds')
        else do 
          as' <- mapM freshInternal as
          ks' <- mapM scopeKind ks
          let ctx'' = Map.union (fromTVarList as') ctx'
          (ctx''',cds') <- scopeConsDecls ctx'' cds
          return (insertDId ti ctx''', Map.insert ti (zip as' ks', cds') dds')
    scopeConsDecls :: ScopingCtx -> M.ConsDecls -> Scoping (ScopingCtx, M.ConsDecls)
    scopeConsDecls ctx cds = foldM scopeConsDecl (ctx, Map.empty) (Map.assocs cds)
      where
        scopeConsDecl :: (ScopingCtx, M.ConsDecls) -> (Identifier, [T.Type]) -> Scoping (ScopingCtx, M.ConsDecls)
        scopeConsDecl (ctx',cds') (ci,ts) =
          if memberCId ci ctx'
            then do 
              insertError (MultipleConsDecls (getSpan ci) ci)
              return (ctx', Map.insert ci ts cds')
            else do
              ts' <- mapM (scopeType ctx') ts
              let ctx'' = insertCId ci ctx'
              return (ctx'', Map.insert ci ts' cds')

scopeTypeDecls :: ScopingCtx -> M.TypeDecls -> Scoping (ScopingCtx, M.TypeDecls)
scopeTypeDecls ctx tds = foldM scopeTypeDecl (ctx, Map.empty) (Map.assocs tds)
  where
    scopeTypeDecl :: (ScopingCtx, M.TypeDecls) -> (Identifier, M.Lambda T.Type) -> Scoping (ScopingCtx, M.TypeDecls)
    scopeTypeDecl (ctx', tds') (ti, td@(unzip -> (as,ks), t)) =
      if ti `memberTId` ctx' || ti `memberDId` ctx'
        then do
          insertError (MultipleTypeDecls (getSpan ti) ti)
          return (ctx',Map.insert ti td tds')
        else do 
          as' <- mapM freshInternal as
          ks' <- mapM scopeKind ks
          t'  <- scopeType (fromTVarList as') t
          return (insertTId ti ctx', Map.insert ti (zip as' ks', t') tds')

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
      checkConflictingDefs [ExpLevel p]
      (ictx', p') <- scopePat ctx ictx p
      rhs' <- scopeRHS ctx rhs
      let ctx'' = fromEVarList (Set.toList $ patVars p')
      let ctx' = ctx'' `Map.union` ctx
      second (E.ValDecl p' rhs':) <$> scopeDefs' ctx' ictx' ds
    scopeDefs' ctx ictx (E.FnDecl x psrhss : ds) = do 
      (ictx', x') <- case lookupEVar x ictx of 
        Nothing -> (ictx,) <$> freshInternal x
        Just internal -> pure (deleteEVar x ictx, x{internal})
      let ctx' = insertEVar x' ctx
      psrhss' <- forM psrhss \(pars, rhs) -> do
        checkConflictingDefs (ExpLevel (E.VarPat (getSpan x') x') : pars)
        (ctx'', pars') <- foldM scopeParam (ctx',[]) pars
        (pars',) <$> scopeRHS ctx'' rhs
      second (E.FnDecl x' psrhss' :) <$> scopeDefs' ctx' ictx' ds
      where 
        scopeParam (ctx',pars') (ExpLevel  p) = do
          (_, p') <- scopePat ctx' Map.empty p
          let ctx'' = fromEVarList (Set.toList (patVars p')) `Map.union` ctx'
          return (ctx'', pars'++[ExpLevel p'])
        scopeParam (ctx',pars') (TypeLevel a) = do
          a' <- freshInternal a
          let ctx'' = insertTVar a' ctx'
          return (ctx'', pars'++[TypeLevel a'])
    scopeDefs' ctx ictx (E.SigDecl xs t : ds) = do 
      checkConflictingDefs $ map (\x -> ExpLevel $ E.VarPat (getSpan x) x) xs
      (ictx', xs') <- foldM (\(ictx'',xs'') x -> 
          case lookupEVar x ictx'' of
            Nothing -> do 
              x' <- freshInternal x 
              return (insertEVar x' ictx'', xs''++[x'])
            Just internal -> do
              insertError (MultipleVarDecls (getSpan x) x) -- TODO: better error
              return (ictx'',xs''++[x])
        ) (ictx,[]) xs
      t' <- scopeTypeQ ctx t
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
  case lookupEVar x ctx of
    Nothing -> {- insertError (OutOfScope (getSpan x) x) -} -- leaving this for the typechecker
      pure e
    Just internal -> pure $ E.Var s x{internal}
scopeExp ctx (E.App s e args) =
  E.App s
  <$> scopeExp ctx e
  <*> mapM (\case ExpLevel  e -> ExpLevel  <$> scopeExp ctx e
                  TypeLevel t -> TypeLevel <$> scopeType ctx t)
           args
scopeExp ctx (E.Abs s pars m e) = do
  checkConflictingDefs (map (bimap fst fst) pars)
  let (ps, ts) = (bimap (map fst) (map fst) . partitionLevels) pars
  (ctx',pars') <- foldM scopeTypedParam (ctx,[]) pars
  E.Abs s pars' m <$> scopeExp ctx' e
  where
    scopeTypedParam (ctx',pars') (ExpLevel  (p,t)) = do
      (_, p') <- scopePat ctx' Map.empty p
      t' <- scopeType ctx' t
      let ctx'' = fromEVarList (Set.toList (patVars p')) `Map.union` ctx'
      return (ctx'', pars'++[ExpLevel (p',t')])
    scopeTypedParam (ctx',pars') (TypeLevel (a,k)) = do
      a' <- freshInternal a
      k' <- scopeKind k
      let ctx'' = insertTVar a' ctx'
      return (ctx'', pars'++[TypeLevel (a',k')])
scopeExp ctx (E.Let s ds e) = do
  (ctx', ds') <- scopeDefs ctx ds
  E.Let s ds' <$> scopeExp ctx' e
scopeExp ctx (E.Case s e pes) = do
  e' <- scopeExp ctx e
  E.Case s e' <$> mapM scopePatExp pes
  where
    scopePatExp :: (E.Pat, E.Exp) -> Scoping (E.Pat, E.Exp)
    scopePatExp (p,e) = do
      checkConflictingDefs [ExpLevel p]
      (_,p') <- scopePat ctx Map.empty p
      let pvs = Set.toList $ patVars p'
      let ctx' = fromEVarList pvs `Map.union` ctx
      (p',) <$> scopeExp ctx' e
scopeExp ctx (E.If s e1 e2 e3) =
  E.If s <$> scopeExp ctx e1 <*> scopeExp ctx e2 <*> scopeExp ctx e3
scopeExp _ e = pure e

-- | Scopes a pattern. This function takes two contexts: the first being the main
-- lexical context, and the second being an auxilliary context for 'let' definitions,
-- which is used to match signatures to definitions. It returns the modified
-- auxilliary context (i.e., the lexical context must be modified separately!)
scopePat :: ScopingCtx -- main context
         -> ScopingCtx -- auxilliary context
         -> E.Pat 
         -> Scoping (ScopingCtx, E.Pat) -- returns the auxilliary context
scopePat _ ictx (E.WildPat s w) = (ictx,) . E.WildPat s <$> freshInternal w
scopePat _ ictx (E.VarPat s x) =
  case lookupEVar x ictx of
    Just internal -> pure (deleteEVar x ictx, E.VarPat s x{internal})
    Nothing -> (ictx,) . E.VarPat s <$> freshInternal x
scopePat ctx ictx p@(E.ConsPat s c ps) =
  if memberCId c ctx
    then do
      (ictx', ps') <- foldM (\(ictx'',ps'') p -> do
                              (ictx''', p') <- scopePat ctx ictx'' p
                              return (ictx''', ps''++[p]))
                            (Map.empty, [])
                            ps
      return (ictx', E.ConsPat s c ps')
    else pure (ictx, p) -- leaving this error for the typechecker
scopePat ctx ictx (E.TuplePat s ps) = do
  (ictx', ps') <- foldM (\(ictx'',ps'') p -> do
                          (ictx''', p') <- scopePat ctx ictx'' p
                          return (ictx''', ps''++[p]))
                        (Map.empty, [])
                        ps
  return (ictx', E.TuplePat s ps')
scopePat ctx ictx (E.AsPat s x p) =
  case lookupEVar x ictx of
    Nothing -> do
      x' <- freshInternal x
      second (E.AsPat s x') <$> scopePat ctx ictx p
    Just internal -> second (E.AsPat s x{internal}) <$> scopePat ctx (deleteEVar x ictx) p
scopePat ctx ictx p = pure (ictx, p)

checkConflictingDefs :: [Level E.Pat Variable] -> Scoping ()
checkConflictingDefs (partitionLevels -> (ps, as)) = do
  let evos = Map.unionsWith (++) (map patVarOccurs ps)
      tvos = varOccurs as
      vos = Map.filter ((>1) . length) (Map.union evos tvos)
  unless (Map.null vos) (insertError (ConflictingDefs vos))
  where 
    varOccurs :: [Variable] -> Map.Map (Level String String) [Span]
    varOccurs = foldr (\a occs -> Map.insertWith (++) (TypeLevel $ external a) [getSpan a] occs) Map.empty
    patVarOccurs :: E.Pat -> Map.Map (Level String String) [Span]
    patVarOccurs = \case
      E.VarPat s x     -> Map.singleton (ExpLevel $ external x) [getSpan x]
      E.ConsPat _ _ ps -> Map.unionsWith (++) (map patVarOccurs ps)
      E.TuplePat _ ps  -> Map.unionsWith (++) (map patVarOccurs ps)
      E.AsPat _ x p    -> Map.insertWith (++) (ExpLevel $ external x) [getSpan x] (patVarOccurs p)
      _                -> Map.empty

patVars :: E.Pat -> Set.Set Variable
patVars = \case 
  E.WildPat _ _    -> Set.empty
  E.VarPat _ x     -> Set.singleton x
  E.ConsPat s _ ps -> Set.unions (map patVars ps)
  E.TuplePat s ps  -> Set.unions (map patVars ps)
  E.AsPat _ x p    -> Set.insert x (patVars p)
  _                -> Set.empty

freshKVar :: Located a => a -> Scoping K.Kind
freshKVar l = do
  phi <- incCounter >>= \i -> return (Variable (getSpan l) ("φ"++show i) i)
  psi <- incCounter >>= \i -> return (Variable (getSpan l) ("ψ"++show i) i)
  return $ K.Proper (getSpan l) (K.VarM phi) (K.VarPK psi)

scopeType :: ScopingCtx -> T.Type -> Scoping T.Type
scopeType ctx = \case
  T.Choice  s m p lts ->
    let lts' = mapM (\(l,t) -> (l,) <$> scopeType ctx t) lts
    in T.Choice s m p <$> lts'
  T.Forall s a k t -> do
    a' <- freshInternal a
    k' <- scopeKind k
    let ctx' = insertTVar a' ctx
    T.Forall s a' k' <$> scopeType ctx' t
  t@(T.Var s a) ->
    case lookupTVar a ctx of
      Just i  -> return $ T.Var s a{internal=i}
      Nothing -> T.Var s <$> freshInternal a -- no error here; leave it for the typechecker
  T.App s t ts ->
    T.App s <$> scopeType ctx t <*> mapM (scopeType ctx) ts
  T.TName s i ts | memberDId i ctx -> pure $ T.DName s i ts
  T.DName s i ts -> T.DName s i <$> mapM (scopeType ctx) ts
  t -> pure t

scopeTypeQ :: ScopingCtx -> T.Type -> Scoping T.Type
scopeTypeQ ctx t = do
  t' <- scopeType ctx t 
  let fvm = Map.fromList (map (\a -> (TVar $ external a, a)) $ Set.toList (freeVars t'))
  if Map.null fvm 
    then scopeType ctx t
    else do
      aks <- mapM (\a -> (a,) <$> freshKVar a) $ List.sortBy (compare `on` getSpan) $ Map.elems fvm
      T.variadicForall (getSpan t) (NE.fromList aks) <$> scopeType (Map.map internal fvm `Map.union` ctx) t'

scopeKind :: K.Kind -> Scoping K.Kind
scopeKind = \case 
  K.Arrow s k1 k2 -> K.Arrow s  <$> scopeKind k1 <*> scopeKind k2
  K.Proper s m pk -> K.Proper s <$> scopeMult m  <*> scopePrekind pk
  where
    scopeMult (K.VarM phi) = do
      phi' <- freshInternal phi
      return $ K.VarM phi'{external="φ"++show (internal phi')}
    scopeMult m = pure m
    scopePrekind (K.VarPK psi) = do
      psi' <- freshInternal psi
      return $ K.VarPK psi'{external="φ"++show (internal psi')}
    scopePrekind pk = pure pk
