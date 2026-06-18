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

module Parser.Scoping
  ( ScopingCtx
  , emptyScopingCtx
  , runScoping
  , runScopeModule
  , scopeModule
  , scopeModule'
  , scopeExp
  , scopeType
  , scopeKind
  , freshInternal
  , scopeDefs -- for freesti
  )
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Validation.Substitution ( freeTypeVars )
import Validation.Base
import Syntax.Type.Unkinded qualified as T
import UI.Error ( Error(..) )

import Control.Monad ( replicateM, forM, void, forM_, unless, foldM, when )
import Control.Monad.Extra ( ifM )
import Control.Monad.State ( gets, modify, State, runState )
import Control.Monad.Trans.Except ( runExceptT, throwE )
import Data.Bifunctor ( first, second, bimap )
import Data.Bitraversable ( bisequence, bimapM )
import Data.Foldable ( foldrM )
import Data.Function ( on )
import Data.List qualified as List
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

-- = Scoping context
-- The scoping context keeps track of variable and indentifier names.

-- == Internals
-- These should not be manipulated directly. See interface below.

-- | Keys that keep track of variable names.
data VarKey
  = TVar String -- ^ Key for type variable names
  | EVar String -- ^ Key for expression variable names
  | MVar String -- ^ Key for multiplicity variable names
  deriving (Eq, Ord, Show)

-- | The part of the context that keeps track of variable names.
type VarCtx = Map.Map VarKey Variable

-- | Keys that keep track of identifier names.
data IdKey
  = TId String  -- ^ Key for @type@ names
  | DId String  -- ^ Key for @data@ names
  | CId String  -- ^ Key for @data@ constructor names
  | KSig String -- ^ Key for kind signatures
  deriving (Eq, Ord, Show)

-- | The part of the context that keeps track of identifier names.
type IdCtx = Map.Map IdKey Identifier

-- | The scoping context, keeps track of both identifier and variable names.
type ScopingCtx = (IdCtx, VarCtx)

-- == Interface
-- The internals are hidden for easy replacement.

-- | The empty context.
emptyScopingCtx:: ScopingCtx
emptyScopingCtx= (Map.empty, Map.empty)

-- | The left-biased union of two contexts.
union :: ScopingCtx -> ScopingCtx -> ScopingCtx
union (ictx1, vctx1) (ictx2, vctx2) = 
  (Map.union ictx1 ictx2, Map.union vctx1 vctx2)

-- | Lookup the name of a variable in the context. Use
--     * 'lookupTVar' for type variables
--     * 'lookupEVar' for expression variables
--     * 'lookupMVar' for multiplicity variables
lookupTVar, lookupEVar, lookupMVar
  :: Variable -> ScopingCtx -> Maybe Variable
lookupTVar a = Map.lookup (TVar $ external a) . snd
lookupEVar x = Map.lookup (EVar $ external x) . snd
lookupMVar x = Map.lookup (MVar $ external x) . snd

-- | Is a given identifier name in the context? Use
--
--     * 'memberTId' for @type@ names;
--     * 'memberDId' for @data@ names;
--     * 'memberCId' for @data@ constructor names;
--     * 'memberKSig' for kind signatures.
memberTId, memberDId, memberCId, memberKSig
  :: Identifier -> ScopingCtx -> Bool
memberTId  (Identifier _ s) ctx = TId  s `Map.member` fst ctx
memberDId  (Identifier _ s) ctx = DId  s `Map.member` fst ctx
memberCId  (Identifier _ s) ctx = CId  s `Map.member` fst ctx
memberKSig (Identifier _ s) ctx = KSig s `Map.member` fst ctx

-- | Build a context from a list of variables. Use
-- 
--     * 'fromTVarList' for type variables;
--     * 'fromEVarList' for expression variables.
fromTVarList, fromEVarList, fromMVarList
  :: [Variable] -> ScopingCtx
fromTVarList = (Map.empty,) . Map.fromList . map (\a -> (TVar $ external a, a))
fromEVarList = (Map.empty,) . Map.fromList . map (\x -> (EVar $ external x, x))
fromMVarList = (Map.empty,) . Map.fromList . map (\x -> (MVar $ external x, x))

-- | Convert to a list of expression variables.
toEVarList :: ScopingCtx -> [Variable]
toEVarList (_, vctx) = 
  Map.elems $ Map.filterWithKey (\cases EVar{} _ -> True ; _ _ -> False) vctx

toTVarList :: ScopingCtx -> [Variable]
toTVarList (_, vctx) = 
  Map.elems $ Map.filterWithKey (\cases TVar{} _ -> True ; _ _ -> False) vctx

toMVarList :: ScopingCtx -> [Variable]
toMVarList (_, vctx) = 
  Map.elems $ Map.filterWithKey (\cases MVar{} _ -> True ; _ _ -> False) vctx

-- | Insert a variable name in the context. Use
-- 
--     * 'insertTVar' for type variables
--     * 'insertEVar' for expression variables
insertTVar, insertEVar, insertMVar :: Variable -> ScopingCtx -> ScopingCtx
insertTVar a = second $ Map.insert (TVar $ external a) a
insertEVar x = second $ Map.insert (EVar $ external x) x
insertMVar x = second $ Map.insert (MVar $ external x) x

-- | Delete a variable name from the context. Use
-- 
--     * 'deleteTVar' for type variables;
--     * 'deleteEVar' for expression variables.
deleteTVar, deleteEVar, deleteMVar :: Variable -> ScopingCtx -> ScopingCtx
deleteTVar a = second $ Map.delete (TVar $ external a)
deleteEVar x = second $ Map.delete (EVar $ external x)
deleteMVar x = second $ Map.delete (MVar $ external x)

-- | Insert an identifier name in the context. Use
--
--     * 'insertTId' for @type@ names;
--     * 'insertDId' for @data@ names;
--     * 'insertCId' for @data@ constructor names;
--     * 'insertKSig' for kind signatures.
insertTId, insertDId, insertCId, insertKSig
  :: Identifier -> ScopingCtx -> ScopingCtx
insertTId  i@(Identifier _ s) = first $ Map.insert (TId  s) i
insertDId  i@(Identifier _ s) = first $ Map.insert (DId  s) i
insertCId  i@(Identifier _ s) = first $ Map.insert (CId  s) i
insertKSig i@(Identifier _ s) = first $ Map.insert (KSig s) i

tIdElems, dIdElems, cIdElems, kSigElems :: ScopingCtx -> [Identifier]
tIdElems  = Map.elems . Map.filterWithKey (\cases TId{}  _ -> True; _ _ -> False) . fst
dIdElems  = Map.elems . Map.filterWithKey (\cases DId{}  _ -> True; _ _ -> False) . fst
cIdElems  = Map.elems . Map.filterWithKey (\cases CId{}  _ -> True; _ _ -> False) . fst
kSigElems = Map.elems . Map.filterWithKey (\cases KSig{} _ -> True; _ _ -> False) . fst

-- | Run a scoping procedure on a given value, returning either:
-- 
--     * a list of errors, if any was encountered;
--     * the result of the scoping procedure, otherwise.
runScoping :: (ScopingCtx -> a -> Validation b) -> a -> Either [Error] b
runScoping f x =
  let (x', ValidationState{errors}) = runState (runExceptT $ f emptyScopingCtx x) emptyValidationState
  in case x' of
    Left e -> Left (errors ++ [e])
    Right x'' | null errors -> Right x'' 
              | otherwise   -> Left errors

-- | Insert an error in the scoping state.
insertError :: Error -> Validation ()
insertError e = modify (\s -> s{errors = e : errors s})

-- | Update the internal name of a variable with a fresh name.
freshInternal :: Variable -> Validation Variable
freshInternal x = incCounter >>= \i -> return x{internal = i}

-- = Scoping procedures

-- | Run scoping on a module, returning either:
-- 
--     * a list of errors, if any was encountered;
--     * the scoped module, otherwise.
runScopeModule :: M.ParsedModule -> Either [Error] M.ScopedModule
runScopeModule = runScoping scopeModule

-- | Scope a module, returning also the resulting context.
scopeModule' :: ScopingCtx -> M.ParsedModule -> Validation (ScopingCtx, M.ScopedModule)
scopeModule' ctx m = do
  (ctx, kss) <- scopeKindSigs  ctx (M.kindSigs m)
  (ctx, tds, dds) <- scopeTypeDataDecls ctx (M.typeDecls m) (M.dataDecls m)
  (ctx, cds) <- scopeConsDecls ctx dds (M.consDecls m)
  (ctx, lds) <- scopeDefs      ctx (M.definitions m)
  return (ctx, m{ M.kindSigs    = kss
                , M.typeDecls   = tds
                , M.dataDecls   = dds
                , M.consDecls   = cds
                , M.definitions = lds
                })

-- | Scope a module.
scopeModule :: ScopingCtx -> M.ParsedModule -> Validation M.ScopedModule
scopeModule ctx m = snd <$> scopeModule' ctx m

-- | Update a scoping context with a list of kind signatures
-- (Kind signatures themselves do not need scoping).
scopeKindSigs :: ScopingCtx -> M.KindSigs Parsed 
                 -> Validation (ScopingCtx, M.KindSigs Scoped)
scopeKindSigs ctx kss = do
  let es = Map.fromList [(i, [i]) | i <- kSigElems ctx]
      (es', ctx') = foldr scopeKindSig (es, ctx) kss
  forM_ es' (\is -> when (length is > 1) do
    throwE (MultipleKindSigs (getSpan (head is)) is))
  return (ctx', Map.fromList kss)
  where
   scopeKindSig (i, k) (es, ctx) = (Map.insertWith (++) i [i] es, insertKSig i ctx)

-- | Insert @data@ and @type@ names in the scoping context, checking for
-- duplicate declarations in the process.
scopeTypeDataDecls :: ScopingCtx 
                   -> M.TypeDecls Parsed
                   -> M.DataDecls Parsed
                   -> Validation (ScopingCtx, M.TypeDecls Scoped, M.DataDecls Scoped)
scopeTypeDataDecls ctx tds dds = do
  let es = Map.fromList [(i, [i]) | i <- tIdElems ctx ++ dIdElems ctx]
      (es' , ctx' ) = foldr (\(ti, _) -> bimap (Map.insertWith (++) ti [ti]) 
                                              (insertTId ti)) 
                           (es, ctx) tds
      (es'', ctx'') = foldr (\(ti, _) -> bimap (Map.insertWith (++) ti [ti]) 
                                              (insertDId ti)) 
                           (es', ctx') dds
  forM_ es'' \is -> when (length is > 1) $
    throwE (MultipleTypeDecls (getSpan (head is)) is)
  (ctx''' , tds') <- scopeTypeDecls ctx''  tds
  (ctx'''', dds') <- scopeDataDecls ctx''' dds
  return (ctx'''', tds', dds')

scopeConsDecls :: ScopingCtx
               -> M.DataDecls Scoped
               -> M.ConsDecls Parsed 
               -> Validation (ScopingCtx, M.ConsDecls Scoped)
scopeConsDecls ctx dds cds = do
  let es = Map.fromList [(i, [i]) | i <- cIdElems ctx]
      (es' , ctx') = foldr 
        (\(ci, _) -> bimap (Map.insertWith (++) ci [ci]) (insertCId ci))
        (es, ctx) cds
  forM_ es' \is -> when (length is > 1) $
    throwE (MultipleConsDecls (getSpan (head is)) is)
  (ctx',) <$> foldM (scopeConsDecl ctx') Map.empty cds
  where
    scopeConsDecl :: ScopingCtx 
                  -> M.ConsDecls Scoped 
                  -> (Identifier, (Identifier, [T.ParsedType])) 
                  -> Validation (M.ConsDecls Scoped)
    scopeConsDecl ctx' cds' (ci, (di, ts)) = do
      let as = map fst (fst (dds Map.! di))
      ts' <- mapM (scopeType (fromTVarList as `union` ctx')) ts
      return (Map.insert ci (di, ts') cds')

-- | Scope a list of @data@ declarations, returning also the updated scoping
-- context.
scopeDataDecls :: ScopingCtx 
               -> M.DataDecls Parsed
               -> Validation (ScopingCtx, M.DataDecls Scoped)
scopeDataDecls ctx = foldM scopeDataDecl (ctx, Map.empty)
  where
    scopeDataDecl (ctx', dds') dd@(ti, (unzip -> (as, ks), cis)) = do
        unless (ti `memberKSig` ctx) do
          throwE (LacksKindSig (getSpan ti) ti)
        as'  <- mapM freshInternal as 
        ks'  <- mapM (scopeKind ctx) ks
        return (ctx', Map.insert ti (zip as' ks', cis) dds')
    scopeConsDecls ctx = foldM (scopeConsDecl ctx) Map.empty
      where
        scopeConsDecl ctx cds' (ci, ts) = do
          ts' <- mapM (scopeType ctx) ts 
          return (Map.insert ci ts' cds')

-- | Scope a list of @type@ declarations, returning also the updated scoping 
-- context.
scopeTypeDecls :: ScopingCtx -> M.TypeDecls Parsed
               -> Validation (ScopingCtx, M.TypeDecls Scoped)
scopeTypeDecls ctx = foldM scopeTypeDecl (ctx, Map.empty)
  where
    scopeTypeDecl (ctx', tds') (ti, (n, t)) = do
      unless (memberKSig ti ctx') (throwE (LacksKindSig (getSpan ti) ti))
      t'  <- scopeType ctx' t
      return (ctx', Map.insert ti (n, t') tds')

-- | Scope a list of @let@ declarations, returning also the updated scoping 
-- context. Besides scoping the variables, this procedure also groups function
-- equations and detects signatures without accompanying definitions.
scopeDefs :: ScopingCtx -> [E.LetDecl Parsed] -> Validation (ScopingCtx, [E.LetDecl Scoped])
scopeDefs ctx ds = do    
  (ictx, ctx, ds) <- scopeDefs' False ctx emptyScopingCtx (groupEquations ds)
  forM_ (toEVarList ictx) (\x -> insertError (SigLacksDef (getSpan x) x))
  return (ctx, ds)
  where
    groupEquations = \case
      (E.FnDef f1 psrhss1 : E.FnDef f2 psrhss2 : ds) 
        | external f1 == external f2 -> 
          groupEquations (E.FnDef f1 (psrhss1 ++ psrhss2) : ds)
      (E.Mutual ds' : ds) -> E.Mutual (groupEquations ds') : groupEquations ds
      (d1:d2:ds) -> d1 : groupEquations (d2:ds)
      [d] -> [d]
      []  -> []

    scopeDefs' isMutual ctx ictx = \case 
      [] -> return (ictx, ctx, [])
      (E.ValDef p rhs : ds) -> do
        checkConflictingDefs [ExpLevel p]
        (ictx', p') <- scopePat ctx ictx p
        rhs' <- scopeRHS ctx rhs
        let ctx' = insertPatVars p' ctx
        second (E.ValDef p' rhs':) <$> scopeDefs' isMutual ctx' ictx' ds
      (E.FnDef x psrhss : ds) -> do
        (ictx', x') <- case lookupEVar x ictx of
          Nothing -> (ictx,) <$> freshInternal x
          Just x' -> pure (deleteEVar x ictx, x{internal = internal x'})
        let ctx' = insertEVar x' ctx
        psrhss' <- forM psrhss \(pars, rhs) -> do
          checkConflictingDefs (ExpLevel (E.VarPat (getSpan x') x') : pars)
          (ctx'', pars') <- foldM scopeFnDefParam (ctx',[]) pars
          (pars',) <$> scopeRHS ctx'' rhs
        second (E.FnDef x' psrhss' :) <$> scopeDefs' isMutual ctx' ictx' ds
        where
          scopeFnDefParam (ctx', pars') = \case 
            (ExpLevel  p) -> do
              (_, p') <- scopePat ctx' emptyScopingCtx p
              let ctx'' = insertPatVars p' ctx'
              return (ctx'', pars'++[ExpLevel p'])
            (TypeLevel a) -> do
              a' <- freshInternal a
              let ctx'' = insertTVar a' ctx'
              return (ctx'', pars'++[TypeLevel a'])
            (MultLevel φ) -> do
              φ' <- freshInternal φ
              let ctx'' = insertMVar φ' ctx'
              return (ctx'', pars'++[MultLevel φ'])
      (E.TypeSig xs t : ds) -> do
        checkConflictingDefs $ map (\x -> ExpLevel $ E.VarPat (getSpan x) x) xs
        (ictx', xs') <- foldM (\(ictx'', xs'') x -> do 
            x' <- freshInternal x
            return (insertEVar x' ictx'', xs'' ++ [x'])) 
          (ictx, []) xs
        t' <- scopeAndQuantifyType ctx t
        let ctx' | isMutual  = foldr insertEVar ctx xs'
                 | otherwise = ctx
        second (E.TypeSig xs' t':) <$> scopeDefs' isMutual ctx' ictx' ds
      (E.Mutual ds' : ds) -> do
        -- hoist signatures, scope with isMutual = True
        -- (this will add them to the context in the case for E.TypeSig)
        let (sigs, fndefs) = 
              List.partition (\case E.TypeSig{} -> True ; _ -> False) ds'
        (ictx', ctx', ds'') <- scopeDefs' True ctx emptyScopingCtx(sigs ++ fndefs)
        forM_ (toEVarList ictx') (\x -> insertError (SigLacksDef (getSpan x) x))
        second (E.Mutual ds'' :) <$> scopeDefs' True ctx' ictx ds

-- | Scope a right-hand side.
scopeRHS :: ScopingCtx -> E.RHS Parsed -> Validation (E.RHS Scoped)
scopeRHS ctx = \case
  E.GuardedRHS ges Nothing   ->
    E.GuardedRHS <$> mapM (bimapM (scopeExp ctx) (scopeExp ctx)) ges 
                 <*> pure Nothing
  E.GuardedRHS ges (Just ds) -> do
    (ctx',ds') <- scopeDefs ctx ds
    E.GuardedRHS <$> mapM (bimapM (scopeExp ctx') (scopeExp ctx')) ges 
                 <*> pure (Just ds')
  E.UnguardedRHS e Nothing   ->
    E.UnguardedRHS <$> scopeExp ctx e <*> pure Nothing
  E.UnguardedRHS e (Just ds) -> do
    (ctx',ds') <- scopeDefs ctx ds
    E.UnguardedRHS <$> scopeExp ctx' e <*> pure (Just ds')

-- | Scope an expression.
scopeExp :: ScopingCtx -> E.Exp Parsed -> Validation (E.Exp Scoped)
scopeExp ctx = \case
  E.Int s x -> pure $ E.Int s x
  E.Float s x -> pure $ E.Float s x
  E.Char s x -> pure $ E.Char s x
  E.String s x -> pure $ E.String s x
  E.DCons s i -> pure $ E.DCons s i
  E.Var s x -> case lookupEVar x ctx of
    Nothing -> {- insertError (OutOfScope (getSpan x) x) -} -- leaving this for the typechecker
      pure $ E.Var s x
    Just x' -> pure $ E.Var s x{internal = internal x'}
  E.App s e args ->
    E.App s <$> scopeExp ctx e
            <*> forM args (\case 
                  ExpLevel  e -> ExpLevel  <$> scopeExp ctx e
                  TypeLevel t -> TypeLevel <$> scopeType ctx t
                  MultLevel m -> MultLevel <$> scopeMultiplicity ctx m)
  E.Abs s pars m e -> do
    checkConflictingDefs (map (mapLevel fst fst id) pars)
    (ctx', pars') <- foldM scopeAbsParam (ctx,[]) pars
    E.Abs s pars' <$> scopeMultiplicity ctx m <*> scopeExp ctx' e
    where
      scopeAbsParam = \cases 
        (ctx', pars') (ExpLevel  (p, t)) -> do
          (_, p') <- scopePat ctx' emptyScopingCtx p
          t' <- scopeType ctx' t
          let ctx'' = insertPatVars p' ctx'
          return (ctx'', pars' ++ [ExpLevel (p', t')])
        (ctx', pars') (TypeLevel (a, k)) -> do
          a' <- freshInternal a
          k' <- scopeKind ctx k
          let ctx'' = insertTVar a' ctx'
          return (ctx'', pars' ++ [TypeLevel (a', k')])
        (ctx', pars') (MultLevel φ) -> do
          φ' <- freshInternal φ
          let ctx'' = insertMVar φ' ctx'
          return (ctx'', pars' ++ [MultLevel φ'])
  E.Pack s ts e ->
    E.Pack s <$> mapM (scopeType ctx) ts <*> scopeExp ctx e
  E.Asc s e t ->
    E.Asc s <$> scopeExp ctx e <*> scopeType ctx t
  E.Let s ds e -> do
    (ctx', ds') <- scopeDefs ctx ds
    E.Let s ds' <$> scopeExp ctx' e
  E.Semi s e1 e2 -> 
    E.Semi s <$> scopeExp ctx e1 <*> scopeExp ctx e2
  E.Case s e prhss -> do
    e' <- scopeExp ctx e
    E.Case s e' <$> mapM scopePatRHS prhss
    where
      scopePatRHS :: (E.Pat, E.RHS Parsed) -> Validation (E.Pat, E.RHS Scoped)
      scopePatRHS (p, rhs) = do
        checkConflictingDefs [ExpLevel p]
        (_, p') <- scopePat ctx emptyScopingCtx p
        let ctx' = insertPatVars p' ctx
        (p',) <$> scopeRHS ctx' rhs
  E.If s e1 e2 e3 ->
    E.If s <$> scopeExp ctx e1 <*> scopeExp ctx e2 <*> scopeExp ctx e3
  E.Channel s t ->
    E.Channel s <$> scopeType ctx t
  E.Select s i -> pure $ E.Select s i
  E.SendType s t ->
    E.SendType s <$> scopeType ctx t
  E.ReceiveType s -> pure $ E.ReceiveType s

-- | Scope a pattern. This function takes two contexts: the first being the main
-- lexical context, and the second being an auxilliary context for 'let' definitions,
-- which is used to match signatures to definitions. It returns the modified
-- auxilliary context (i.e., the lexical context must be modified separately!)
scopePat :: ScopingCtx -- main context
         -> ScopingCtx -- auxilliary context
         -> E.Pat
         -> Validation (ScopingCtx, E.Pat) -- returns the auxilliary context
scopePat ctx ictx = \case
  E.WildPat s w -> (ictx,) . E.WildPat s <$> freshInternal w
  E.VarPat s x  -> case lookupEVar x ictx of
    Just x' -> pure (deleteEVar x ictx, E.VarPat s x{internal = internal x'})
    Nothing -> (ictx,) . E.VarPat s <$> freshInternal x
  E.PackPat s aks p -> do 
    as' <- mapM (freshInternal . fst) aks
    ks' <- mapM (scopeKind ctx . snd) aks  
    (ictx', p') <- scopePat (foldr insertTVar ctx as') ictx p
    return (ictx', E.PackPat s (zip as' ks') p')
  E.DConsPat s c ps -> do
    (ictx', ps') <- foldM (\(ictx'', ps'') p -> do
        (ictx''', p') <- scopePat ctx ictx'' p
        return (ictx''', ps''++[p']))
      (emptyScopingCtx, []) ps
    return (ictx', E.DConsPat s c ps')
  E.InPat s p1 p2 -> do
    (ictx', p1') <- scopePat ctx ictx p1
    (ictx'', p2') <- scopePat ctx ictx' p2
    return (ictx'', E.InPat s p1' p2')
  E.TypeInPat s (a, k) p -> do
    a' <- freshInternal a
    k' <- scopeKind ctx k
    (ictx', p') <- scopePat (insertTVar a' ctx) ictx p
    return (ictx', E.TypeInPat s (a', k') p')
  E.ChoicePat s c p -> do
    second (E.ChoicePat s c) <$> scopePat ctx ictx p
  E.AsPat s x p -> case lookupEVar x ictx of
    Nothing -> do
      x' <- freshInternal x
      second (E.AsPat s x') <$> scopePat ctx ictx p
    Just x' -> second (E.AsPat s x{internal = internal x'}) 
      <$> scopePat ctx (deleteEVar x ictx) p
  p -> pure (ictx, p)

-- | Check conflicting definitions for bindings.
checkConflictingDefs :: [Level E.Pat Variable Variable] -> Validation ()
checkConflictingDefs (partitionLevels -> (ps, as, φs)) = do
  let evos = Map.unionsWith (++) (map patVarOccurs ps)
      tvos = varOccurs TypeLevel as
      mvos = varOccurs MultLevel φs
  forM_ (Map.assocs $ Map.unions [evos, tvos, mvos]) \(xa, ss) -> 
    when (length ss > 1) $ insertError (ConflictingDefs (ss !! 1) xa ss)
  where
    varOccurs lv = foldr (\v occs -> 
        Map.insertWith (++) (lv $ external v) [getSpan v] occs) 
      Map.empty
    patVarOccurs = \case
      E.VarPat s x      -> Map.singleton (ExpLevel $ external x) [getSpan x]
      E.DConsPat _ _ ps -> Map.unionsWith (++) (map patVarOccurs ps)
      E.ChoicePat _ _ p -> patVarOccurs p
      E.AsPat _ x p     -> Map.insertWith (++) (ExpLevel $ external x) 
                             [getSpan x] (patVarOccurs p)
      _                 -> Map.empty

-- | Inserts the variables in a pattern into the scoping context.
-- TODO: can we do this in one pass with scopePat?
insertPatVars :: E.Pat -> ScopingCtx -> ScopingCtx
insertPatVars p ctx = 
  foldr (\case ExpLevel  x -> insertEVar x
               TypeLevel a -> insertTVar a
               MultLevel φ -> insertMVar φ) ctx (patVars p)
  where
    patVars :: E.Pat -> Set.Set (Level Variable Variable Variable)
    patVars = \case
      E.VarPat _ x      -> Set.singleton (ExpLevel x)
      E.PackPat _ aks p -> Set.fromList (map (TypeLevel . fst) aks) `Set.union` patVars p
      E.DConsPat _ _ ps -> Set.unions (map patVars ps)
      E.InPat _ p1 p2   -> patVars p1 `Set.union` patVars p2
      E.TypeInPat _ (a, _) p'-> Set.insert (TypeLevel a) (patVars p')
      E.ChoicePat _ _ p -> patVars p
      E.AsPat _ x p     -> Set.insert (ExpLevel x) (patVars p)
      _                 -> Set.empty

-- | Generate a fresh kind inference variable.
freshKVar :: Located a => a -> Validation K.Kind
freshKVar (getSpan -> s) = do
  i <- incCounter
  return $ K.Var s (Variable s  ("τ"++show i) i)

-- | Scope a type.
scopeType :: ScopingCtx -> T.ParsedType -> Validation T.ScopedType
scopeType ctx = \case
  T.Int s -> pure $ T.Int s
  T.Float s -> pure $ T.Float s
  T.Char s -> pure $ T.Char s
  T.Arrow s m -> T.Arrow s <$> scopeMultiplicity ctx m
  T.Quant s p pk m -> pure $ T.Quant s p pk m
  T.ForallM s m φs t -> do
    φs' <- mapM freshInternal φs
    T.ForallM s <$> scopeMultiplicity ctx m
                <*> pure φs'
                <*> scopeType (fromMVarList φs' `union` ctx) t
  T.Void s k -> T.Void s <$> scopeKind ctx k
  T.Skip s -> pure $ T.Skip s
  T.End s p -> pure $ T.End s p
  T.Message s m p -> T.Message s <$> scopeMultiplicity ctx m <*> pure p
  T.Choice  s m p ls -> do
    m' <- scopeMultiplicity ctx m
    let ds = foldr (\i -> Map.insertWith (++) i [i]) Map.empty ls
    forM_ ds \ids -> when (length ids > 1) $
      insertError (MultipleFieldDecls (getSpan (head ids)) ids)
    return $ T.Choice s m' p ls
  T.Semi s -> pure $ T.Semi s
  T.Dual s -> pure $ T.Dual s
  T.TName s i 
    | memberDId i ctx -> return (T.DName s i)
    | otherwise       -> return (T.TName s i)
  T.DName s i -> return (T.DName s i)
  t@(T.Var s a) ->
    case lookupTVar a ctx of
      Just a' -> return $ T.Var s a{internal = internal a'}
      Nothing -> T.Var s <$> freshInternal a
  T.Abs s (unzip -> (as, ks)) t -> do
    as' <- mapM freshInternal as
    ks' <- mapM (scopeKind ctx) ks
    T.Abs s (zip as' ks') <$> scopeType (fromTVarList as' `union` ctx) t
  T.App s t ts ->
    T.App s <$> scopeType ctx t <*> mapM (scopeType ctx) ts

-- | Scope a type, universally quantifying any free variables it might have
-- with a fresh kind inference variable.
scopeAndQuantifyType :: ScopingCtx -> T.ParsedType -> Validation T.ScopedType
scopeAndQuantifyType ctx t = do
  t' <- scopeType ctx t
  let fvt' = Set.toList (freeTypeVars t' Set.\\ Set.fromList (toTVarList ctx))        
  if null fvt'
    then return t'
    else do
      aks <- mapM (\a -> (a,) <$> freshKVar a) 
        $ List.sortBy (compare `on` getSpan) fvt'
      scopeType ctx $ T.AppForall (getSpan t) (K.Un $ getSpan t) aks t

-- | Scope a kind.
scopeKind :: ScopingCtx -> K.Kind -> Validation K.Kind
scopeKind ctx = \case
    K.Arrow s k1 k2 -> K.Arrow s  <$> scopeKind ctx k1 <*> scopeKind ctx k2
    K.Proper s m pk -> K.Proper s <$> scopeMultiplicity ctx m  <*> scopePrekind pk
    K.Var s τ       -> K.Var s    <$> scopeKVar τ
  where
    scopePrekind (K.VarPK ψ) = do
      ψ' <- freshInternal ψ
      return $ K.VarPK ψ'{external = "ψ" ++ show (internal ψ')}
    scopePrekind pk = pure pk
    scopeKVar τ = do
      τ' <- freshInternal τ
      return $ τ'{external = "τ" ++ show (internal τ')}

-- | Scope a multiplicity.
scopeMultiplicity :: ScopingCtx -> K.Multiplicity -> Validation K.Multiplicity
scopeMultiplicity ctx = \case
  K.Sup s lvφs -> K.Sup s . List.nub <$> foldrM (\(lv, φ) lvφs' -> do 
    case lookupMVar φ ctx of 
      Nothing -> throwE (MultVarOutOfScope (getSpan φ) φ)
      Just φ' -> return $ (lv, φ{internal = internal φ'}) : lvφs')
    [] lvφs
  m -> pure m
