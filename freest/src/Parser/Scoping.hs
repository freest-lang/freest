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
  (ScopingCtx
  ,emptyScopingCtx
  ,runScoping
  ,runScopeModule
  ,scopeModule
  ,scopeModule'
  ,scopeExp
  ,scopeType
  ,scopeKind
  )
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
-- import Validation.Rename ( rename )
import Validation.Substitution ( freeVars )
import Validation.Base
import Syntax.Type qualified as T
import UI.Error ( Error(..))

import Control.Monad ( replicateM, forM, void, forM_, unless, foldM, when )
import Control.Monad.Extra ( ifM )
import Control.Monad.State ( gets, modify, State, runState )
import Data.Bifunctor ( first, second, bimap )
import Data.Bitraversable ( bisequence, bimapM )
import Data.Foldable ( foldrM )
import Data.Function ( on )
import Data.List qualified as List
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Control.Monad.Except
import Control.Monad.Trans.Except (throwE)

-- = Scoping context
-- The scoping context keeps track of variable and indentifier names.

-- == Internals
-- These should not be manipulated directly. See interface below.

-- | Keys that keep track of variable names.
data VarKey
  = TVar String -- ^ Key for type variable names.
  | EVar String -- ^ Key for expression variable names.
  deriving (Eq,Ord,Show)

-- | The part of the context that keeps track of variable names.
type VarCtx = Map.Map VarKey Variable

-- | Keys that keep track of identifier names.
data IdKey
  = TId String  -- ^ Key for @type@ names
  | DId String  -- ^ Key for @data@ names
  | CId String  -- ^ Key for @data@ constructor names
  | KSig String -- ^ Key for kind signatures
  deriving (Eq,Ord,Show)

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
--     * 'lookupTVar' for type variables;
--     * 'lookupEVar' for expression variables.
lookupTVar, lookupEVar
  :: Variable -> ScopingCtx -> Maybe Variable
lookupTVar a = Map.lookup (TVar $ external a) . snd
lookupEVar x = Map.lookup (EVar $ external x) . snd

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
fromTVarList, fromEVarList
  :: [Variable] -> ScopingCtx
fromTVarList = (Map.empty,) . Map.fromList . map (\a -> (TVar $ external a, a))
fromEVarList = (Map.empty,) . Map.fromList . map (\x -> (EVar $ external x, x))

-- | Convert to a list of expression variables.
toEVarList :: ScopingCtx -> [Variable]
toEVarList (_, vctx) = 
  Map.elems $ Map.filterWithKey (\cases EVar{} _ -> True ; _ _ -> False) vctx

toTVarList :: ScopingCtx -> [Variable]
toTVarList (_, vctx) = 
  Map.elems $ Map.filterWithKey (\cases TVar{} _ -> True ; _ _ -> False) vctx

-- | Insert a variable name in the context. Use
-- 
--     * 'insertTVar' for type variables
--     * 'insertEVar' for expression variables
insertTVar, insertEVar :: Variable -> ScopingCtx -> ScopingCtx
insertTVar a = second $ Map.insert (TVar $ external a) a
insertEVar x = second $ Map.insert (EVar $ external x) x

-- | Delete a variable name from the context. Use
-- 
--     * 'deleteTVar' for type variables;
--     * 'deleteEVar' for expression variables.
deleteTVar, deleteEVar :: Variable -> ScopingCtx -> ScopingCtx
deleteTVar a = second $ Map.delete (TVar $ external a)
deleteEVar x = second $ Map.delete (EVar $ external x)

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

-- | Run a scoping procedure on a given value, returning either:
-- 
--     * a list of errors, if any was encountered;
--     * the result of the scoping procedure, otherwise.
runScoping :: (ScopingCtx -> a -> FreeST b) -> a -> Either [Error] b
runScoping f x =
  let (x', FreeSTState{errors}) = runState (runExceptT $ f emptyScopingCtx x) emptyValidationState
  in case x' of
    Left e -> Left (errors ++ [e])
    Right x'' | null errors -> Right x'' 
              | otherwise   -> Left errors

-- | Increment the fresh internal variable name counter, returning the previous
-- value.
incCounter :: FreeST Int
incCounter = do
  c <- gets counter
  modify (\s -> s{counter=succ (counter s)})
  return c

-- | Update the internal name of a variable with a fresh name.
freshInternal :: Variable -> FreeST Variable
freshInternal x = incCounter >>= \i -> return x{internal = i}

-- = Scoping procedures

-- | Run scoping on a module, returning either:
-- 
--     * a list of errors, if any was encountered;
--     * the scoped module, otherwise.
runScopeModule :: M.ParsedModule -> Either [Error] M.ScopedModule
runScopeModule = runScoping scopeModule

-- | Scope a module, returning also the resulting context.
scopeModule' :: ScopingCtx -> M.ParsedModule -> FreeST (ScopingCtx, M.ScopedModule)
scopeModule' ctx m = do
  (ctx, kss') <- scopeKindSigs ctx (M.kindSigs m)
  (ctx, tds', dds') <- scopeTypeDataDecls ctx (M.typeDecls m) (M.dataDecls m)
  (ctx, cds') <- scopeConsDecls ctx dds' (M.consDecls m)
  (ctx, ds' ) <- scopeDefs      ctx (M.definitions m)
  return (ctx, m{ M.kindSigs    = kss'
                , M.typeDecls   = tds'
                , M.dataDecls   = dds'
                , M.consDecls   = cds'
                , M.definitions = ds'
                })

-- | Scope a module.
scopeModule :: ScopingCtx -> M.ParsedModule -> FreeST M.ScopedModule
scopeModule ctx m = snd <$> scopeModule' ctx m

-- | Update a scoping context with a list of kind signatures
-- (Kind signatures themselves do not need scoping).
scopeKindSigs :: ScopingCtx -> M.KindSigs Parsed -> FreeST (ScopingCtx, M.KindSigs Scoped)
scopeKindSigs ctx kss = do
  let (es, ctx') = foldr scopeKindSigs' (Map.empty, ctx) kss
  forM_ es (\is -> when (length is > 1) $
    throwE (MultipleKindSigs (getSpan (head is)) is))
  return (ctx', Map.fromList kss)
  where
   scopeKindSigs' (i, k) (es, ctx) = (Map.insertWith (++) i [i] es, insertKSig i ctx)

-- | Insert @data@ and @type@ names in the scoping context, checking for
-- duplicate declarations in the process.
scopeTypeDataDecls :: ScopingCtx 
                   -> M.TypeDecls Parsed
                   -> M.DataDecls Parsed
                   -> FreeST (ScopingCtx, M.TypeDecls Scoped, M.DataDecls Scoped)
scopeTypeDataDecls ctx tds dds = do
  let (es , ctx' ) = foldr (\(ti, _) -> bimap (Map.insertWith (++) ti [ti]) 
                                              (insertTId ti)) 
                           (es, ctx) tds
      (es', ctx'') = foldr (\(ti, _) -> bimap (Map.insertWith (++) ti [ti]) 
                                              (insertDId ti)) 
                           (Map.empty, ctx') dds
  forM_ es' \is -> when (length is > 1) $
    throwE (MultipleTypeDecls (getSpan (head is)) is)
  (ctx''' , tds') <- scopeTypeDecls ctx''  tds
  (ctx'''', dds') <- scopeDataDecls ctx''' dds
  return (ctx'''', tds', dds')

-- | Check for duplicate data constructor declarations
scopeConsDecls :: ScopingCtx
               -> M.DataDecls Scoped
               -> M.ConsDecls Parsed 
               -> FreeST (ScopingCtx, M.ConsDecls Scoped)
scopeConsDecls ctx dds cds = do
  let (es , ctx') = foldr (\(ci, _) -> bimap (Map.insertWith (++) ci [ci]) 
                                              (insertCId ci)) 
                          (Map.empty, ctx) cds
  forM_ es \is -> when (length is > 1) $
    throwE (MultipleConsDecls (getSpan (head is)) is)
  (ctx',) <$> foldM (scopeConsDecl ctx') Map.empty cds
  where
    scopeConsDecl :: ScopingCtx -> M.ConsDecls Scoped -> (Identifier, (Identifier, [T.Type Parsed])) -> FreeST (M.ConsDecls Scoped)
    scopeConsDecl ctx' cds' (ci, (di, ts)) = do
      let as = map fst (fst (dds Map.! di))
      ts' <- mapM (scopeType (fromTVarList as `union` ctx')) ts
      return (Map.insert ci (di, ts') cds')

-- | Scope a list of @data@ declarations, returning also the updated scoping
-- context.
scopeDataDecls :: ScopingCtx 
               -> M.DataDecls Parsed
               -> FreeST (ScopingCtx, M.DataDecls Scoped)
scopeDataDecls ctx = foldM scopeDataDecl (ctx, Map.empty)
  where
    scopeDataDecl (ctx', dds') dd@(ti, (unzip -> (as, ks), cis)) = do
        unless (ti `memberKSig` ctx) do
          throwE (LacksKindSig (getSpan ti) ti)
        as'  <- mapM freshInternal as 
        ks'  <- mapM scopeKind ks
        return (ctx', Map.insert ti (zip as' ks', cis) dds')
    scopeConsDecls ctx = foldM (scopeConsDecl ctx) Map.empty
      where
        scopeConsDecl ctx cds' (ci, ts) = do
          ts' <- mapM (scopeType ctx) ts 
          return (Map.insert ci ts' cds')

-- | Scope a list of @type@ declarations, returning also the updated scoping 
-- context.
scopeTypeDecls :: ScopingCtx 
               -> M.TypeDecls Parsed
               -> FreeST (ScopingCtx, M.TypeDecls Scoped)
scopeTypeDecls ctx = foldM scopeTypeDecl (ctx, Map.empty)
  where
    scopeTypeDecl (ctx', tds') (ti, t) = do
      unless (memberKSig ti ctx') (throwE (LacksKindSig (getSpan ti) ti))
      t'  <- scopeType ctx' t
      return (ctx', Map.insert ti t' tds')
    
-- | Scope a list of @let@ declarations, returning also the updated scoping 
-- context. Besides scoping the variables, this procedure also groups function
-- equations and detects signatures without accompanying definitions.
scopeDefs :: ScopingCtx -> [E.ParsedLetDecl] -> FreeST (ScopingCtx, [E.ScopedLetDecl])
scopeDefs ctx ds = do    
  (ictx, ctx, ds) <- scopeDefs' False ctx emptyScopingCtx (groupEquations ds)
  forM_ (toEVarList ictx) (\x -> throwE (SigLacksDef (getSpan x) x))
  return (ctx, ds)
  where
    groupEquations = \case 
      []  -> []
      [d] -> [d]
      (E.FnDef f1 psrhss1 : E.FnDef f2 psrhss2 : ds) 
        | external f1 == external f2 -> 
          groupEquations (E.FnDef f1 (psrhss1 ++ psrhss2) : ds)
      (E.Mutual ds' : ds) -> E.Mutual (groupEquations ds') : groupEquations ds
      (d1:d2:ds) -> d1 : groupEquations (d2:ds)

    scopeDefs' isMutual ctx ictx = \case 
      [] -> return (ictx, ctx, [])
      (E.ValDef p rhs : ds) -> do
        checkConflictingDefs [ExpLevel p]
        (ictx', p') <- scopePat ctx ictx p
        rhs' <- scopeRHS ctx rhs
        let ctx'' = fromEVarList (Set.toList $ patVars p')
        let ctx' = ctx'' `union` ctx
        second (E.ValDef p' rhs':) <$> scopeDefs' isMutual ctx' ictx' ds
      (E.FnDef x psrhss : ds) -> do
        (ictx', x') <- case lookupEVar x ictx of
          Nothing -> (ictx,) <$> freshInternal x
          Just x' -> pure (deleteEVar x ictx, x{internal = internal x'})
        let ctx' = insertEVar x' ctx
        psrhss' <- forM psrhss \(pars, rhs) -> do
          checkConflictingDefs (ExpLevel (E.VarPat (getSpan x') x') : pars)
          (ctx'', pars') <- foldM scopeParam (ctx',[]) pars
          (pars',) <$> scopeRHS ctx'' rhs
        second (E.FnDef x' psrhss' :) <$> scopeDefs' isMutual ctx' ictx' ds
        where
          scopeParam (ctx',pars') (ExpLevel  p) = do
            (_, p') <- scopePat ctx' emptyScopingCtx p
            let ctx'' = fromEVarList (Set.toList (patVars p')) `union` ctx'
            return (ctx'', pars'++[ExpLevel p'])
          scopeParam (ctx',pars') (TypeLevel a) = do
            a' <- freshInternal a
            let ctx'' = insertTVar a' ctx'
            return (ctx'', pars'++[TypeLevel a'])
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
        forM_ (toEVarList ictx') (\x -> throwE (SigLacksDef (getSpan x) x))
        second (E.Mutual ds'' :) <$> scopeDefs' True ctx' ictx ds

-- | Scope a right-hand side.
scopeRHS :: ScopingCtx -> E.ParsedRHS -> FreeST E.ScopedRHS
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
scopeExp :: ScopingCtx -> E.ParsedExp -> FreeST E.ScopedExp
scopeExp ctx = \case
  E.Var s x -> case lookupEVar x ctx of
    Nothing -> {- throwE (OutOfScope (getSpan x) x) -} -- leaving this for the typechecker
      pure $ E.Var s x
    Just x' -> pure $ E.Var s x{internal = internal x'}
  E.App s e args ->
    E.App s <$> scopeExp ctx e
            <*> forM args (\case 
                  ExpLevel  e -> ExpLevel  <$> scopeExp ctx e
                  TypeLevel t -> TypeLevel <$> scopeType ctx t)
  E.Abs s pars m e -> do
    checkConflictingDefs (map (bimap fst fst) pars)
    let (ps, ts) = (bimap (map fst) (map fst) . partitionLevels) pars
    (ctx',pars') <- foldM scopeTypedParam (ctx,[]) pars
    E.Abs s pars' m <$> scopeExp ctx' e
    where
      scopeTypedParam (ctx',pars') (ExpLevel  (p,t)) = do
        (_, p') <- scopePat ctx' emptyScopingCtx p
        t' <- scopeType ctx' t
        let ctx'' = fromEVarList (Set.toList (patVars p')) `union` ctx'
        return (ctx'', pars'++[ExpLevel (p',t')])
      scopeTypedParam (ctx',pars') (TypeLevel (a,k)) = do
        a' <- freshInternal a
        k' <- scopeKind k
        let ctx'' = insertTVar a' ctx'
        return (ctx'', pars'++[TypeLevel (a',k')])
  E.Let s ds e -> do
    (ctx', ds') <- scopeDefs ctx ds
    E.Let s ds' <$> scopeExp ctx' e
  E.Semi s e1 e2 -> 
    E.Semi s <$> scopeExp ctx e1 <*> scopeExp ctx e2
  E.Case s e prhss -> do
    e' <- scopeExp ctx e
    E.Case s e' <$> mapM scopePatRHS prhss
    where
      scopePatRHS :: (E.ParsedPat, E.ParsedRHS) -> FreeST (E.ScopedPat, E.ScopedRHS)
      scopePatRHS (p,rhs) = do
        checkConflictingDefs [ExpLevel p]
        (_, p') <- scopePat ctx emptyScopingCtx p
        let pvs = Set.toList $ patVars p'
        let ctx' = fromEVarList pvs `union` ctx
        (p',) <$> scopeRHS ctx' rhs
  E.If s e1 e2 e3 ->
    E.If s <$> scopeExp ctx e1 <*> scopeExp ctx e2 <*> scopeExp ctx e3
  E.Channel s t ->
    E.Channel s <$> scopeType ctx t
  -- TODO: organize these
  E.Int s x -> pure $ E.Int s x
  E.Float s x -> pure $ E.Float s x
  E.Char s x -> pure $ E.Char s x
  E.DCons s i -> pure $ E.DCons s i
  E.Select s i -> pure $ E.Select s i

-- | Scope a pattern. This function takes two contexts: the first being the main
-- lexical context, and the second being an auxilliary context for 'let' definitions,
-- which is used to match signatures to definitions. It returns the modified
-- auxilliary context (i.e., the lexical context must be modified separately!)
scopePat :: ScopingCtx -- main context
         -> ScopingCtx -- auxilliary context
         -> E.ParsedPat
         -> FreeST (ScopingCtx, E.ScopedPat) -- returns the auxilliary context
scopePat ctx ictx = \case
  E.WildPat s w -> (ictx,) . E.WildPat s <$> freshInternal w
  E.VarPat s x  -> case lookupEVar x ictx of
    Just x' -> pure (deleteEVar x ictx, E.VarPat s x{internal = internal x'})
    Nothing -> (ictx,) . E.VarPat s <$> freshInternal x
  E.DConsPat s c ps -> do
    (ictx', ps') <- foldM (\(ictx'',ps'') p -> do
        (ictx''', p') <- scopePat ctx ictx'' p
        return (ictx''', ps''++[p']))
      (emptyScopingCtx, []) ps
    return (ictx', E.DConsPat s c ps')
  E.ChoicePat s c p -> do
    second (E.ChoicePat s c) <$> scopePat ctx ictx p
  E.AsPat s x p -> case lookupEVar x ictx of
    Nothing -> do
      x' <- freshInternal x
      second (E.AsPat s x') <$> scopePat ctx ictx p
    Just x' -> second (E.AsPat s x{internal = internal x'}) 
      <$> scopePat ctx (deleteEVar x ictx) p
  -- TODO: organize these
  E.IntPat s x -> pure (ictx, E.IntPat s x)
  E.FloatPat s x -> pure (ictx, E.FloatPat s x)
  E.CharPat s x -> pure (ictx, E.CharPat s x)

-- | Check conflicting definitions for bindings.
checkConflictingDefs :: [Level E.ParsedPat Variable] -> FreeST ()
checkConflictingDefs (partitionLevels -> (ps, as)) = do
  let evos = Map.unionsWith (++) (map patVarOccurs ps)
      tvos = varOccurs as
  forM_ (Map.assocs $ Map.union evos tvos) \(xa, ss) -> 
    when (length ss > 1) $ throwE (ConflictingDefs (ss !! 1) xa ss)
  where
    varOccurs = foldr (\a occs -> 
        Map.insertWith (++) (TypeLevel $ external a) [getSpan a] occs) 
      Map.empty
    patVarOccurs = \case
      E.VarPat s x      -> Map.singleton (ExpLevel $ external x) [getSpan x]
      E.DConsPat _ _ ps -> Map.unionsWith (++) (map patVarOccurs ps)
      E.ChoicePat _ _ p -> patVarOccurs p
      E.AsPat _ x p     -> Map.insertWith (++) (ExpLevel $ external x) 
                             [getSpan x] (patVarOccurs p)
      _                 -> Map.empty

-- | The set of variables in a pattern.
patVars :: E.Pat x -> Set.Set Variable
patVars = \case
  E.VarPat _ x      -> Set.singleton x
  E.DConsPat s _ ps -> Set.unions (map patVars ps)
  E.ChoicePat _ _ p -> patVars p
  E.AsPat _ x p     -> Set.insert x (patVars p)
  _                 -> Set.empty

-- | Generate a fresh kind inference variable.
freshKVar :: Located a => a -> FreeST K.Kind
freshKVar (getSpan -> s) = do
  i <- incCounter
  return $ K.Var s (Variable s  ("τ"++show i) i)

-- | Scope a type.
scopeType :: ScopingCtx -> T.ParsedType -> FreeST T.ScopedType
scopeType ctx = \case
  T.Arrow s x m -> T.Arrow s x <$> scopeMultiplicity m
  T.Message s x m p -> T.Message s x <$> scopeMultiplicity m <*> pure p
  T.Choice  s x m p ls -> do
    m' <- scopeMultiplicity m
    let ds = foldr (\i -> Map.insertWith (++) i [i]) Map.empty ls
    forM_ ds \ids -> when (length ids > 1) $
      throwE (MultipleFieldDecls (getSpan (head ids)) ids)
    return $ T.Choice s x m' p ls
  T.Abs s x (unzip -> (as, ks)) t -> do
    as' <- mapM freshInternal as
    ks' <- mapM scopeKind ks
    T.Abs s x (zip as' ks') <$> scopeType (fromTVarList as' `union` ctx) t
  t@(T.Var s x a) ->
    case lookupTVar a ctx of
      Just a' -> return $ T.Var s x a{internal = internal a'}
      Nothing -> T.Var s x <$> freshInternal a
  T.App s x t ts ->
    T.App s x <$> scopeType ctx t <*> mapM (scopeType ctx) ts
  T.TName s x i 
    | memberDId i ctx -> return (T.DName s x i)
    | otherwise       -> return (T.TName s x i)
  T.DName s x i -> return (T.DName s x i)
  -- TODO: organize these
  T.Skip s x -> pure $ T.Skip s x
  T.End s x p -> pure $ T.End s x p
  T.Quant s x p -> pure $ T.Quant s x p
  T.Int s x -> pure $ T.Int s x
  T.Float s x -> pure $ T.Float s x
  T.Char s x -> pure $ T.Char s x
  T.Semi s x -> pure $ T.Semi s x
  T.Dual s x -> pure $ T.Dual s x

-- | Scope a type, universally quantifying any free variables it might have
-- with a fresh kind inference variable.
scopeAndQuantifyType :: ScopingCtx -> T.ParsedType -> FreeST T.ScopedType
scopeAndQuantifyType ctx t = do
  t' <- scopeType ctx t
  let fvt' = Set.toList (freeVars t' Set.\\ Set.fromList (toTVarList ctx))        
  if null fvt'
    then return t'
    else do
      aks <- mapM (\a -> (a,) <$> freshKVar a) 
        $ List.sortBy (compare `on` getSpan) fvt'
      scopeType ctx $ T.AppForall (getSpan t) (T.getExt t) aks t

-- | Scope a kind.
scopeKind :: K.Kind -> FreeST K.Kind
scopeKind = \case
    K.Arrow s k1 k2 -> K.Arrow s  <$> scopeKind k1 <*> scopeKind k2
    K.Proper s m pk -> K.Proper s <$> scopeMultiplicity m  <*> scopePrekind pk
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
scopeMultiplicity :: K.Multiplicity -> FreeST K.Multiplicity
scopeMultiplicity = \case
  K.VarM φ -> do
    φ' <- freshInternal φ
    return $ K.VarM φ'{external = "φ" ++ show (internal φ')}
  m -> pure m

