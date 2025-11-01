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
  (Scoping
  ,ScopingState(..)
  ,emptyScopingState
  ,ScopingCtx
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
import Validation.Rename ( rename )
import Validation.Substitution ( freeVars )
import Syntax.Type qualified as T
import UI.Error ( Error(..) )

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

-- = Scoping state

-- | The scoping state. Keeps track of:
--
--     * a counter to generate fresh variable names;
--     * a list of errors thrown during the scoping process.
data ScopingState = ScopingState{counter :: Int, errors :: [Error]}

emptyScopingState :: ScopingState
emptyScopingState = ScopingState firstInternal []

-- | The Scoping monad, a State monad carrying a ScopingState.
type Scoping = State ScopingState

-- | Run a scoping procedure on a given value, returning either:
-- 
--     * a list of errors, if any was encountered;
--     * the result of the scoping procedure, otherwise.
runScoping :: (ScopingCtx -> a -> Scoping b) -> a -> Either [Error] b
runScoping f x =
  let (x', s) = runState (f emptyScopingCtx x) emptyScopingState
  in if null (errors s) then Right x' else Left (errors s)

-- | Insert an error in the scoping state.
insertError :: Error -> Scoping ()
insertError e = modify (\s -> s{errors = e : errors s})

-- | Increment the fresh internal variable name counter, returning the previous
-- value.
incCounter :: Scoping Int
incCounter = do
  c <- gets counter
  modify (\s -> s{counter=succ (counter s)})
  return c

-- | Update the internal name of a variable with a fresh name.
freshInternal :: Variable -> Scoping Variable
freshInternal x = incCounter >>= \i -> return x{internal = i}

-- = Scoping procedures

-- | Run scoping on a module, returning either:
-- 
--     * a list of errors, if any was encountered;
--     * the scoped module, otherwise.
runScopeModule :: M.Module -> Either [Error] M.Module
runScopeModule = runScoping scopeModule

-- | Scope a module, returning also the resulting context.
scopeModule' :: ScopingCtx -> M.Module -> Scoping (ScopingCtx, M.Module)
scopeModule' ctx m = do
  ctx <- checkDupKindSigs      ctx (M.kindSigs m)
  ctx <- checkDupDataTypeDecls ctx (M.dataDecls m) (M.typeDecls m)
  ctx <- checkDupConsDecls     ctx (M.dataDecls m)
  (ctx, dataDecls'  ) <- scopeDataDecls ctx (M.dataDecls   m)
  (ctx, typeDecls'  ) <- scopeTypeDecls ctx (M.typeDecls   m)
  (ctx, definitions') <- scopeDefs      ctx (M.definitions m)
  return (ctx, m{ M.dataDecls   = dataDecls'
                , M.typeDecls   = typeDecls'
                , M.definitions = definitions'
                })

-- | Scope a module.
scopeModule :: ScopingCtx -> M.Module -> Scoping M.Module
scopeModule ctx m = snd <$> scopeModule' ctx m

-- | Update a scoping context with a list of kind signatures
-- (Kind signatures themselves do not need scoping).
checkDupKindSigs :: ScopingCtx -> M.KindSigList -> Scoping ScopingCtx
checkDupKindSigs ctx kindSigs = do
  let (es, ctx') = foldr checkDupKindSigs' (Map.empty, ctx) kindSigs
  forM_ es (\is -> when (length is > 1) $
    insertError (MultipleKindSigs (getSpan (head is)) is))
  return ctx'
  where
   checkDupKindSigs' (ids, k) (err, ctx) = 
      foldr (\i -> bimap (Map.insertWith (++) i [i]) (insertKSig i))
            (err, ctx) ids

-- | Check for duplicate data and type declarations.
checkDupDataTypeDecls :: ScopingCtx -> M.DataDeclList -> M.TypeDeclList -> Scoping ScopingCtx
checkDupDataTypeDecls ctx dds tds = do
  let (es, ctx'  ) = foldr (\(ti, _, _) -> bimap (Map.insertWith (++) ti [ti]) 
                                                 (insertDId ti)) 
                           (Map.empty, ctx) dds
      (es', ctx'') = foldr (\(ti, _) -> bimap (Map.insertWith (++) ti [ti]) 
                                              (insertTId ti)) 
                           (es, ctx') tds
  forM_ es' \is -> when (length is > 1) $
    insertError (MultipleTypeDecls (getSpan (head is)) is)
  return ctx''

-- | Check for duplicate data constructor declarations
checkDupConsDecls :: ScopingCtx -> M.DataDeclList -> Scoping ScopingCtx
checkDupConsDecls ctx dds = do -- insertCId ci ctx'
  let (es, ctx') = foldr collectConsDecls (Map.empty, ctx) dds
  forM_ es \is -> when (length is > 1) $
    insertError (MultipleConsDecls (getSpan (head is)) is)
  return ctx'
  where
    collectConsDecls (_, _, cdsi) = flip (foldr collectConsDecls') cdsi
    collectConsDecls' (ci, _) = bimap (Map.insertWith (++) ci [ci]) 
                                      (insertCId ci)

-- | Scope a list of @data@ declarations, returning also the updated scoping
-- context.
scopeDataDecls :: ScopingCtx 
               -> M.DataDeclList 
               -> Scoping (ScopingCtx, M.DataDeclList)
scopeDataDecls ctx = foldM scopeDataDecl (ctx, [])
  where
    scopeDataDecl (ctx', dds') dd@(ti, unzip -> (as, ks), cds) = do
        unless (ti `memberKSig` ctx) do
          insertError (LacksKindSig (getSpan ti) ti)
        as'  <- mapM freshInternal as 
        ks'  <- mapM scopeKind ks
        cds' <- scopeConsDecls (fromTVarList as' `union` ctx') cds
        return (ctx', (ti, zip as' ks', cds') : dds')
    scopeConsDecls ctx = foldM (scopeConsDecl ctx) []
      where
        scopeConsDecl ctx cds' (ci, ts) = do
          ts' <- mapM (scopeType ctx) ts 
          return ((ci, ts') : cds')

-- | Scope a list of @type@ declarations, returning also the updated scoping 
-- context.
scopeTypeDecls :: ScopingCtx 
               -> M.TypeDeclList 
               -> Scoping (ScopingCtx, M.TypeDeclList)
scopeTypeDecls ctx tds = do
  foldM scopeTypeDecl (ctx, []) tds
  where
    scopeTypeDecl (ctx, tds') td@(ti, t) = do
      unless (memberKSig ti ctx) (insertError (LacksKindSig (getSpan ti) ti))
      t'  <- scopeType ctx t
      return (ctx, (ti, rename tdm t') : tds')
    tdm = Map.fromList tds

-- | Scope a list of @let@ declarations, returning also the updated scoping 
-- context. Besides scoping the variables, this procedure also groups function
-- equations and detects signatures without accompanying definitions.
scopeDefs :: ScopingCtx -> [E.LetDecl] -> Scoping (ScopingCtx, [E.LetDecl])
scopeDefs ctx ds = do    
  (ictx, ctx, ds) <- scopeDefs' False ctx emptyScopingCtx (groupEquations ds)
  forM_ (toEVarList ictx) (\x -> insertError (SigLacksDef (getSpan x) x))
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
        forM_ (toEVarList ictx') (\x -> insertError (SigLacksDef (getSpan x) x))
        second (E.Mutual ds'' :) <$> scopeDefs' True ctx' ictx ds

-- | Scope a right-hand side.
scopeRHS :: ScopingCtx -> E.RHS -> Scoping E.RHS
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
scopeExp :: ScopingCtx -> E.Exp -> Scoping E.Exp
scopeExp ctx = \case
  e@(E.Var s x) -> case lookupEVar x ctx of
    Nothing -> {- insertError (OutOfScope (getSpan x) x) -} -- leaving this for the typechecker
      pure e
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
      scopePatRHS :: (E.Pat, E.RHS) -> Scoping (E.Pat, E.RHS)
      scopePatRHS (p,rhs) = do
        checkConflictingDefs [ExpLevel p]
        (_,p') <- scopePat ctx emptyScopingCtx p
        let pvs = Set.toList $ patVars p'
        let ctx' = fromEVarList pvs `union` ctx
        (p',) <$> scopeRHS ctx' rhs
  E.If s e1 e2 e3 ->
    E.If s <$> scopeExp ctx e1 <*> scopeExp ctx e2 <*> scopeExp ctx e3
  E.Channel s t ->
    E.Channel s <$> scopeType ctx t
  e -> pure e

-- | Scope a pattern. This function takes two contexts: the first being the main
-- lexical context, and the second being an auxilliary context for 'let' definitions,
-- which is used to match signatures to definitions. It returns the modified
-- auxilliary context (i.e., the lexical context must be modified separately!)
scopePat :: ScopingCtx -- main context
         -> ScopingCtx -- auxilliary context
         -> E.Pat
         -> Scoping (ScopingCtx, E.Pat) -- returns the auxilliary context
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
  p -> pure (ictx, p)

-- | Check conflicting definitions for bindings.
checkConflictingDefs :: [Level E.Pat Variable] -> Scoping ()
checkConflictingDefs (partitionLevels -> (ps, as)) = do
  let evos = Map.unionsWith (++) (map patVarOccurs ps)
      tvos = varOccurs as
  forM_ (Map.assocs $ Map.union evos tvos) \(xa, ss) -> 
    when (length ss > 1) $ insertError (ConflictingDefs (ss !! 1) xa ss)
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
patVars :: E.Pat -> Set.Set Variable
patVars = \case
  E.VarPat _ x      -> Set.singleton x
  E.DConsPat s _ ps -> Set.unions (map patVars ps)
  E.ChoicePat _ _ p -> patVars p
  E.AsPat _ x p     -> Set.insert x (patVars p)
  _                 -> Set.empty

-- | Generate a fresh kind inference variable.
freshKVar :: Located a => a -> Scoping K.Kind
freshKVar (getSpan -> s) = do
  i <- incCounter
  return $ K.Var s (Variable s  ("τ"++show i) i)

-- | Scope a type.
scopeType :: ScopingCtx -> T.Type -> Scoping T.Type
scopeType ctx = \case
  T.Arrow s m -> T.Arrow s <$> scopeMultiplicity m
  T.Message s m p -> T.Message s <$> scopeMultiplicity m <*> pure p
  T.Choice  s m p ls -> do
    m' <- scopeMultiplicity m
    let ds = foldr (\i -> Map.insertWith (++) i [i]) Map.empty ls
    forM_ ds \ids -> when (length ids > 1) $
      insertError (MultipleFieldDecls (getSpan (head ids)) ids)
    return $ T.Choice s m' p ls
  T.Abs s (unzip -> (as, ks)) t -> do
    as' <- mapM freshInternal as
    ks' <- mapM scopeKind ks
    T.Abs s (zip as' ks') <$> scopeType (fromTVarList as' `union` ctx) t
  t@(T.Var s a) ->
    case lookupTVar a ctx of
      Just a' -> return $ T.Var s a{internal = internal a'}
      Nothing -> T.Var s <$> freshInternal a
  T.App s t ts ->
    T.App s <$> scopeType ctx t <*> mapM (scopeType ctx) ts
  T.TName s i 
    | memberDId i ctx -> return (T.DName s i)
    | otherwise       -> return (T.TName s i)
  T.DName s i -> return (T.DName s i)
  t -> pure t

-- | Scope a type, universally quantifying any free variables it might have
-- with a fresh kind inference variable.
scopeAndQuantifyType :: ScopingCtx -> T.Type -> Scoping T.Type
scopeAndQuantifyType ctx t = do
  t' <- scopeType ctx t
  let fvt' = Set.toList (freeVars t' Set.\\ Set.fromList (toTVarList ctx))        
  if null fvt'
    then return t'
    else do
      aks <- mapM (\a -> (a,) <$> freshKVar a) 
        $ List.sortBy (compare `on` getSpan) fvt'
      scopeType ctx $ T.AppForall (getSpan t) aks t

-- | Scope a kind.
scopeKind :: K.Kind -> Scoping K.Kind
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
scopeMultiplicity :: K.Multiplicity -> Scoping K.Multiplicity
scopeMultiplicity = \case
  K.VarM φ -> do
    φ' <- freshInternal φ
    return $ K.VarM φ'{external = "φ" ++ show (internal φ')}
  m -> pure m

