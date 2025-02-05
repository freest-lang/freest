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
  ,ScopingCtx
  ,runScoping
  ,scopeModule
  ,scopeModule_
  ,scopeType
  ,scopeKind
  )
where

import           Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import qualified Syntax.Module as M
import           Validation.Substitution (freeVars)
import qualified Syntax.Type as T
import           UI.Error (Error(..))

import           Control.Monad (replicateM, forM, void, forM_, unless, foldM, when)
import           Control.Monad.State ( gets, modify, State, runState)
import           Data.Bifunctor (first, second, bimap)
import           Data.Bitraversable (bisequence, bimapM)
import           Data.Foldable (foldrM)
import           Data.Function (on)
import qualified Data.List as List
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Control.Monad.Extra (ifM)

data ScopingKey
  = TVar String
  | EVar String
  | KSig String
  | TId String
  | DId String
  | CId String
  deriving (Eq,Ord,Show)

type ScopingCtx = Map.Map ScopingKey Int

lookupTVar, lookupEVar
  :: Variable -> ScopingCtx -> Maybe Int
lookupTVar a = Map.lookup $ TVar $ external a
lookupEVar x = Map.lookup $ EVar $ external x

memberKSig, memberCId, memberTId, memberDId
  :: Identifier -> ScopingCtx -> Bool
memberKSig (Identifier _ s) ctx = KSig s `Map.member` ctx
memberCId  (Identifier _ s) ctx = CId  s `Map.member` ctx
memberTId  (Identifier _ s) ctx = TId  s `Map.member` ctx
memberDId  (Identifier _ s) ctx = DId  s `Map.member` ctx

fromTVarList, fromEVarList
  :: [Variable] -> ScopingCtx
fromTVarList = Map.fromList . map (\a -> (TVar $ external a, internal a))
fromEVarList = Map.fromList . map (\x -> (EVar $ external x, internal x))

insertTVar, insertEVar, deleteTVar, deleteEVar
  :: Variable -> ScopingCtx -> ScopingCtx
insertTVar a = Map.insert (TVar $ external a) (internal a)
insertEVar x = Map.insert (EVar $ external x) (internal x)
deleteTVar a = Map.delete (TVar $ external a)
deleteEVar x = Map.delete (EVar $ external x)

insertKSig, insertCId, insertTId, insertDId
  :: Identifier -> ScopingCtx -> ScopingCtx
insertKSig (Identifier _ s) = Map.insert (KSig s) defaultInternal
insertCId  (Identifier _ s) = Map.insert (CId  s) defaultInternal
insertTId  (Identifier _ s) = Map.insert (TId  s) defaultInternal
insertDId  (Identifier _ s) = Map.insert (DId  s) defaultInternal

type Scoping = State ScopingState

data ScopingState = ScopingState{counter :: Int, errors :: [Error]}

runScoping :: (ScopingCtx -> a -> Scoping b) -> a -> Either [Error] b
runScoping f x =
  let (x',s) = runState (f Map.empty x) (ScopingState firstInternal [])
  in if null (errors s) then Right x' else Left (errors s)

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
  ctx' <- scopeKindSigs ctx (M.kindSigs m)
  (ctx''  , dataDecls'  ) <- scopeDataDecls ctx'   (M.dataDecls   m)
  (ctx''' , typeDecls'  ) <- scopeTypeDecls ctx''  (M.typeDecls   m)
  (ctx'''', definitions') <- scopeDefs      ctx''' (M.definitions m)
  return (ctx'''', m{ M.dataDecls   = dataDecls'
                    , M.typeDecls   = typeDecls'
                    , M.definitions = definitions'
                    })

scopeModule_ :: ScopingCtx -> M.Module -> Scoping M.Module
scopeModule_ ctx m = snd <$> scopeModule ctx m

scopeKindSigs :: ScopingCtx -> M.KindSigList -> Scoping ScopingCtx
scopeKindSigs = foldM scopeKindSig
  where
    scopeKindSig ctx (is, k) = 
      foldM (\ctx i -> do 
          when (memberKSig i ctx) 
            (insertError (MultipleKindSigs (getSpan i) i))
          return (insertKSig i ctx)) 
        ctx is

scopeDataDecls :: ScopingCtx -> M.DataDeclList -> Scoping (ScopingCtx, M.DataDeclList)
scopeDataDecls ctx dds = do
  ctx' <- foldM (\ctx'' (ti, _) -> do
      when (memberTId ti ctx'' || memberDId ti ctx'') 
        do insertError (MultipleTypeDecls (getSpan ti) ti)
      return $ insertDId ti ctx'')
    ctx dds
  foldM scopeDataDecl (ctx', []) dds
  where
    scopeDataDecl (ctx',dds') dd@(ti, (as, cds)) = do
        unless (ti `memberKSig` ctx) (insertError (LacksKindSig (getSpan ti) ti))
        as' <- mapM freshInternal as 
        (ctx''',cds') <- scopeConsDecls (Map.union (fromTVarList as') ctx') cds
        return (ctx''', (ti, (as', cds')) : dds')
    scopeConsDecls ctx = foldM scopeConsDecl (ctx, [])
      where
        scopeConsDecl (ctx',cds') (ci,ts)
          | memberCId ci ctx' = do
            insertError (MultipleConsDecls (getSpan ci) ci)
            return (ctx', (ci, ts) : cds')
          | otherwise = do
            ts' <- mapM (scopeType ctx') ts
            let ctx'' = insertCId ci ctx'
            return (ctx'', (ci, ts') : cds')

scopeTypeDecls :: ScopingCtx -> M.TypeDeclList -> Scoping (ScopingCtx, M.TypeDeclList)
scopeTypeDecls ctx tds = do
  ctx' <- foldM (\ctx'' (ti, _) -> do 
      when (ti `memberTId` ctx'' || ti `memberDId` ctx'') 
        do insertError (MultipleTypeDecls (getSpan ti) ti)
      return $ insertTId ti ctx'') 
    ctx tds
  foldM scopeTypeDecl (ctx', []) tds
  where
    scopeTypeDecl (ctx', tds') td@(ti, (as, t)) = do
      unless (ti `memberKSig` ctx') (insertError (LacksKindSig (getSpan ti) ti))
      as' <- mapM freshInternal as
      t'  <- scopeType (fromTVarList as' `Map.union` ctx') t
      return (ctx', (ti, (as', t')) : tds')

scopeDefs :: ScopingCtx -> [E.LetDecl] -> Scoping (ScopingCtx, [E.LetDecl])
scopeDefs ctx = scopeDefs' ctx Map.empty . groupEquations
  where
    groupEquations :: [E.LetDecl] -> [E.LetDecl]
    groupEquations = \case 
      []  -> []
      [d] -> [d]
      (E.FnDef f1 psrhss1 : E.FnDef f2 psrhss2 : ds) 
        | external f1 == external f2 -> 
          groupEquations (E.FnDef f1 (psrhss1 ++ psrhss2) : ds)
      (d1:d2:ds) -> d1 : groupEquations (d2:ds)

    scopeDefs' :: ScopingCtx -> ScopingCtx -> [E.LetDecl] -> Scoping (ScopingCtx, [E.LetDecl])
    scopeDefs' ctx ictx = \case 
      [] -> return (ctx, [])
      (E.ValDef p rhs : ds) -> do
        checkConflictingDefs [ExpLevel p]
        (ictx', p') <- scopePat ctx ictx p
        rhs' <- scopeRHS ctx rhs
        let ctx'' = fromEVarList (Set.toList $ patVars p')
        let ctx' = ctx'' `Map.union` ctx
        second (E.ValDef p' rhs':) <$> scopeDefs' ctx' ictx' ds
      (E.FnDef x psrhss : ds) -> do
        (ictx', x') <- case lookupEVar x ictx of
          Nothing -> (ictx,) <$> freshInternal x
          Just internal -> pure (deleteEVar x ictx, x{internal})
        let ctx' = insertEVar x' ctx
        psrhss' <- forM psrhss \(pars, rhs) -> do
          checkConflictingDefs (ExpLevel (E.VarPat (getSpan x') x') : pars)
          (ctx'', pars') <- foldM scopeParam (ctx',[]) pars
          (pars',) <$> scopeRHS ctx'' rhs
        second (E.FnDef x' psrhss' :) <$> scopeDefs' ctx' ictx' ds
        where
          scopeParam (ctx',pars') (ExpLevel  p) = do
            (_, p') <- scopePat ctx' Map.empty p
            let ctx'' = fromEVarList (Set.toList (patVars p')) `Map.union` ctx'
            return (ctx'', pars'++[ExpLevel p'])
          scopeParam (ctx',pars') (TypeLevel a) = do
            a' <- freshInternal a
            let ctx'' = insertTVar a' ctx'
            return (ctx'', pars'++[TypeLevel a'])
      (E.TypeSig xs t : ds) -> do
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
        second (E.TypeSig xs' t':) <$> scopeDefs' ctx ictx' ds

scopeRHS :: ScopingCtx -> E.RHS -> Scoping E.RHS
scopeRHS ctx = \case
  E.GuardedRHS ges Nothing   ->
    E.GuardedRHS <$> mapM (bimapM (scopeExp ctx) (scopeExp ctx)) ges <*> pure Nothing
  E.GuardedRHS ges (Just ds) -> do
    (ctx',ds') <- scopeDefs ctx ds
    E.GuardedRHS <$> mapM (bimapM (scopeExp ctx') (scopeExp ctx')) ges <*> pure (Just ds')
  E.UnguardedRHS e Nothing   ->
    E.UnguardedRHS <$> scopeExp ctx e <*> pure Nothing
  E.UnguardedRHS e (Just ds) -> do
    (ctx',ds') <- scopeDefs ctx ds
    E.UnguardedRHS <$> scopeExp ctx' e <*> pure (Just ds')

scopeExp :: ScopingCtx -> E.Exp -> Scoping E.Exp
scopeExp ctx = \case
  e@(E.Var s x) -> case lookupEVar x ctx of
    Nothing -> {- insertError (OutOfScope (getSpan x) x) -} -- leaving this for the typechecker
      pure e
    Just internal -> pure $ E.Var s x{internal}
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
        (_, p') <- scopePat ctx' Map.empty p
        t' <- scopeType ctx' t
        let ctx'' = fromEVarList (Set.toList (patVars p')) `Map.union` ctx'
        return (ctx'', pars'++[ExpLevel (p',t')])
      scopeTypedParam (ctx',pars') (TypeLevel (a,k)) = do
        a' <- freshInternal a
        k' <- scopeKind k
        let ctx'' = insertTVar a' ctx'
        return (ctx'', pars'++[TypeLevel (a',k')])
  E.Let s ds e -> do
    (ctx', ds') <- scopeDefs ctx ds
    E.Let s ds' <$> scopeExp ctx' e
  E.Case s e prhss -> do
    e' <- scopeExp ctx e
    E.Case s e' <$> mapM scopePatRHS prhss
    where
      scopePatRHS :: (E.Pat, E.RHS) -> Scoping (E.Pat, E.RHS)
      scopePatRHS (p,rhs) = do
        checkConflictingDefs [ExpLevel p]
        (_,p') <- scopePat ctx Map.empty p
        let pvs = Set.toList $ patVars p'
        let ctx' = fromEVarList pvs `Map.union` ctx
        (p',) <$> scopeRHS ctx' rhs
  E.If s e1 e2 e3 ->
    E.If s <$> scopeExp ctx e1 <*> scopeExp ctx e2 <*> scopeExp ctx e3
  E.Channel s t ->
    E.Channel s <$> scopeType ctx t
  E.Select s i e ->
    E.Select s i <$> scopeExp ctx e
  e -> pure e

-- | Scopes a pattern. This function takes two contexts: the first being the main
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
    Just internal -> pure (deleteEVar x ictx, E.VarPat s x{internal})
    Nothing -> (ictx,) . E.VarPat s <$> freshInternal x
  E.DConsPat s c ps -> do
    (ictx', ps') <- foldM (\(ictx'',ps'') p -> do
        (ictx''', p') <- scopePat ctx ictx'' p
        return (ictx''', ps''++[p']))
      (Map.empty, []) ps
    return (ictx', E.DConsPat s c ps')
  E.AsPat s x p -> case lookupEVar x ictx of
    Nothing -> do
      x' <- freshInternal x
      second (E.AsPat s x') <$> scopePat ctx ictx p
    Just internal -> second (E.AsPat s x{internal}) <$> scopePat ctx (deleteEVar x ictx) p
  p -> pure (ictx, p)

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
      E.DConsPat _ _ ps -> Map.unionsWith (++) (map patVarOccurs ps)
      E.AsPat _ x p    -> Map.insertWith (++) (ExpLevel $ external x) [getSpan x] (patVarOccurs p)
      _                -> Map.empty

patVars :: E.Pat -> Set.Set Variable
patVars = \case
  E.VarPat _ x     -> Set.singleton x
  E.DConsPat s _ ps -> Set.unions (map patVars ps)
  E.AsPat _ x p    -> Set.insert x (patVars p)
  _                -> Set.empty

freshKVar :: Located a => a -> Scoping K.Kind
freshKVar l = do
  phi <- incCounter >>= \i -> return (Variable (getSpan l) ("φ"++show i) i)
  psi <- incCounter >>= \i -> return (Variable (getSpan l) ("ψ"++show i) i)
  return $ K.Proper (getSpan l) (K.VarM phi) (K.VarPK psi)

scopeType :: ScopingCtx -> T.Type -> Scoping T.Type
scopeType ctx = \case
  -- Functional types
  T.Arrow s m -> T.Arrow s <$> scopeMultiplicity m
  -- Session types
  T.Message s m p -> T.Message s <$> scopeMultiplicity m <*> pure p
  T.Choice  s m p lts ->
    let lts' = mapM (\(l,t) -> (l,) <$> scopeType ctx t) lts
    in T.Choice s <$> scopeMultiplicity m <*> pure p <*> lts'
  -- Polymorphism
  T.Quant s p a k t -> do
    a' <- freshInternal a
    k' <- scopeKind k
    let ctx' = insertTVar a' ctx
    T.Quant s p a' k' <$> scopeType ctx' t
  -- Higher-order
  t@(T.Var s a) ->
    case lookupTVar a ctx of
      Just internal  -> return $ T.Var s a{internal}
      Nothing -> T.Var s <$> freshInternal a -- no error here; leave it for the typechecker
  T.App s t ts ->
    T.App s <$> scopeType ctx t <*> mapM (scopeType ctx) ts
  -- Equations
  T.TName s i 
    | memberDId i ctx -> return (T.DName s i)
    | otherwise       -> return (T.TName s i)
  T.DName s i -> return (T.DName s i)
  t -> pure t

scopeTypeQ :: ScopingCtx -> T.Type -> Scoping T.Type
scopeTypeQ ctx t = do
  t' <- scopeType ctx t
  let fvm = Map.fromList (map (\a -> (TVar $ external a, a)) 
                              (Set.toList (freeVars t')))
  if Map.null fvm
    then scopeType ctx t
    else do
      aks <- mapM (\a -> (a,) <$> freshKVar a) 
        $ List.sortBy (compare `on` getSpan) $ Map.elems fvm
      T.variadicQuant (getSpan t) T.In aks 
        <$> scopeType (Map.map internal fvm `Map.union` ctx) t'

scopeKind :: K.Kind -> Scoping K.Kind
scopeKind = \case
    K.Arrow s k1 k2 -> K.Arrow s  <$> scopeKind k1 <*> scopeKind k2
    K.Proper s m pk -> K.Proper s <$> scopeMultiplicity m  <*> scopePrekind pk
  where 
    scopePrekind (K.VarPK psi) = do
      psi' <- freshInternal psi
      return $ K.VarPK psi'{external="φ"++show (internal psi')}
    scopePrekind pk = pure pk

scopeMultiplicity :: K.Multiplicity -> Scoping K.Multiplicity
scopeMultiplicity = \case
  K.VarM φ -> do
    φ' <- freshInternal φ
    return $ K.VarM φ'{external="φ"++show (internal φ')}
  m -> pure m

