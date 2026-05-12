{- |
Module      :  Validation.Kinding
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional kinding algorithm.
-}

module Validation.Kinding
  ( synth
  , check
  , checkK
  , checkSubkindOf
  , checkProper
  , checkProperK
  , checkPrekind
  , checkSession
  , checkChannel
  , isRestricted
  , isStrictlySession
  , isStrictlyChannel
  , KindCtx
  , emptyKindCtx
  , kindModule
  , runKindModule
  , runSynth
  , runCheck
  )
where

import Syntax.Base hiding (void)
import Syntax.Expression qualified as E
import Syntax.Kind
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as TK
import Syntax.Type.Unkinded qualified as T
import UI.Error
import Utils
import Validation.Base
import Validation.Expose qualified as Expose
import Validation.HOTRecursion (checkNoHOTRec)
import Validation.Normalisation
import Validation.Substitution ( subs, subsMultType )

import Control.Monad.Identity ( Identity(..) )
import Control.Monad.Extra ( unlessM, (&&^) )
import Control.Monad.State ( MonadState, foldM, unless, void, forM, forM_, when, runState, StateT (runStateT), evalState, gets, modify )
import Control.Monad.Trans.Except ( throwE, runExceptT, ExceptT (ExceptT) )
import Data.Bifunctor ( first, second, bimap )
import Data.Bitraversable (bitraverse) -- bimapM 
import Data.Foldable.Extra ( allM )
import Data.Functor ( (<&>) )
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.List qualified as List

-- | The kinding context. Keeps track of type variables and their kinds.
type KindCtx = Map.Map Variable Kind

-- | Function signature context.
type TypeCtx = Map.Map Variable TK.KindedType

emptyKindCtx :: KindCtx
emptyKindCtx = Map.empty

-- | Synthesize the (minimal?) kind of a type.
synth :: M.ScopedModule -> KindCtx -> T.ScopedType -> Validation TK.KindedType
synth modl ctx = \case
  -- Functional types
  T.Int s    -> pure $ TK.Int s
  T.Float s  -> pure $ TK.Float s
  T.Char s   -> pure $ TK.Char s
  T.Arrow s m -> pure $ TK.Arrow s m
  -- Session types
  T.Message s m p -> pure $ TK.Message s m p
  T.UnChoice s p ls -> pure $ TK.UnChoice s p ls
  T.AppLinChoice s p lts -> do
    lts' <- forM lts (\(i, t) -> do
      (_, _, u) <- checkSession modl ctx t
      return (i, u))
    pure $ TK.AppLinChoice s p lts'
  T.End s p -> pure $ TK.End s p
  T.Skip s -> pure $ TK.Skip s
  T.Void s k -> pure $ TK.Void s k
  T.AppSemi s t u -> do
    (m1, pk1, t') <- checkSession modl ctx t
    (m2, pk2, u') <- checkSession modl ctx u
    return $ TK.AppSemi s t' u'
  T.AppDual s t -> do
    t' <- check modl ctx t (ls s)
    return (TK.AppDual s t')
  -- Polymorphism
  T.AppQuant s p pk m aks t -> do
    (_, _, kt) <- checkPrekind modl (Map.fromList aks `Map.union` ctx) t pk
    return $ TK.AppQuant s p pk m aks kt
  T.ForallM s m φs t -> TK.ForallM s m φs <$> synth modl ctx t
  -- Equations (including built-ins)
  T.TName s i -> flip (TK.TName s) i <$> lookupKind modl i
  T.Tuple s ts -> do
    (_, ts') <- foldCheckProperJoin modl ctx (Un s) ts
    return $ TK.Tuple s ts'
  T.List s t -> do
    (_, _, t') <- checkProper modl ctx t
    return $ TK.List s t'
  T.DName s i -> flip (TK.DName s) i <$> lookupKind modl i
  -- Higher-order
  T.Var s a -> case ctx Map.!? a of
    Just k -> pure $ TK.fromVariable ObjLv a k
    Nothing -> do
      throwE (TypeVarOutOfScope s a)
  T.App s t ts -> do
    t' <- synth modl ctx t
    let k = TK.kindOf t'
    let (ks, kn) = Expose.kindArrow k
    (_, ts') <- checkArgs t' (length ts) (length ks) ts ks kn
    return $ TK.App s t' ts'
    where
      checkArgs :: TK.KindedType -> Int -> Int -- error info
                -> [T.ScopedType] -> [Kind] -> Kind
                -> Validation (Kind, [TK.KindedType])
      checkArgs _ _ _ [] ks kn = pure
        (foldr (\k k' -> Arrow (spanFromTo k k') k k') kn ks, [])
      checkArgs t' nargs npars ts [] kn = do
        throwE (GivenTooManyArgsK (spanFromTo (head ts) (last ts)) t' kn npars nargs)
      checkArgs t' nargs npars (ti : ts) (ki : ks) kn = do
        ti' <- check modl ctx ti ki
        second (ti' :) <$> checkArgs t' nargs npars ts ks kn
  T.Abs s aks t -> do
    TK.Abs s aks <$> synth modl (Map.fromList aks `Map.union` ctx) t

-- | Check a type against a given kind.
check :: M.ScopedModule -> KindCtx -> T.ScopedType -> Kind -> Validation TK.KindedType
check ctx mod t k = do
  kt <- synth ctx mod t
  checkSubkindOf kt (TK.kindOf kt) k
  return kt

checkK :: TK.KindedType -> Kind -> Validation ()
checkK t = checkSubkindOf t (TK.kindOf t)

-- | Calculate the join of the multiplicities of a list of types, starting
-- from a given multiplicity. Throws an error if a non-proper type is
-- encountered.
foldCheckProperJoin :: M.ScopedModule -> KindCtx -> Multiplicity -> [T.ScopedType] -> Validation (Multiplicity, [TK.KindedType])
foldCheckProperJoin modl ctx m = foldM checkProperJoin (m, [])
  where checkProperJoin (m', ts) t = do
          (m'', _, t') <- checkProper modl ctx t
          pure (join m' m'', ts ++ [t'])

-- | Check if a type is a proper type. If so, return its minimal multiplicity 
-- and prekind. Otherwise, throw an error.
checkProper :: M.ScopedModule -> KindCtx -> T.ScopedType -> Validation (Multiplicity, Prekind, TK.KindedType)
checkProper modl ctx t = synth modl ctx t >>= \t' -> case TK.kindOf t' of
    Proper _ mult pk ->  pure (mult, pk, t')
    k -> throwE (ProperKindMismatch (getSpan t) t' k)

-- | Check if a type is a proper type. If so, return its minimal multiplicity 
-- and prekind. Otherwise, throw an error.
checkProperK :: TK.KindedType -> Validation (Multiplicity, Prekind, TK.KindedType)
checkProperK t = case TK.kindOf t of
    Proper _ m pk -> pure (m, pk, t)
    k -> throwE (ProperKindMismatch (getSpan t) t k)

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkSession :: M.ScopedModule -> KindCtx -> T.ScopedType -> Validation (Multiplicity, Prekind, TK.KindedType)
checkSession mod ctx t = checkPrekind mod ctx t Session

checkSessionK :: TK.KindedType -> Validation (Multiplicity, Prekind)
checkSessionK t = checkPrekindK t Session

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkChannel :: TK.KindedType -> Validation (Multiplicity, Prekind) -- TODO: parsed version?
checkChannel t = checkPrekindK t Channel

-- | Check if a type is a proper type of the given prekind. If so, return its 
-- minimal multiplicity and prekind. Otherwise, throw an error.
checkPrekind :: M.ScopedModule -> KindCtx -> T.ScopedType -> Prekind -> Validation (Multiplicity, Prekind, TK.KindedType)
checkPrekind modl ctx t pk = do
  (m, pk', kt) <- checkProper modl ctx t
  unless (pk' <: pk) $
    throwE (PrekindMismatch (getSpan t) pk kt (Proper (getSpan t) m pk'))
  return (m, pk', kt)

checkPrekindK :: TK.KindedType -> Prekind -> Validation (Multiplicity, Prekind)
checkPrekindK t pk = do
  (m, pk', _) <- checkProperK t
  unless (pk' <: pk) $
    throwE (PrekindMismatch (getSpan t) pk t (Proper (getSpan t) m pk'))
  return (m, pk')

-- | Check if the kind of a type is a subkind of another. If not, throw an 
-- error located at the type.
checkSubkindOf :: TK.KindedType -> Kind -> Kind -> Validation ()
checkSubkindOf t k' k = unless (k' <: k) $
    throwE (KindMismatch (getSpan t) k t)

-- | Check if the kind of a type is a subkind of another in a contravariant 
-- position. If not, throw an error located at the type.
checkSubkindOf' :: TK.KindedType -> Kind -> Kind -> Validation ()
checkSubkindOf' t k' k = unless (k' <: k) $
     throwE (KindMismatch (getSpan t) k' t)

isRestricted, isStrictlyChannel, isStrictlySession :: TK.KindedType -> Bool

isRestricted t = case TK.kindOf t of
  (Proper _ Un{} _) -> False
  _ -> True

isStrictlyChannel t = case TK.kindOf t of
  (Proper _ _ Channel) -> True
  _ -> False


isStrictlySession t = case TK.kindOf t of
  (Proper _ _ Session) -> True
  _ -> False

-- | Check a module for type formation.
kindModule :: M.ScopedModule -> Validation M.KindedModule
kindModule mod = do
  tds <- Map.traverseWithKey kindTypeDecl (M.typeDecls mod)
  cds <- foldM kindDataConsDecls Map.empty $ Map.toList $ M.dataDecls mod -- TODO: foldrWithKeyM
  let mod' :: M.KindedModule
      mod' = mod { M.name = M.name mod, M.imports = M.imports mod, M.kindSigs    = M.kindSigs mod
                 , M.typeDecls   = tds
                 , M.dataDecls   = M.dataDecls mod
                 , M.consDecls   = cds
                 , M.definitions = []
                 }
  checkNoHOTRec mod'
  (_, lds) <- kindLetDecls mod mod' Map.empty (M.definitions mod)
  return mod'{M.definitions = lds}
  where
    kindTypeDecl :: Identifier -> (Bool, T.ScopedType) -> Validation (Bool, TK.KindedType)
    kindTypeDecl i (hasParams, t) = do
      k <- lookupKind mod i
      (hasParams,) <$> case t of
        T.Abs s aks u | hasParams -> do
          (aks', k') <- kindParams aks k
          u' <- check mod (Map.fromList aks') u k' -- TODO: Map.empty'
          return $ TK.Abs s aks' u'
          where
            kindParams ((a, Var _ _) : aks') (Arrow _ k1 k2) =
              first ((a, k1) :) <$> kindParams aks' k2
            kindParams ((a, k) : aks') (Arrow _ k1 k2) = do
              checkK (TK.fromVariable ObjLv a k) k1
              first ((a, k) :) <$> kindParams aks' k2
            kindParams []  k' = pure ([], k')
            kindParams aks _ = throwE (ExpectsTooManyArgsK (getSpan i) i k)

        t' -> check mod Map.empty t' k-- TODO: Map.empty? 
      -- return (hasParams, t')

    kindDataConsDecls :: M.ConsDecls Kinded
                      -> (Identifier, ([(Variable, Kind)], [Identifier]))
                      -> Validation (M.ConsDecls Kinded)
    kindDataConsDecls cds' (i, (aks, cis)) = do
      k  <- lookupKind mod i
      cd <- checkDataDecl k id Map.empty aks k
      return (Map.union cd cds')
      where
        checkDataDecl :: Kind
                      -> (Kind -> Kind)
                      -> KindCtx
                      -> [(Variable, Kind)]
                      -> Kind
                      -> Validation (M.ConsDecls Kinded)
        checkDataDecl k f ctx [] _ = checkConsDecls k f ctx
        checkDataDecl k f ctx ((a, Var _ _) : aks') (Arrow s k1 k2) =
          checkDataDecl k (f . Arrow s k1) (Map.insert a k1 ctx) aks' k2
        checkDataDecl k f ctx ((a, k') : aks') (Arrow s k1 k2) = do
          checkK (TK.fromVariable ObjLv a k') k1
          checkDataDecl k (f . Arrow s k') (Map.insert a k' ctx) aks' k2
        checkDataDecl k f ctx aks Proper{} =
          throwE (ExpectsTooManyArgsK (getSpan i) i k)

        checkConsDecls :: Kind
                       -> (Kind -> Kind)
                       -> KindCtx
                       -> Validation (M.ConsDecls Kinded)
        checkConsDecls k f ctx = do
          (m, cds') <- synthDataMult ctx cis
          let k' = f (Proper (getSpan i) m Top)
          unless (k' <: k)
            (throwE (KindMismatch (getSpan i) k (TK.TName (getSpan i) k' i)))
          return cds'

        synthDataMult :: KindCtx
                      -> [Identifier]
                      -> Validation (Multiplicity, M.ConsDecls Kinded)
        synthDataMult ctx = foldM (\(m, acc) ci ->
          case M.consDecls mod Map.!? ci of
            Just (snd -> ts) -> do
              (m, ts') <- foldCheckProperJoin mod ctx m ts
              return (m, Map.insert ci (i, ts') acc)
            Nothing -> internalError ("constructor " ++ show ci ++ " not found"))
          (Un (getSpan i), Map.empty)

    kindLetDecls :: M.ScopedModule -> M.KindedModule
                 -> KindCtx
                 -> [E.LetDecl Scoped]
                 -> Validation (KindCtx, [E.LetDecl Kinded])
    kindLetDecls smodl kmodl kctx lds = do
      (kctx, _, lds) <- foldM kindLetDecl (kctx, Map.empty, []) lds
      return (kctx, lds)
      where
        kindLetDecl :: (KindCtx, TypeCtx, [E.LetDecl Kinded])
                    -> E.LetDecl Scoped
                    -> Validation (KindCtx, TypeCtx, [E.LetDecl Kinded])
        kindLetDecl (kctx, tctxds, lds) = \case
          E.ValDef p rhs -> do
            rhs' <- kindRHS smodl kmodl kctx rhs
            (kctx', p') <- kindPat kctx p
            return (kctx', tctxds, lds ++ [E.ValDef p' rhs'])
          E.FnDef x psrhss -> do
            case tctxds Map.!? x of
              Just t -> do
                psrhss' <- forM psrhss \(psi, rhsi) ->
                  unwrap <$> kindFun x kctx tctxds (wrap psi) rhsi t
                return (kctx, tctxds, lds ++ [E.FnDef x psrhss'])
                where
                  wrap   = map (mapLevel (, Nothing) (, Nothing) id)
                  unwrap = first (map (mapLevel fst fst id))
              Nothing -> throwE (LacksTypeSig (getSpan x) x)
          E.TypeSig xs t -> do
            t' <- synth mod kctx t
            let tctxds' = Map.fromList (map (, t') xs) `Map.union` tctxds
            return (kctx, tctxds', lds ++ [E.TypeSig xs t'])
          E.Mutual lds' -> do
            let (sigs, fndefs) = List.partition (\case E.TypeSig{} -> True; _ -> False) lds'
            (kctx',lds'') <- kindLetDecls smodl kmodl kctx (sigs ++ fndefs)
            return (kctx', tctxds, lds ++ [E.Mutual lds''])

        kindFun :: Located e => e
                -> KindCtx
                -> TypeCtx
                -> [Level (E.Pat, Maybe T.ScopedType) (Variable, Maybe Kind) Variable]
                -> E.ScopedRHS
                -> TK.KindedType
                -> Validation ([Level (E.Pat, TK.KindedType) (Variable, Kind) Variable], E.RHS Kinded)
        kindFun e = kindFun' 0
          where
            kindFun' :: Int
                    -> KindCtx
                    -> TypeCtx
                    -> [Level (E.Pat, Maybe T.ScopedType) (Variable, Maybe Kind) Variable]
                    -> E.ScopedRHS
                    -> TK.KindedType
                    -> Validation ([Level (E.Pat, TK.KindedType) (Variable, Kind) Variable], E.RHS Kinded)
            kindFun' i kctx tctxds ps rhs t = case (ps, normalise kmodl t) of
              ([], _) -> ([],) <$> kindRHS smodl kmodl kctx rhs
              (TypeLevel (ai, mki) : ps', TK.AppForall s' m ((a, k) : aks) u) -> do
                k' <- case mki of
                  Just ki -> checkK (TK.fromVariable ObjLv ai ki) k >> return ki
                  Nothing -> return k
                first (TypeLevel (ai, k') :) <$> kindFun' (i + 1) (Map.insert ai k' kctx) tctxds ps'
                  rhs (TK.AppForall s' m aks $ subs a (TK.fromVariable ObjLv ai k') u)
              (ExpLevel  (p, mtp) : ps', TK.AppArrow _ _ u v) -> do
                tp' <- case mtp of
                  Just tp -> do
                    (_, _, tp') <- checkProper smodl kctx tp
                    return tp'
                  Nothing -> pure u
                (kctxi', p') <- kindPat kctx p
                first (ExpLevel (p', tp') :) <$> kindFun' (i + 1) kctxi' tctxds ps' rhs v
              (MultLevel φ : ps', TK.ForallM s' m (φ' : φs) u) ->
                first (MultLevel φ :) <$> kindFun' (i + 1) kctx tctxds ps' rhs 
                  ((if null φs then id else TK.ForallM s' m φs) $ 
                    subsMultType ObjLv φ' (VarM (getSpan φ) ObjLv φ) u)
              (pi : ps', TK.AppArrow _ _ u _) ->
                throwE (UnexpectedParam (paramSpan pi) i (ExpLevel  u ) (voidLevel pi))
              (pi : ps', TK.AppForall _ _ ((_, k) : _) u) ->
                throwE (UnexpectedParam (paramSpan pi) i (TypeLevel k ) (voidLevel pi))
              (pi : ps', TK.ForallM{}) -> 
                throwE (UnexpectedParam (paramSpan pi) i (MultLevel ()) (voidLevel pi))
              (as, t') -> do
                throwE (ExpectsTooManyArgs (getSpan e) t (i + length as) i)
              where
                -- TODO: duplicates in Typing
                paramSpan = \case
                  ExpLevel (p, mt) -> maybe (getSpan p) (spanFromTo p) mt
                  TypeLevel (a, mk) -> maybe (getSpan a) (spanFromTo a) mk
                  MultLevel φ -> getSpan φ

        kindRHS :: M.ScopedModule -> M.KindedModule
                -> KindCtx
                -> E.RHS Scoped
                -> Validation (E.RHS Kinded)
        kindRHS smodl kmodl kctx = \case
          E.GuardedRHS es mlds -> do
            (kctx', mlds') <- case mlds of
              Just lds -> second Just <$> kindLetDecls smodl kmodl kctx lds
              Nothing -> pure (kctx, Nothing)
            es' <- mapM (bitraverse (kindExp kctx') (kindExp kctx')) es
            return $ E.GuardedRHS es' mlds'
          E.UnguardedRHS e mlds -> do
            (kctx', mlds') <- case mlds of
              Just lds -> second Just <$> kindLetDecls smodl kmodl kctx lds
              Nothing -> pure (kctx, Nothing)
            e' <- kindExp kctx' e
            return $ E.UnguardedRHS e' mlds'

        kindPat :: KindCtx -> E.Pat -> Validation (KindCtx, E.Pat)
        kindPat kctx = \case
          E.IntPat   s i -> pure (kctx, E.IntPat   s i)
          E.FloatPat s f -> pure (kctx, E.FloatPat s f)
          E.CharPat  s c -> pure (kctx, E.CharPat  s c)
          E.WildPat  s x -> pure (kctx, E.WildPat  s x)
          E.VarPat   s x -> pure (kctx, E.VarPat   s x)
          E.PackPat s aks p -> second (E.PackPat s aks) <$> kindPat (Map.fromList aks `Map.union` kctx) p
          E.NilPat   s   -> pure (kctx, E.NilPat   s  )
          E.ConsPat s p1 p2 -> do
            (kctx' , p1') <- kindPat kctx p1
            (kctx'', p2') <- kindPat kctx p2
            return (kctx'', E.ConsPat s p1' p2')
          E.TuplePat s ps -> do
            (kctx', ps') <- foldM (\(kctxi, psi) pi -> do
                (kctxi', pi') <- kindPat kctxi pi
                return (kctxi', psi ++ [pi']))
              (kctx, []) ps
            return (kctx', E.TuplePat s ps')
          -- (C p1 ... pn)
          E.DConsPat s i ps -> do
            (kctx', ps') <- foldM (\(kctxi, psi) pi -> do
                (kctxi', pi') <- kindPat kctxi pi
                return (kctxi', psi ++ [pi']))
              (kctx, []) ps
            return (kctx', E.DConsPat s i ps')
          E.WaitPat s       -> pure (kctx, E.WaitPat s)
          E.InPat s p1 p2 -> do
            (kctx', p1') <- kindPat kctx p1
            (kctx'', p2') <- kindPat kctx p2
            return (kctx'', E.InPat s p1' p2')
          E.ChoicePat s i p -> second (E.ChoicePat s i) <$> kindPat kctx p
          E.TypeInPat s (a, k) p -> second (E.TypeInPat s (a, k)) <$> kindPat (Map.insert a k kctx) p
          E.AsPat s x p     -> second (E.AsPat     s x) <$> kindPat kctx p

        kindExp :: KindCtx -> E.ScopedExp -> Validation E.KindedExp
        kindExp kctx = \case
          E.Int   s i -> pure $ E.Int   s i
          E.Float s d -> pure $ E.Float s d
          E.Char  s c -> pure $ E.Char  s c
          E.DCons s i -> pure $ E.DCons s i
          E.Var   s a -> pure $ E.Var   s a
          E.App s e args -> do
            e' <- kindExp kctx e
            args' <- forM args \case
              ExpLevel  e -> ExpLevel  <$> kindExp kctx e
              TypeLevel t -> TypeLevel <$> synth smodl kctx t
              MultLevel m -> pure $ MultLevel m
            return $ E.App s e' args'
          E.Abs s pars m e -> do
            (kctx', pars') <- foldM (\(kctxi, parsi) -> \case
                ExpLevel  (p, t) -> do
                  (kctxi', p') <- kindPat kctxi p
                  t' <- synth smodl kctxi' t
                  return (kctxi', parsi ++ [ExpLevel (p', t')])
                TypeLevel (a, k) -> do
                  let kctxi' = Map.insert a k kctxi
                  return (kctxi', parsi ++ [TypeLevel (a, k)])
                MultLevel φ -> do
                  return (kctxi, parsi ++ [MultLevel φ]))
              (kctx, []) pars
            e' <- kindExp kctx' e
            pure $ E.Abs s pars' m e'
          E.Pack s' ts e -> E.Pack s' <$> mapM (synth smodl kctx) ts <*> kindExp kctx e
          E.Asc s e t -> E.Asc s <$> kindExp kctx e <*> synth smodl kctx t
          E.Let s lds e -> do
            (kctx', lds') <- kindLetDecls smodl kmodl kctx lds
            e' <- kindExp kctx' e
            return (E.Let s lds' e')
          E.Semi s e1 e2 -> E.Semi s <$> kindExp kctx e1 <*> kindExp kctx e2
          E.Case s e prhss -> do
            e' <- kindExp kctx e
            prhss' <- forM prhss \(pi, rhsi) -> do
              (kctxi, pi') <- kindPat kctx pi
              rhsi' <- kindRHS smodl kmodl kctxi rhsi
              return (pi', rhsi')
            return $ E.Case s e' prhss'
          E.If s e1 e2 e3 ->
            E.If s <$> kindExp kctx e1 <*> kindExp kctx e2 <*> kindExp kctx e3
          E.Channel s t -> E.Channel s <$> synth smodl kctx t
          E.Select s i -> pure $ E.Select s i
          E.SendType s t -> E.SendType s <$> synth smodl kctx t
          E.ReceiveType s -> pure $ E.ReceiveType s

-- | Run kinding on a module, building the initial validation state from it.
-- This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * the given module, otherwise.
runKindModule :: M.ScopedModule -> Either [Error] M.KindedModule
runKindModule modl = runValidation emptyValidationState (kindModule modl)

-- | Run synthesis on type, building the initial validation state from a given
-- module. This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * a kind synthesized from the type, otherwise.
runSynth :: M.ScopedModule -> T.ScopedType -> Either [Error] TK.KindedType -- TODO: this function will be deprecated
runSynth modl t = runValidation emptyValidationState (synth modl Map.empty t)

-- | Run checking on a type against a kind, building the initial validation 
-- state from a given module. This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * unit, otherwise.
runCheck :: M.ScopedModule -> T.ScopedType -> Kind -> Either [Error] TK.KindedType
runCheck mod t k = runValidation emptyValidationState (check mod Map.empty t k)
