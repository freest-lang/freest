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
  , checkSessionK
  , checkChannel
  , KindCtx
  , emptyKindCtx
  , kindModule
  , runKindModule
  , runSynth
  , runCheck
  , isStrictlyLin
  , isStrictlySession
  , isStrictlyChannel
  )
where

import UI.Error
import Syntax.Base
import Syntax.Kind
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Syntax.Expression qualified as E
import Utils
import Validation.Base
import Validation.Expose qualified as Expose
import Validation.Normalisation
import Validation.Substitution ( subs )

import Control.Monad.Identity ( Identity(..) )
import Control.Monad.Extra ( unlessM, (&&^) )
import Control.Monad.State ( MonadState, foldM, unless, void, forM, forM_, when, runState, StateT (runStateT), evalState, gets, modify )
import Control.Monad.Trans.Except ( throwE, runExceptT, ExceptT (ExceptT) )
import Data.Bifunctor ( first, second, bimap )
import Data.Bitraversable (bitraverse) -- bimapM 
import Data.Foldable.Extra ( allM )
import Data.Functor ( (<&>) )
import Data.List qualified as List
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Debug.Trace (traceM)
import Data.Coerce

-- | The kinding context. Keeps track of type variables and their kinds.
type KindCtx = Map.Map Variable Kind

-- | Function signature context.
type TypeCtx = Map.Map Variable T.KindedType

emptyKindCtx :: KindCtx
emptyKindCtx = Map.empty

trimap :: (a -> b) -> (c -> d) -> (e -> f) -> (a, c, e) -> (b, d, f)
trimap f g h (x, y, z) = (f x, g y, h z)

-- | Synthesize the (minimal?) kind of a type.
synth :: KindCtx -> M.ScopedModule -> T.ScopedType -> FreeST T.KindedType
synth ctx mod = \case
  -- Functional types
  T.Int s _    -> pure $ T.Int s (ut s)
  T.Float s _  -> pure $ T.Float s (ut s)
  T.Char s _   -> pure $ T.Char s (ut s)
  T.Arrow s _ m -> pure $ T.Arrow s k m
    where k = Arrow s (lt s) (Arrow s (lt s) (Proper s m Top))
  -- Session types
  T.Message s _ m p -> pure $ T.Message s k m p
    where k = Arrow s (lt s) (if m == Lin then ls s else uc s)
  T.SharedChoice s _ p ls -> pure $ T.SharedChoice s (uc s) p ls
  T.AppLinChoice s _ _ p lts -> do
    (m, pk, lts) <- foldM (\(m,pk,lts) (l,t) -> trimap (join m) (meet pk) ((: lts) . (l,)) -- TODO: order?
                            <$> checkSession ctx mod t) (Un, Session, []) lts
    pure $ T.AppLinChoice s (Proper s Lin pk) (Proper s m pk) p lts
  T.End s _ p -> pure $ T.End s (lc s) p
  T.Skip s _ -> pure $ T.Skip s (us s)
  T.Void s _ k -> pure $ T.Void s k k
  T.AppSemi s _ t u -> do
    (m1, pk1, t) <- checkSession ctx mod t
    (m2, pk2, u) <- checkSession ctx mod u
    let k = Proper s (if pk1 == Channel then m1 else join m1 m2) (meet pk1 pk2)
    return $ T.AppSemi s k t u
  T.AppDual s _ t -> do
    t' <- check ctx mod t (ls s)
    return (T.AppDual s (T.getExt t') t')
  -- Polymorphism
  T.AppQuant s _ p aks t -> do
    checkProper (Map.fromList aks `Map.union` ctx) mod t
    >>= \case (m, Channel, t) -> pure $ T.AppQuant s (Proper s Lin Channel) p aks t
              (m, Session, t) -> pure $ T.AppQuant s (Proper s Lin Session) p aks t
              (m, Top    , t) -> pure $ T.AppQuant s (Proper s m   Top    ) p aks t
  -- Equations (including built-ins)
  T.TName s _ i -> flip (T.TName s) i <$> lookupKind mod i
  T.Tuple s _ ts -> do
    (m, ts) <- foldCheckProperJoin ctx mod Un ts
    return $ T.Tuple s (Proper s m Top) ts
  T.List s _ t -> do
    (m, _, t) <- checkProper ctx mod t
    pure $ T.List s (Proper s m Top) t
  T.DName s _ i -> flip (T.DName s) i <$> lookupKind mod i
  -- Higher-order
  T.Var s _ a -> case ctx Map.!? a of
    Just k -> pure $ T.Var s k a
    Nothing -> throwE (TypeVarOutOfScope s a)
  T.App s _ t ts -> do
    t' <- synth ctx mod t
    let (ks, kn) = Expose.kindArrow (T.getExt t')
    (k, ts') <- checkArgs t' (length ts) (length ks) ts ks kn
    pure $ T.App s k t' ts'
    where
      checkArgs :: T.KindedType -> Int -> Int -- error info
                -> [T.ScopedType] -> [Kind] -> Kind
                -> FreeST (Kind, [T.KindedType])
      checkArgs _ _ _ [] ks kn = pure
        (foldr (\k k' -> Arrow (spanFromTo k k') k k') kn ks, [])
      checkArgs t' nargs npars ts [] kn = do
        throwE (GivenTooManyArgsK (spanFromTo (head ts) (last ts)) t' kn npars nargs)
      checkArgs t' nargs npars (ti : ts) (ki : ks) kn = do
        ti' <- check ctx mod ti ki
        second (ti' :) <$> checkArgs t' nargs npars ts ks kn
  T.Abs s _ aks t -> do
    t' <- synth (Map.fromList aks `Map.union` ctx) mod t
    let k = foldr (\(_, ki) k -> Arrow (spanFromTo ki k) ki k) k aks
    return $ T.Abs s k aks t'

-- | Check a type against a given kind.
check :: KindCtx -> M.ScopedModule -> T.ScopedType -> Kind -> FreeST T.KindedType
check ctx mod t k = do
  kt <- synth ctx mod t
  checkSubkindOf kt (T.getExt kt) k
  return kt

checkK :: T.KindedType -> Kind -> FreeST ()
checkK t = checkSubkindOf t (T.getExt t)

-- | Calculate the join of the multiplicities of a list of types, starting
-- from a given multiplicity. Throws an error if a non-proper type is
-- encountered.
foldCheckProperJoin :: KindCtx -> M.ScopedModule -> Multiplicity -> [T.ScopedType] -> FreeST (Multiplicity, [T.KindedType])
foldCheckProperJoin ctx m mult = foldM checkProperJoin (mult,[])
  where checkProperJoin (m', ts) t =
          checkProper ctx m t  >>= \(m'',_ ,t) -> pure (join m' m'', ts ++ [t])

-- | Check if a type is a proper type. If so, return its minimal multiplicity 
-- and prekind. Otherwise, throw an error.
checkProper :: KindCtx -> M.ScopedModule -> T.ScopedType -> FreeST (Multiplicity, Prekind, T.KindedType)
checkProper ctx m t = synth ctx m t >>= \kT -> case T.getExt kT of
    Proper _ mult pk ->  pure (mult,pk,kT)
    k -> throwE (ProperKindMismatch (getSpan t) kT k)

-- | Check if a type is a proper type. If so, return its minimal multiplicity 
-- and prekind. Otherwise, throw an error.
checkProperK :: T.KindedType -> FreeST (Multiplicity, Prekind, T.KindedType)
checkProperK t = case T.getExt t of
    Proper _ m pk -> pure (m,pk,t)
    k -> throwE (ProperKindMismatch (getSpan t) t k)

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkSession :: KindCtx -> M.ScopedModule -> T.ScopedType -> FreeST (Multiplicity, Prekind, T.KindedType)
checkSession ctx mod t = checkPrekind ctx mod t Session

checkSessionK :: KindCtx -> T.KindedType -> FreeST (Multiplicity, Prekind)
checkSessionK ctx t = checkPrekindK ctx t Session

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkChannel :: KindCtx -> T.KindedType -> FreeST (Multiplicity, Prekind) -- TODO: parsed version?
checkChannel ctx t = checkPrekindK ctx t Channel

-- | Check if a type is a proper type of the given prekind. If so, return its 
-- minimal multiplicity and prekind. Otherwise, throw an error.
checkPrekind :: KindCtx -> M.ScopedModule -> T.ScopedType -> Prekind -> FreeST (Multiplicity, Prekind, T.KindedType)
checkPrekind ctx mod t pk = do
  (m, pk', kt) <- checkProper ctx mod t
  unless (pk' <: pk) $
    throwE (PrekindMismatch (getSpan t) pk kt (Proper (getSpan t) m pk'))
  return (m, pk', kt)

checkPrekindK :: KindCtx -> T.KindedType -> Prekind -> FreeST (Multiplicity, Prekind)
checkPrekindK _ t pk = do
  (m, pk', _) <- checkProperK t
  unless (pk' <: pk) $
    throwE (PrekindMismatch (getSpan t) pk t (Proper (getSpan t) m pk'))
  return (m, pk')

-- | Check if the kind of a type is a subkind of another. If not, throw an 
-- error located at the type.
checkSubkindOf :: T.KindedType -> Kind -> Kind -> FreeST ()
checkSubkindOf t k' k = unless (k' <: k) $
    throwE (KindMismatch (getSpan t) k t k')

-- | Check if the kind of a type is a subkind of another in a contravariant 
-- position. If not, throw an error located at the type.
checkSubkindOf' :: T.KindedType -> Kind -> Kind -> FreeST ()
checkSubkindOf' t k' k = unless (k' <: k) $
     throwE (KindMismatch (getSpan t) k' t k)


checkSubkindOfP' :: M.ScopedModule -> T.ScopedType -> Kind -> Kind -> FreeST ()
checkSubkindOfP' mod t k' k = do
  t' <- synth Map.empty mod t -- TODO: map empty
  unless (k' <: k) $
     throwE (KindMismatch (getSpan t) k' t' k)

-- | Check a module for type formation.
kindModule :: M.ScopedModule -> FreeST M.KindedModule
kindModule mod = do
  tds <- Map.traverseWithKey kindTypeDecl (M.typeDecls mod)
  cds <- foldM kindDataConsDecls Map.empty $ Map.toList $ M.dataDecls mod -- TODO: foldrWithKeyM
  (_, lds) <- kindLetDecls tds Map.empty (M.definitions mod)
  return mod{ M.kindSigs   = M.kindSigs mod
            , M.typeDecls   = tds
            , M.dataDecls   = M.dataDecls mod
            , M.consDecls   = cds
            , M.definitions = lds
            }
  where
    kindTypeDecl :: Identifier -> T.ScopedType -> FreeST T.KindedType
    kindTypeDecl i t = do
      k <- lookupKind mod i
      t' <- case t of
        T.Abs s _ aks u -> do
          aks' <- kindParams aks k
          u' <- synth (Map.fromList aks') mod u -- TODO: Map.empty'
          return $ T.Abs s k aks' u'
          where
            kindParams ((a, Var _ _) : aks') (Arrow _ k1 k2) =
              ((a, k1) :) <$> kindParams aks' k2
            kindParams ((a, k) : aks') (Arrow _ k1 k2) = do
              checkSubkindOfP' mod (T.Var (getSpan a) Syntax.Base.void a) k1 k
              ((a, k) :) <$> kindParams aks' k2
            kindParams []  _ = pure []
            kindParams aks _ = throwE (ExpectsTooManyArgsK (getSpan i) i k)

        t' -> synth Map.empty mod t' -- TODO: Map.empty? 
      checkK t' k
      return t'

    kindDataConsDecls :: M.ConsDecls Kinded
                      -> (Identifier, ([(Variable, Kind)], [Identifier]))
                      -> FreeST (M.ConsDecls Kinded)
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
                      -> FreeST (M.ConsDecls Kinded)
        checkDataDecl k f ctx [] _ = checkConsDecls k f ctx
        checkDataDecl k f ctx ((a, Var _ _) : aks') (Arrow s k1 k2) =
          checkDataDecl k (f . Arrow s k1) (Map.insert a k1 ctx) aks' k2
        checkDataDecl k f ctx ((a, k') : aks') (Arrow s k1 k2) = do
          checkSubkindOfP' mod (T.Var (getSpan a) Syntax.Base.void a) k1 k'
          checkDataDecl k (f . Arrow s k') (Map.insert a k' ctx) aks' k2
        checkDataDecl k f ctx aks Proper{} =
          throwE (ExpectsTooManyArgsK (getSpan i) i k)

        checkConsDecls :: Kind
                       -> (Kind -> Kind)
                       -> KindCtx
                       -> FreeST (M.ConsDecls Kinded)
        checkConsDecls k f ctx = do
          (m, cds') <- synthDataMult ctx cis
          let k' = f (Proper (getSpan i) m Top)
          unless (k' <: k)
            (throwE (KindMismatch (getSpan i) k (T.TName (getSpan i) k' i) k'))
          return cds'

        synthDataMult :: KindCtx
                      -> [Identifier]
                      -> FreeST (Multiplicity, M.ConsDecls Kinded)
        synthDataMult ctx = foldM (\(m, acc) ci ->
          case M.consDecls mod Map.!? ci of
            Just (snd -> ts) -> do
              (m, ts') <- foldCheckProperJoin ctx mod m ts
              return (m, Map.insert ci (i, ts') acc)
            Nothing -> internalError ("constructor " ++ show ci ++ " not found"))
          (Un, Map.empty)

    kindLetDecls :: M.TypeDecls Kinded 
                 -> KindCtx
                 -> [E.LetDecl Scoped]
                 -> FreeST (KindCtx, [E.LetDecl Kinded])
    kindLetDecls tds kctx lds = do
      (kctx, _, lds) <- foldM kindLetDecl (kctx, Map.empty, []) lds
      return (kctx, lds)
      where
        kindLetDecl :: (KindCtx, TypeCtx, [E.LetDecl Kinded]) 
                    -> E.LetDecl Scoped 
                    -> FreeST (KindCtx, TypeCtx, [E.LetDecl Kinded])
        kindLetDecl (kctx, tctxds, lds) = \case
          E.ValDef p rhs -> do
            rhs' <- kindRHS tds kctx rhs
            (kctx', p') <- kindPat kctx p
            return (kctx', tctxds, lds ++ [E.ValDef p' rhs'])
          E.FnDef x psrhss -> do
            case tctxds Map.!? x of
              Just t -> do 
                psrhss' <- forM psrhss \(psi, rhsi) ->
                  unwrap <$> kindFun x kctx tctxds (wrap psi) rhsi t
                return (kctx, tctxds, lds ++ [E.FnDef x psrhss'])
                where
                  wrap   = map (bimap (, Nothing) (, Nothing))
                  unwrap = first (map (bimap fst fst))
              Nothing -> throwE (LacksTypeSig (getSpan x) x)
          E.TypeSig xs t -> do 
            t' <- synth kctx mod t
            let tctxds' = Map.fromList (map (, t') xs) `Map.union` tctxds
            return (kctx, tctxds', lds ++ [E.TypeSig xs t'])
          E.Mutual lds' -> do
            let (sigs, fndefs) = List.partition (\case E.TypeSig{} -> True; _ -> False) lds'
            (kctx',lds'') <- kindLetDecls tds kctx (sigs ++ fndefs)
            return (kctx', tctxds, lds ++ [E.Mutual lds''])

        kindFun :: Located a => a
                -> KindCtx 
                -> TypeCtx
                -> [Level (E.ScopedPat, Maybe T.ScopedType) (Variable, Maybe Kind)] 
                -> E.RHS Scoped 
                -> T.KindedType
                -> FreeST ([Level (E.KindedPat, T.KindedType) (Variable, Kind)], E.RHS Kinded)
        kindFun e = kindFun' 0
          where
            kindFun' i kctx tctxds ps rhs t = case (ps, normalise tds t) of
              ([], _) -> ([],) <$> kindRHS tds kctx rhs
              (TypeLevel (ai, mki) : ps', T.AppForall s' kx ((a, k) : aks) u) -> do
                k' <- case mki of
                  Just ki -> checkSubkindOf (T.fromVariable ki ai) ki k >> return ki
                  Nothing -> return k
                first (TypeLevel (ai, k') :) <$> kindFun' (i + 1) (Map.insert ai k' kctx) tctxds ps' 
                  rhs (T.AppForall s' kx aks $ subs a (T.Var (getSpan ai) k' ai) u)
              (ExpLevel  (p, mtp) : ps', t''@(T.AppArrow s' _ _ m u v)) -> do
                tp' <- case mtp of
                  Just tp -> do
                    (_, _, tp') <- checkProper kctx mod tp
                    return tp'
                  Nothing -> pure u
                (kctxi', p') <- kindPat kctx p
                first (ExpLevel (p', tp') :) <$> kindFun' (i + 1) kctxi' tctxds ps' rhs v
              (TypeLevel (a, k) : as, T.AppArrow s' _ _ m u v) -> 
                throwE (UnexpectedParam (getSpan a) i (ExpLevel u) (TypeLevel a))
              (ExpLevel  (p, t) : as, T.AppForall s' _ ((a, k) : aks) u) -> do
                (_, p') <- kindPat kctx p
                throwE (UnexpectedParam (getSpan p) i (TypeLevel k) (ExpLevel p'))
              (as, t') -> do
                throwE (ExpectsTooManyArgs (getSpan e) t (i + length as) i)

        kindRHS :: M.TypeDecls Kinded 
                -> KindCtx 
                -> E.RHS Scoped 
                -> FreeST (E.RHS Kinded)
        kindRHS tds kctx = \case
          E.GuardedRHS es mlds -> do
            (kctx', mlds') <- case mlds of
              Just lds -> second Just <$> kindLetDecls tds kctx lds
              Nothing -> pure (kctx, Nothing)
            es' <- mapM (bitraverse (kindExp kctx') (kindExp kctx')) es
            return $ E.GuardedRHS es' mlds'
          E.UnguardedRHS e mlds -> do
            (kctx', mlds') <- case mlds of
              Just lds -> second Just <$> kindLetDecls tds kctx lds
              Nothing -> pure (kctx, Nothing)
            e' <- kindExp kctx' e
            return $ E.UnguardedRHS e' mlds'

        kindPat :: KindCtx -> E.Pat Scoped -> FreeST (KindCtx, E.Pat Kinded)
        kindPat kctx = \case
          E.IntPat   s i -> pure (kctx, E.IntPat   s i)
          E.FloatPat s f -> pure (kctx, E.FloatPat s f)
          E.CharPat  s c -> pure (kctx, E.CharPat  s c)
          E.VarPat   s x -> pure (kctx, E.VarPat   s x)
          E.WildPat  s x -> pure (kctx, E.WildPat  s x)
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
          E.ChoicePat s i p -> second (E.ChoicePat s i) <$> kindPat kctx p
          E.AsPat s x p     -> second (E.AsPat     s x) <$> kindPat kctx p

        kindExp :: KindCtx -> E.ScopedExp -> FreeST E.KindedExp
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
              TypeLevel t -> TypeLevel <$> synth kctx mod t
            return $ E.App s e' args'
          E.Abs s pars m e -> do
            (kctx', pars') <- foldM (\(kctxi, parsi) -> \case 
                ExpLevel  (p, t) -> do
                  (kctxi', p') <- kindPat kctxi p
                  t' <- synth kctxi' mod t
                  return (kctxi', parsi ++ [ExpLevel (p', t')])
                TypeLevel (a, k) -> do
                  let kctxi' = Map.insert a k kctxi 
                  return (kctxi', parsi ++ [TypeLevel (a, k)])) 
              (kctx, []) pars
            e' <- kindExp kctx' e
            pure $ E.Abs s pars' m e'
          E.Let s lds e -> do 
            (kctx', lds') <- kindLetDecls tds kctx lds
            e' <- kindExp kctx' e
            return (E.Let s lds' e')
          E.Semi s e1 e2 -> E.Semi s <$> kindExp kctx e1 <*> kindExp kctx e2
          E.Case s e prhss -> do
            e' <- kindExp kctx e 
            prhss' <- forM prhss \(pi, rhsi) -> do
              (kctxi, pi') <- kindPat kctx pi
              rhsi' <- kindRHS tds kctxi rhsi
              return (pi', rhsi')
            return $ E.Case s e' prhss'
          E.If s e1 e2 e3 -> 
            E.If s <$> kindExp kctx e1 <*> kindExp kctx e2 <*> kindExp kctx e3
          E.Channel s t -> E.Channel s <$> synth kctx mod t
          E.Select s i -> pure $ E.Select s i

-- | Run kinding on a module, building the initial validation state from it.
-- This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * the given module, otherwise.
runKindModule :: M.ScopedModule -> Either [Error] M.KindedModule
runKindModule m = runValidation emptyValidationState (kindModule m)

-- | Run synthesis on type, building the initial validation state from a given
-- module. This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * a kind synthesized from the type, otherwise.
runSynth :: M.ScopedModule -> T.ScopedType -> Either [Error] T.KindedType
runSynth m t = runValidation emptyValidationState (synth Map.empty m t)

-- | Run checking on a type against a kind, building the initial validation 
-- state from a given module. This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * the same type, now annotated with kinds.
runCheck :: M.ScopedModule -> T.ScopedType -> Kind -> Either [Error] T.KindedType
runCheck m t k = runValidation emptyValidationState (check Map.empty m t k)

isStrictlyLin, isStrictlyChannel, isStrictlySession :: T.KindedType -> Bool

isStrictlyLin t = case T.getExt t of
  (Proper _ Lin _) -> True
  _ -> False

isStrictlyChannel t = case T.getExt t of
  (Proper _ _ Channel) -> True
  _ -> False


isStrictlySession t = case T.getExt t of
  (Proper _ _ Session) -> True
  _ -> False
