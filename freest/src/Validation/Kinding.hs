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
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Debug.Trace (traceM)
import Data.Coerce

-- | The kinding context. Keeps track of type variables and their kinds.
type KindCtx = Map.Map Variable Kind

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
  T.AppDual s _ t -> check ctx mod t (ls s)
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
    t <- synth ctx mod t
    let (ks,kn) = Expose.kindArrow (T.getExt t)
    (k,ts) <- checkArgs s t (T.getExt t) (length ts) (length ks) ts ks kn
    pure $ T.App s k t ts
    where
      checkArgs :: Span -> T.KindedType -> Kind -> Int -> Int -- error info
                -> [T.ScopedType] -> [Kind] -> Kind
                -> FreeST (Kind,[T.KindedType])
      checkArgs _ _ _ _ _ [] ks' kn = pure
        (foldr (\k k' -> Arrow (spanFromTo k k') k k') kn ks',[])
      checkArgs s t k nargs npars ts [] kn = do
        throwE (GivenTooManyArgsK (spanFromTo (head ts) (last ts)) (T.setExt k t) kn npars nargs)
      checkArgs s t k nargs npars (t' : ts') (k' : ks') kn =
        check ctx mod t' k' >> checkArgs s t k nargs npars ts' ks' kn
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
          checkProper ctx m t  >>= \(m'',_ ,t) -> pure (join m' m'', t:ts)

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
checkPrekindK _ _ _ = undefined

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
  lds <- mapM kindLetDecl (M.definitions mod)
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

    kindLetDecl :: E.LetDecl Scoped -> FreeST (E.LetDecl Kinded)
    kindLetDecl = \case
      E.ValDef p rhs -> E.ValDef <$> kindPat p <*> kindRHS rhs
      E.FnDef x psrhss -> do
        rhss <- forM psrhss \(psj, rhsj) -> do
            pjs' <- forM psj (\case
                      ExpLevel p -> ExpLevel <$> kindPat p
                      TypeLevel t -> pure $ TypeLevel t)
            rhs <- kindRHS rhsj
            return (pjs', rhs)
        return $ E.FnDef x rhss

      E.TypeSig xs t -> E.TypeSig xs <$> synth Map.empty mod t
      E.Mutual xs -> E.Mutual <$> forM xs kindLetDecl

    kindRHS = \case
      E.GuardedRHS es ldcls -> do
        es' <- mapM (bitraverse kindExp kindExp) es
        ldcls' <- case ldcls of
          Nothing -> pure Nothing
          Just ldcl -> Just <$> forM ldcl kindLetDecl
        return $ E.GuardedRHS es' ldcls'
      E.UnguardedRHS e ldcls -> do
        e' <- kindExp e
        ldcls' <- case ldcls of
          Nothing -> pure Nothing
          Just ldcl -> Just <$> forM ldcl kindLetDecl
        return $ E.UnguardedRHS e' ldcls'

    kindPat = \case
      E.IntPat s i -> pure $ E.IntPat s i
      E.FloatPat s d -> pure $ E.FloatPat s d
      E.CharPat s c -> pure $ E.CharPat s c
      E.WildPat s a -> pure $ E.WildPat s a
      E.VarPat s a -> pure $ E.VarPat s a
      E.DConsPat s i pats -> E.DConsPat s i <$> forM pats kindPat
      E.ChoicePat s i p -> E.ChoicePat s i <$> kindPat p
      E.AsPat s a p -> E.AsPat s a <$> kindPat p

    kindExp = \case
      E.Int s i -> pure $ E.Int s i
      E.Float s d -> pure $ E.Float s d
      E.Char s c -> pure $ E.Char s c
      E.DCons s i -> pure $ E.DCons s i
      E.Var s a -> pure $ E.Var s a
      E.App s e lvl -> do --  [Level (Exp x) (Type x)]
        e' <- kindExp e
        lvls <- forM lvl (\case
                      ExpLevel e -> ExpLevel <$> kindExp e
                      TypeLevel t -> TypeLevel <$> synth Map.empty mod t)
        pure $ E.App s e' lvls
      E.Abs s lvls mult e -> do -- [Level (Pat x, Type x) (Variable,Kind)] Multiplicity (Exp x)
        lvls' <- forM lvls (\case
                                ExpLevel e -> ExpLevel <$> bitraverse kindPat (synth Map.empty mod) e
                                TypeLevel vk -> pure $ TypeLevel vk
                            )
        e' <- kindExp e
        pure $ E.Abs s lvls' mult e'
      E.Let s ldcls e -> E.Let s <$> forM ldcls kindLetDecl <*> kindExp e
      E.Semi s e1 e2 -> E.Semi s <$> kindExp e1 <*> kindExp e2
      E.Case s e prhss -> E.Case s <$> kindExp e <*> forM prhss (bitraverse kindPat kindRHS)
      E.If s e1 e2 e3 -> E.If s <$> kindExp e1 <*> kindExp e2 <*> kindExp e3
      E.Channel s t -> E.Channel s <$> synth Map.empty mod t
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
