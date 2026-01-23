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
synth :: KindCtx -> T.ParsedType -> Validation Kinded T.KindedType
synth ctx = \case
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
                            <$> checkSession ctx t) (Un, Session, []) lts
    pure $ T.AppLinChoice s (Proper s Lin pk) (Proper s m pk) p lts 
  T.End s _ p -> pure $ T.End s (lc s) p
  T.Skip s _ -> pure $ T.Skip s (us s)
  T.Void s _ k -> pure $ T.Void s k k
  T.AppSemi s _ t u -> do
    (m1, pk1, t) <- checkSession ctx t
    (m2, pk2, u) <- checkSession ctx u
    let k = Proper s (if pk1 == Channel then m1 else join m1 m2) (meet pk1 pk2) 
    return $ T.AppSemi s k t u
  T.AppDual s _ t -> synthCheck ctx t (ls s)
  -- Polymorphism
  T.AppQuant s _ p aks t -> do
    checkProper (Map.fromList aks `Map.union` ctx) t
    >>= \case (m, Channel, t) -> pure $ T.AppQuant s (Proper s Lin Channel) p aks t
              (m, Session, t) -> pure $ T.AppQuant s (Proper s Lin Session) p aks t
              (m, Top    , t) -> pure $ T.AppQuant s (Proper s m   Top    ) p aks t
  -- Equations (including built-ins)
  T.TName s _ i -> flip (T.TName s) i <$> lookupKind i
  T.Tuple s _ ts -> do
    (m, ts) <- foldCheckProperJoin ctx Un ts
    return $ T.Tuple s (Proper s m Top) ts
  T.List s _ t -> do
    (m, _, t) <- checkProper ctx t
    pure $ T.List s (Proper s m Top) t    
  T.DName s _ i -> flip (T.DName s) i <$> lookupKind i
  -- Higher-order
  T.Var s _ a -> case ctx Map.!? a of
    Just k -> pure $ T.Var s k a
    Nothing -> throwE (TypeVarOutOfScope s a)
  T.App s _ t ts -> do
    t <- synth ctx t
    let (ks,kn) = Expose.kindArrow (T.getExt t)
    (k,ts) <- checkArgs s t (T.getExt t) (length ts) (length ks) ts ks kn
    pure $ T.App s k t ts
    where
      checkArgs :: Span -> T.KindedType -> Kind -> Int -> Int -- error info
                -> [T.ParsedType] -> [Kind] -> Kind
                -> Validation Kinded (Kind,[T.KindedType])
      checkArgs _ _ _ _ _ [] ks' kn = pure
        (foldr (\k k' -> Arrow (spanFromTo k k') k k') kn ks',[])         
      checkArgs s t k nargs npars ts [] kn = do 
        throwE (GivenTooManyArgsK (spanFromTo (head ts) (last ts)) (T.setExt k t) kn npars nargs)
      checkArgs s t k nargs npars (t' : ts') (k' : ks') kn = 
        check ctx t' k' >> checkArgs s t k nargs npars ts' ks' kn                
  T.Abs s _ aks t -> do
    t' <- synth (Map.fromList aks `Map.union` ctx) t
    let k = foldr (\(_, ki) k -> Arrow (spanFromTo ki k) ki k) k aks
    return $ T.Abs s k aks t'

-- | Check a type against a given kind.
check :: KindCtx -> T.ParsedType -> Kind -> Validation Kinded ()
check ctx t k = Control.Monad.State.void (synthCheck ctx t k)

checkK :: T.KindedType -> Kind -> Validation Kinded ()
checkK t =  -- Control.Monad.State.void (synthCheck ctx t k)
  checkSubkindOf t (T.getExt t)

-- | Calculate the join of the multiplicities of a list of types, starting
-- from a given multiplicity. Throws an error if a non-proper type is
-- encountered.
foldCheckProperJoin :: KindCtx -> Multiplicity -> [T.ParsedType] -> Validation Kinded (Multiplicity, [T.KindedType])
foldCheckProperJoin ctx m = foldM checkProperJoin (m,[])
  where checkProperJoin (m', ts) t =
          checkProper ctx t >>= \(m'',_ ,t) -> pure (join m' m'', t:ts)

-- | Check if a type is a proper type. If so, return its minimal multiplicity 
-- and prekind. Otherwise, throw an error.
checkProper :: KindCtx -> T.ParsedType -> Validation Kinded (Multiplicity, Prekind, T.KindedType)
checkProper ctx t = kindedTypeM >>= \kT -> case T.getExt kT of  
    Proper _ m pk ->  pure (m,pk,kT)
    k -> throwE (ProperKindMismatch (getSpan t) kT k)
    where
      kindedTypeM = synth ctx t

-- | Check if a type is a proper type. If so, return its minimal multiplicity 
-- and prekind. Otherwise, throw an error.
checkProperK :: T.KindedType -> Validation Kinded (Multiplicity, Prekind, T.KindedType)
checkProperK t = case T.getExt t of  
    Proper _ m pk ->  pure (m,pk,t)
    k -> throwE (ProperKindMismatch (getSpan t) t k)     
  
-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkSession :: KindCtx -> T.ParsedType -> Validation Kinded (Multiplicity, Prekind, T.KindedType)
checkSession ctx t = checkPrekind ctx t Session

checkSessionK :: KindCtx -> T.KindedType -> Validation Kinded (Multiplicity, Prekind)
checkSessionK ctx t = checkPrekindK ctx t Session

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkChannel :: KindCtx -> T.KindedType -> Validation Kinded (Multiplicity, Prekind) -- TODO: parsed version?
checkChannel ctx t = checkPrekindK ctx t Channel

-- | Check if a type is a proper type of the given prekind. If so, return its 
-- minimal multiplicity and prekind. Otherwise, throw an error.
checkPrekind :: KindCtx -> T.ParsedType -> Prekind -> Validation Kinded (Multiplicity, Prekind, T.KindedType)
checkPrekind ctx t pk = do
  (m, pk', kt) <- checkProper ctx t
  unless (pk' <: pk) $
    throwE (PrekindMismatch (getSpan t) pk kt (Proper (getSpan t) m pk'))
  return (m, pk', kt)

checkPrekindK :: KindCtx -> T.KindedType -> Prekind -> Validation Kinded (Multiplicity, Prekind)
checkPrekindK _ _ _ = undefined

-- | Check if the kind of a type is a subkind of another. If not, throw an 
-- error located at the type.
checkSubkindOf :: T.KindedType -> Kind -> Kind -> Validation Kinded ()
checkSubkindOf t k' k =
  unless (k' <: k) $
    throwE (KindMismatch (getSpan t) k t k')

-- | Check if the kind of a type is a subkind of another in a contravariant 
-- position. If not, throw an error located at the type.
checkSubkindOf' :: T.KindedType -> Kind -> Kind -> Validation Kinded ()
checkSubkindOf' t k' k = unless (k' <: k) $
     throwE (KindMismatch (getSpan t) k' t k)

     
checkSubkindOfP' :: T.ParsedType -> Kind -> Kind -> Validation Kinded ()
checkSubkindOfP' t k' k = do
  t' <- synth Map.empty t -- TODO: map empty
  unless (k' <: k) $
     throwE (KindMismatch (getSpan t) k' t' k)

-- | Synthesize the kind of a type and check if it is a subkind of another
-- kind.
synthCheck :: KindCtx -> T.ParsedType -> Kind -> Validation Kinded T.KindedType
synthCheck ctx t k = do
  kt <- synth ctx t
  checkSubkindOf kt (T.getExt kt) k
  return kt

-- | Check a module for type formation.
kindModule :: M.ParsedModule -> Validation Kinded M.KindedModule
kindModule m = do
  tds <- forM (M.typeDecls m) kindTypeDecl
  dds <- forM (M.dataDecls m) kindDataDecl
  modify (\s -> s{typeDecls = Map.fromList tds}) -- modify dds?
  lds <- mapM kindLetDecl (M.definitions m)
  -- undefined
  return m{M.typeDecls = tds, M.dataDecls = dds, M.definitions = lds}
  -- TODO: convert module and convert expressions as well
  where 
    kindTypeDecl :: (Identifier, T.ParsedType) -> Validation Kinded (Identifier, T.KindedType)
    kindTypeDecl (i, t) = do
      k <- lookupKind i
      t' <- case t of
        T.Abs s _ aks u -> do
          aks' <- kindParams aks k
          u' <- synth Map.empty u -- TODO: Map.empty'
          return $ T.Abs s k aks' u'
          where
            kindParams ((a, Var _ _) : aks') (Arrow _ k1 k2) =
              ((a, k1) :) <$> kindParams aks' k2
            kindParams ((a, k) : aks') (Arrow _ k1 k2) = do
              checkSubkindOfP' (T.Var (getSpan a) Syntax.Base.void a) k1 k
              ((a, k) :) <$> kindParams aks' k2
            kindParams []  _ = pure []
            kindParams aks _ = throwE (ExpectsTooManyArgsK (getSpan i) i k)

        t' -> synth Map.empty t' -- TODO: Map.empty? 
      checkK t' k
      return (i, t')

    kindDataDecl :: (Identifier, [(Variable, Kind)], M.ParsedConsDeclList) -> Validation Kinded (Identifier, [(Variable, Kind)], M.KindedConsDeclList)
    kindDataDecl (i, aks, t) = do
      k <- lookupKind i
      kcdl <- checkDataDecl k id Map.empty aks k
      return (i, aks, kcdl)
      -- mapM (\(id, ts) -> mapM (synth Map.empty) ts) t
      where
        checkDataDecl k f ctx [] _ = checkConsDecls k f ctx t
        checkDataDecl k f ctx ((a, Var _ _) : aks') (Arrow s k1 k2) =
          checkDataDecl k (f . Arrow s k1) (Map.insert a k1 ctx) aks' k2
        checkDataDecl k f ctx ((a, k') : aks') (Arrow s k1 k2) = do
          checkSubkindOfP' (T.Var (getSpan a) Syntax.Base.void a) k1 k'
          checkDataDecl k (f . Arrow s k') (Map.insert a k' ctx) aks' k2
        checkDataDecl k f ctx aks Proper{} =
          throwE (ExpectsTooManyArgsK (getSpan i) i k)

        checkConsDecls k f ctx cds = do
          (m, t) <- synthDataMult ctx cds
          let k' = f (Proper (getSpan i) m Top)
          unless (k' <: k)
            (throwE (KindMismatch (getSpan i) k (T.TName (getSpan i) k' i) k'))
--          ts <- mapM (\(id, t) -> synth ctx t >>= \t' -> pure (id, t')) cds
          return t -- TODO: synth all the types and zip

        -- KindCtx -> Multiplicity -> [T.ParsedType] -> Validation Kinded (Multiplicity, [T.KindedType])
        synthDataMult ctx = foldM (\(m, acc) (id, t) -> foldCheckProperJoin ctx m t >>= \(m, t) -> pure (m, (id, t) : acc)) (Un, [])
--        synthDataMult ctx = foldM (\(m,ts) t -> foldCheckProperJoin ctx m t) (Un,[])
        -- synthDataMult ctx = foldM (foldCheckProperJoin ctx) Un

    kindLetDecl :: E.ParsedLetDecl -> Validation Kinded E.KindedLetDecl
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

      E.TypeSig xs t -> E.TypeSig xs <$> synth Map.empty t
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
                      TypeLevel t -> TypeLevel <$> synth Map.empty t)    
        pure $ E.App s e' lvls
      E.Abs s lvls m e -> do -- [Level (Pat x, Type x) (Variable,Kind)] Multiplicity (Exp x)
        lvls' <- forM lvls (\case
                                ExpLevel e -> ExpLevel <$> bitraverse kindPat (synth Map.empty) e
                                TypeLevel vk -> pure $ TypeLevel vk
                            )
        e' <- kindExp e
        pure $ E.Abs s lvls' m e'
      E.Let s ldcls e -> E.Let s <$> forM ldcls kindLetDecl <*> kindExp e
      E.Semi s e1 e2 -> E.Semi s <$> kindExp e1 <*> kindExp e2
      E.Case s e prhss -> E.Case s <$> kindExp e <*> forM prhss (bitraverse kindPat kindRHS)
      E.If s e1 e2 e3 -> E.If s <$> kindExp e1 <*> kindExp e2 <*> kindExp e3
      E.Channel s t -> E.Channel s <$> synth Map.empty t
      E.Select s i -> pure $ E.Select s i
      
-- VALIDATION STATE
--       errors    :: [Error x]
--     , kindSigs  :: Map.Map Identifier K.Kind
--     , typeDecls :: TypeDeclMap x
--     , dataDecls :: DataDeclMap x 
--     , consDecls :: Map.Map Identifier (Identifier, [(Variable, K.Kind)], [T.Type x])
    

-- | Run kinding on a module, building the initial validation state from it.
-- This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * the given module, otherwise.
runKindModule :: M.ParsedModule -> Either [KindedError] M.KindedModule
runKindModule m = undefined -- runValidation (buildValidationState m) (kindModule m)

-- | Run synthesis on type, building the initial validation state from a given
-- module. This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * a kind synthesized from the type, otherwise.
runSynth :: M.ParsedModule -> T.ParsedType -> Either [KindedError] Kind
runSynth m t = undefined -- runValidation (buildValidationState m) (synth Map.empty t)

-- | Run checking on a type against a kind, building the initial validation 
-- state from a given module. This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * unit, otherwise.
runCheck :: M.ParsedModule -> T.ParsedType -> Kind -> Either [KindedError] ()
runCheck m t k = undefined -- runValidation (buildValidationState m) (check Map.empty t k)

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
