{-# LANGUAGE TupleSections #-}
module Parser.Scoping
  (runScoping)
where

import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Type as T
import Syntax.Module (Module(..))
import Utils.Error (Error(..))

import Control.Monad (replicateM)
import Control.Monad.State ( gets, modify, State, runState)
import qualified Data.Map as Map
import Data.Bifunctor (first, second)

type Scoping = State ScopingState
data ScopingState = ScopingState{counter :: Int, errors :: [Error]}

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

scopeModule :: ScopingCtx -> Module -> Scoping (ScopingCtx, Module)
scopeModule ctx m = do
  dataDecls' <- scopeDataDecls (dataDecls m)
  typeDecls' <- scopeTypeDecls (typeDecls m)
  -- (ctx', defs') <- scopeDefs ctx (definitions m)
  return (ctx, Module (name m) (imports m) dataDecls' typeDecls' (definitions m))

type ScopingCtx = Map.Map String Int

type DataDecl = (Variable, [Variable], [(Variable, [T.Type])])

scopeDataDecls :: [DataDecl] -> Scoping [DataDecl]
scopeDataDecls = mapM scopeDataDecl
  where scopeDataDecl (n, as, cs) = do
          as' <- mapM (\a -> incCounter >>= \i -> return a{internal=i}) as
          let ctx' = Map.fromList $ map (\a -> (external a, internal a)) as'
          (n,as',) <$> mapM (scopeConsDecl ctx') cs
        scopeConsDecl ctx (c, ts) = (c,) <$> mapM (scopeType ctx) ts

scopeTypeDecls :: [(Variable, [Variable], T.Type)] -> Scoping [(Variable, [Variable], T.Type)]
scopeTypeDecls = mapM scopeTypeDecl
  where scopeTypeDecl (n, as, t) = do
          as' <- mapM (\a -> incCounter >>= \i -> return a{internal=i}) as
          (n, as',) <$> scopeType (Map.fromList $ map (\a -> (external a, internal a)) as') t

scopeDefs :: ScopingCtx -> [E.LetDecl] -> Scoping (ScopingCtx, [E.LetDecl])
scopeDefs ctx ds = return (ctx, ds)

scopeType :: ScopingCtx -> T.Type -> Scoping T.Type
scopeType ctx (T.Labelled  s l lts) =
  let lts' = mapM (\(l,t) -> (l,) <$> scopeType ctx t) lts
  in T.Labelled s l <$> lts'
scopeType ctx (T.Tuple s ts) = 
  T.Tuple s <$> mapM (scopeType ctx) ts
scopeType ctx t@(T.Var s a) =
  case ctx Map.!? external a of
    Just i  -> return $ T.Var s a{internal=i}
    Nothing -> insertError (OutOfScope (getSpan a) a) >> return t
scopeType ctx (T.App s t ts) = 
  T.App s <$> scopeType ctx t <*> mapM (scopeType ctx) ts
scopeType ctx (T.Abs s aks t) = do
  aks' <- mapM (\(a,k) -> incCounter >>= \i -> return (a{internal=i},k)) aks
  let ctx' = ctx `Map.union` Map.fromList (map (\(a,_) -> (external a, internal a)) aks')
  T.Abs s aks' <$> scopeType ctx' t
scopeType ctx t = return t
