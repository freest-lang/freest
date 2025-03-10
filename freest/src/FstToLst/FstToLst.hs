module FstToLst.FstToLst where

import qualified Syntax.Module as M
import qualified LeaST.LeaST as L
import qualified Syntax.Expression as E
import qualified Syntax.Base as B
import qualified Syntax.Type as T

import Data.List ( find )
import Data.Maybe ( maybe )

fstToLst :: [M.Module] -> L.Exp
fstToLst modules = translateLetDecls (concat (map (\M.Module {M.name=_, M.imports=_, M.dataDecls=_, M.typeDecls=_, M.kindSigs=_, M.definitions=letDecls} -> letDecls) modules)) [] (L.Con $ B.Identifier B.nullSpan "()") 

translateLetDecls :: [E.LetDecl] -> [(B.Variable, T.Type)] -> L.Exp -> L.Exp  
translateLetDecls [] _ cont = cont
translateLetDecls ((E.ValDef pat@(E.VarPat _ (B.Variable { B.varSpan=_, B.internal=_, B.external="main"})) rhs):_) _ _ = translateRHS rhs
translateLetDecls ((E.ValDef pat@(E.VarPat _ var) rhs):letDecls) typeSigs cont = (L.App (translatePat (pat, getTypeFromTypeSigs typeSigs var) (translateLetDecls letDecls typeSigs cont)) (translateRHS rhs))
-- translateLetDecls ((E.FnDef var [(levels, rhs)]):letDecls) typeSigs cont = (L.App (L.Abs var (T.Int B.nullSpan) (L.App generateFixPoint (translateLetDecls letDecls typeSigs cont))) (foldr (\abs acc -> case abs of
--     B.ExpLevel pat -> translatePat (pat, T.Int B.nullSpan) acc
--     B.TypeLevel _ -> undefined) (translateRHS rhs) levels))
translateLetDecls ((E.FnDef var [(levels, rhs)]):letDecls) typeSigs cont = (L.App (L.Abs var (T.Int B.nullSpan) (translateLetDecls letDecls typeSigs cont)) (L.App generateFixPoint (L.Abs var (T.Int B.nullSpan) (foldr (\abs acc -> case abs of
    B.ExpLevel pat -> translatePat (pat, T.Int B.nullSpan) acc
    B.TypeLevel _ -> undefined) (translateRHS rhs) levels))))
translateLetDecls ((E.FnDef var patRhss):letDecls) _ _ = undefined
translateLetDecls ((E.TypeSig [var] ty):letDecls) typeSigs cont = translateLetDecls letDecls ((var,ty):typeSigs) cont

translateRHS :: E.RHS -> L.Exp
translateRHS (E.UnguardedRHS exp (Just letDecls)) = translateLetDecls letDecls [] (translateExp exp)
translateRHS (E.UnguardedRHS exp Nothing) = translateExp exp
translateRHS (E.GuardedRHS guards (Just letDecls)) = undefined
translateRHS (E.GuardedRHS guards Nothing) = undefined

translateExp :: E.Exp -> L.Exp
translateExp (E.Int _ int) = L.Lit (L.LInt int)
translateExp (E.Float _ float) = L.Lit (L.LFloat float)
translateExp (E.Char _ char) = L.Lit (L.LChar char)
translateExp (E.DCons _ iden) = L.Con iden
translateExp (E.Var _ var) = L.Var var
translateExp (E.App _ exp args) = foldl (\acc arg -> case arg of
  B.ExpLevel exp -> L.App acc (translateExp exp)
  B.TypeLevel ty -> L.TApp acc (L.Type ty)) (translateExp exp) args
translateExp (E.Abs _ levels _ exp) = foldr (\abs acc -> case abs of
  B.ExpLevel (pat, ty) -> translatePat (pat, ty) acc
  B.TypeLevel (_, kind) -> undefined) (translateExp exp) levels
translateExp (E.Let _ letDecls exp) = translateLetDecls letDecls [] (translateExp exp)
translateExp (E.If _ cond t f) = generateLeastIf (translateExp cond) (translateExp t) (translateExp f)
translateExp (E.Channel _ _) = undefined
translateExp (E.Select _ iden exp) = undefined

generateLeastIf :: L.Exp -> L.Exp -> L.Exp -> L.Exp
-- generateLeastIf cond t f = (L.App (L.App (L.App (L.Var $ generatePrimitiveVar "if__") cond) t) f)
generateLeastIf cond t f = L.Case cond [(L.ACon (B.Identifier B.nullSpan "True") [], t), (L.ACon (B.Identifier B.nullSpan "False") [], f)]

generatePrimitiveVar :: String -> B.Variable
generatePrimitiveVar name = B.Variable {B.internal=(-1), B.external=name, B.varSpan=B.Span{B.filepath="", B.startPos=(0,0), B.endPos=(0,0)}}

translatePat :: (E.Pat, T.Type) -> L.Exp -> L.Exp
translatePat ((E.VarPat _ var), ty) cont = L.Abs var ty cont  

getTypeFromTypeSigs :: [(B.Variable, T.Type)] -> B.Variable -> T.Type
getTypeFromTypeSigs typeSigs var = case find ((var ==) . fst) typeSigs of
  Just (_, ty) -> ty
  Nothing -> T.Int B.nullSpan

generateFixPoint :: L.Exp
generateFixPoint = L.Abs (generatePrimitiveVar "f__") (T.Int B.nullSpan) (
  L.App 
  (L.Abs (generatePrimitiveVar "x__") (T.Int B.nullSpan) (
    L.App (L.Var $ generatePrimitiveVar "f__") 
      (L.Abs (generatePrimitiveVar "v__") (T.Int B.nullSpan)
        (L.App 
          (L.App 
            (L.Var $ generatePrimitiveVar "x__")
            (L.Var $ generatePrimitiveVar "x__"))
          (L.Var $ generatePrimitiveVar "v__")))))
  (L.Abs (generatePrimitiveVar "x__") (T.Int B.nullSpan) (
    L.App (L.Var $ generatePrimitiveVar "f__") 
      (L.Abs (generatePrimitiveVar "v__") (T.Int B.nullSpan)
        (L.App 
          (L.App 
            (L.Var $ generatePrimitiveVar "x__")
            (L.Var $ generatePrimitiveVar "x__"))
          (L.Var $ generatePrimitiveVar "v__"))))))
