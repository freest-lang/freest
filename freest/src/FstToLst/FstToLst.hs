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
-- translateLetDecls ((E.FnDef var [(levels, rhs)]):letDecls) typeSigs cont = (L.App (L.Abs var (T.Int B.nullSpan) (translateLetDecls letDecls typeSigs cont)) (L.App generateFixPoint (L.Abs var (T.Int B.nullSpan) (foldr (\abs acc -> case abs of
--     B.ExpLevel pat -> translatePat (pat, T.Int B.nullSpan) acc
--     B.TypeLevel _ -> undefined) (translateRHS rhs) levels))))
translateLetDecls ((E.FnDef var patRhss):letDecls) typeSigs cont = (L.App (L.Abs var (T.Int B.nullSpan) (translateLetDecls letDecls typeSigs cont)) (L.App generateFixPoint (L.Abs var (T.Int B.nullSpan) (let eqs = bar patRhss in
                    let argsNum = length $ (fst . head) eqs in generateArgs argsNum argsNum (compileEquations argsNum (newKVars 0 argsNum) eqs generateError)))))
translateLetDecls ((E.TypeSig [var] ty):letDecls) typeSigs cont = translateLetDecls letDecls ((var,ty):typeSigs) cont

generateArgs :: Int -> Int -> L.Exp -> L.Exp
generateArgs 0 _ cont = cont
generateArgs n end cont = L.Abs (generatePrimitiveVar $ "arg"++(show (end-n))++"__") (T.Int B.nullSpan) (generateArgs (n-1) end cont) 

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

type Equation = ([E.Pat], L.Exp)

compileEquations :: Int -> [B.Variable] -> [Equation] -> L.Exp -> L.Exp
-- TODO: empty rule is not correct
-- compileEquations _ [] eqs def = let (hd:tl) = [e |(_,e) <- eqs] in 
--   L.App (L.App (L.Var $ generatePrimitiveVar "fatbar__") (foldl (\acc exp -> L.App (L.App (L.Var $ generatePrimitiveVar "fatbar__") acc) exp) hd tl)) def
compileEquations _ [] ((_,exp):_) _ = exp  
compileEquations num vars eqs def | allVars eqs = compileEquations num (tail vars) (replaceVar (head vars) eqs) def
                              | allCons eqs = L.Case (L.Var (head vars)) (foo num (tail vars) (groupEqs eqs) def)
                              | otherwise = undefined

allVars :: [Equation] -> Bool
allVars [] = True 
allVars (eq:eqs) = case (head . fst) eq of
  E.VarPat _ _ -> allVars eqs
  _ -> False

allCons :: [Equation] -> Bool
allCons [] = True
allCons (eq:eqs) = case (head . fst) eq of
  E.DConsPat _ _ _ -> allCons eqs
  _ -> False

replaceVar :: B.Variable -> [Equation] -> [Equation]
replaceVar var eqs = map (\(pats@((E.VarPat _ patVar):_), exp) -> (pats, subs patVar var exp)) eqs  

subs :: B.Variable -> B.Variable -> L.Exp -> L.Exp
subs target var exp@(L.Var v) = if v == target then (L.Var var) else exp
subs target var exp@(L.Abs v ty e) = if v == target then exp else (L.Abs v ty (subs target var e))
subs target var (L.App e1 e2) = L.App (subs target var e1) (subs target var e2)
subs target var (L.Case e alts) = L.Case (subs target var e) (altsSubs target var alts)
subs target var exp = exp

altsSubs :: B.Variable -> B.Variable -> [(L.Alt, L.Exp)] -> [(L.Alt, L.Exp)]
altsSubs target var alts = map (altSub target var) alts

altSub :: B.Variable -> B.Variable -> (L.Alt, L.Exp) -> (L.Alt, L.Exp)
altSub target var (L.ACon iden vars, exp) =
  if elem target vars then
    (L.ACon iden vars, exp)
  else
    (L.ACon iden vars, subs target var exp)

-- TODO implement this
groupEqs :: [Equation] -> [[Equation]]
groupEqs eqs = [eqs]

foo :: Int -> [B.Variable] -> [[Equation]] -> L.Exp -> [(L.Alt, L.Exp)]
-- def makes sense here?
foo num vars [] def = [(L.ADefault, def)]
foo num vars (eqs:eqss) def =
  let E.DConsPat _ iden pats = (head . fst . head) eqs
      freshVars = (newKVars num (length pats))
  in (L.ACon iden freshVars, compileEquations (num+length freshVars) (freshVars++vars) (updateHeadPattern eqs) def):(foo num vars eqss def)

newKVars :: Int -> Int -> [B.Variable]
newKVars from size = [generatePrimitiveVar ("arg"++(show n)++"__") | n <- [from..from+size]]

updateHeadPattern :: [Equation] -> [Equation]
updateHeadPattern eqs = map (\(pats, exp) -> (updateHeadPattern' pats, exp)) eqs

updateHeadPattern' :: [E.Pat] -> [E.Pat]
updateHeadPattern' ((E.DConsPat _ _ []):pats) = pats 
updateHeadPattern' ((E.DConsPat _ _ innerPats):pats) = innerPats++pats 

-- TODO: support functions that take type argument. For now just ignore it
bar :: [([B.Level E.Pat B.Variable], E.RHS)] -> [([E.Pat], L.Exp)]
bar patRHS = map (\(levels, rhs) -> (map (\(B.ExpLevel pat) -> pat) (filter (\level -> case level of 
  B.ExpLevel pat -> True
  B.TypeLevel _ -> False) levels), translateRHS rhs)) patRHS

generateError :: L.Exp
generateError = L.Var $ generatePrimitiveVar "error__"

