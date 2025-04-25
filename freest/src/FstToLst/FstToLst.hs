module FstToLst.FstToLst where

import qualified Syntax.Module as M
import qualified LeaST.LeaST as L
import qualified Syntax.Expression as E
import qualified Syntax.Base as B
import qualified Syntax.Type as T

import Data.List ( find )
import Data.Maybe ( maybe )
import Debug.Trace

fstToLst :: [M.Module] -> L.Exp
fstToLst modules = translateLetDecls (concat (map (\M.Module {M.name=_, M.imports=_, M.dataDecls=_, M.typeDecls=_, M.kindSigs=_, M.definitions=letDecls} -> letDecls) modules)) [] (L.Con $ B.Identifier B.nullSpan "()") 

translateLetDecls :: [E.LetDecl] -> [(B.Variable, T.Type)] -> L.Exp -> L.Exp  
translateLetDecls [] _ cont = cont
translateLetDecls ((E.ValDef pat@(E.VarPat _ (B.Variable { B.varSpan=_, B.internal=_, B.external="main"})) rhs):_) _ _ = translateRHS rhs
translateLetDecls ((E.ValDef pat@(E.VarPat _ var) rhs):letDecls) typeSigs cont = (L.App (translatePat (pat, getTypeFromTypeSigs typeSigs var) (translateLetDecls letDecls typeSigs cont)) (translateRHS rhs))
translateLetDecls ((E.ValDef pat rhs):letDecls) typeSigs cont = L.App (L.Abs (generatePrimitiveVar "arg0__") (T.Int B.nullSpan) (compileEquations 1 (newKVars 0 0) [([pat], cont)] generateError)) (translateRHS rhs) 
-- (L.Case (translateRHS rhs) (foo 0 [] (replaceVar (head vars) s)[[([pat], cont)]] generateError))
-- translateLetDecls ((E.FnDef var [(levels, rhs)]):letDecls) typeSigs cont = (L.App (L.Abs var (T.Int B.nullSpan) (translateLetDecls letDecls typeSigs cont)) (L.App generateFixPoint (L.Abs var (T.Int B.nullSpan) (foldr (\abs acc -> case abs of
--     B.ExpLevel pat -> translatePat (pat, T.Int B.nullSpan) acc
--     B.TypeLevel _ -> undefined) (translateRHS rhs) levels))))
translateLetDecls ((E.FnDef var patRhss):letDecls) typeSigs cont = (L.App (L.Abs var (T.Int B.nullSpan) (translateLetDecls letDecls typeSigs cont)) (L.App generateFixPoint (L.Abs var (T.Int B.nullSpan) (let eqs = bar patRhss in
  let argsNum = length $ (fst . head) eqs in generateArgs argsNum argsNum (compileEquations argsNum (newKVars 0 (argsNum-1)) eqs generateError)))))
-- TODO: remover ctx das assinaturas
translateLetDecls ((E.TypeSig vars ty):letDecls) typeSigs cont = translateLetDecls letDecls [] cont
translateLetDecls (letDecl:_) _ _ = traceShow letDecl undefined

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
translateExp (E.Case _ exp patRhss) = L.App (L.Abs (generatePrimitiveVar "arg0__") (T.Int B.nullSpan) (compileEquations 0 (newKVars 0 0) (map (\(pat, rhs) -> ([pat], translateRHS rhs)) patRhss) generateError)) (translateExp exp)
translateExp (E.Channel _ _) = L.App (L.Var $ generatePrimitiveVar "chan") generateUnit
translateExp (E.Select _ iden exp) = undefined

generateLeastIf :: L.Exp -> L.Exp -> L.Exp -> L.Exp
-- generateLeastIf cond t f = (L.App (L.App (L.App (L.Var $ generatePrimitiveVar "if__") cond) t) f)
generateLeastIf cond t f = L.Case cond [(L.ACon (B.Identifier B.nullSpan "True") [], t), (L.ACon (B.Identifier B.nullSpan "False") [], f)]

generatePrimitiveVar :: String -> B.Variable
generatePrimitiveVar name = B.Variable {B.internal=(-1), B.external=name, B.varSpan=B.Span{B.filepath="", B.startPos=(0,0), B.endPos=(0,0)}}

generateUnit :: L.Exp
generateUnit = L.Con (B.Identifier B.nullSpan "()")

-- TODO: necessario um variavel fresca para o wildpat??
translatePat :: (E.Pat, T.Type) -> L.Exp -> L.Exp
translatePat ((E.VarPat _ var), ty) cont = L.Abs var ty cont  
translatePat ((E.WildPat _ var), ty) cont = L.Abs var ty cont  

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
-- TODO: empty rule is not correct, maybe?
-- compileEquations _ [] eqs def = let (hd:tl) = [e |(_,e) <- eqs] in 
--   L.App (L.App (L.Var $ generatePrimitiveVar "fatbar__") (foldl (\acc exp -> L.App (L.App (L.Var $ generatePrimitiveVar "fatbar__") acc) exp) hd tl)) def
compileEquations _ [] ((_,exp):_) _ = exp
compileEquations num vars eqs def | allVars eqs = compileEquations num (tail vars) (updateHeadPattern (replaceVar (head vars) eqs)) def
                              | allCons eqs = L.Case (L.Var (head vars)) (foo num (tail vars) (groupEqs eqs) def)
                              | otherwise = foldr (\groupedEqs acc -> compileEquations num vars groupedEqs acc) def (reverse $ mixtureGroup eqs)

allVars :: [Equation] -> Bool
allVars [] = True 
allVars (eq:eqs) = case (head . fst) eq of
  E.VarPat _ _ -> allVars eqs
  _ -> False

allCons :: [Equation] -> Bool
allCons [] = True
allCons (eq:eqs) = case (head . fst) eq of
  E.DConsPat _ _ _ -> allCons eqs
  E.IntPat _ _ -> allCons eqs
  E.FloatPat _ _ -> allCons eqs
  E.CharPat _ _ -> allCons eqs
  _ -> False

replaceVar :: B.Variable -> [Equation] -> [Equation]
replaceVar var eqs = map (\(pats, exp) -> case pats of
  ((E.VarPat _ patVar):_) -> (pats, subs patVar var exp)
  _ -> traceShow pats undefined) eqs

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
altSub target var (L.AWildCard, exp) = (L.AWildCard, subs target var exp)

-- TODO Verificar que a ordem nao muda
-- Only called if all are constructor
groupEqs :: [Equation] -> [[Equation]]
groupEqs [] = [[]]
groupEqs (eq:eqs) = addEq eq (groupEqs eqs)

-- Ewwwwww
addEq :: Equation -> [[Equation]] -> [[Equation]]
addEq eq [] = [[eq]]
addEq eq [[]] = [[eq]]
addEq eq@((patX:_),_) (eqs@(((patY:_), _):_):eqss) = if patIsEq patX patY then (eq:eqs):eqss else (eqs: addEq eq eqss)

mixtureGroup :: [Equation] -> [[Equation]]
mixtureGroup [] = [[]]
mixtureGroup (eq:eqs) = addEqMix eq (mixtureGroup eqs)

addEqMix :: Equation -> [[Equation]] -> [[Equation]]
addEqMix eq [] = [[eq]]
addEqMix eq [[]] = [[eq]]
addEqMix eq@((patX:_),_) (eqs@(((patY:_), _):_):eqss) = if patIsEqMix patX patY then (eq:eqs): eqss else (eqs: (addEqMix eq eqss))

patIsEq :: E.Pat -> E.Pat -> Bool
patIsEq (E.IntPat _ x) (E.IntPat _ y) = x == y
patIsEq (E.FloatPat _ x) (E.FloatPat _ y) = x == y
patIsEq (E.CharPat _ x) (E.CharPat _ y) = x == y
patIsEq (E.WildPat _ x) (E.WildPat _ y) = undefined
patIsEq (E.VarPat _ x) (E.VarPat _ y) = undefined
patIsEq (E.DConsPat _ (B.Identifier _ x) _) (E.DConsPat _ (B.Identifier _ y) _) = x == y
patIsEq (E.AsPat _ x xPat) (E.AsPat _ y yPat) = undefined
patIsEq _ _ = False

patIsEqMix :: E.Pat -> E.Pat -> Bool
patIsEqMix (E.VarPat _ _) (E.VarPat _ _) = True
patIsEqMix (E.IntPat _ _) (E.IntPat _ _) = True 
patIsEqMix (E.FloatPat _ _) (E.FloatPat _ _) = True 
patIsEqMix (E.CharPat _ _) (E.CharPat _ _) = True 
patIsEqMix (E.WildPat _ _) (E.WildPat _ _) = undefined
patIsEqMix (E.DConsPat _ _ _) (E.DConsPat _ _ _) = undefined
patIsEqMix _ _ = False

-- TODO: relembrar o que isto faz e dar um nome adequado
foo :: Int -> [B.Variable] -> [[Equation]] -> L.Exp -> [(L.Alt, L.Exp)]
-- def makes sense here?
foo num vars [] def = [(L.AWildCard, def)]
-- foo num vars (eqs:eqss) def =
--   let E.DConsPat _ iden pats = (head . fst . head) eqs
--       freshVars = (newKVars num (length pats))
--   in (L.ACon iden freshVars, compileEquations (num+length freshVars) (freshVars++vars) (updateHeadPattern eqs) def):(foo num vars eqss def)
foo num vars (eqs:eqss) def =
  case (head . fst . head) eqs of
    E.DConsPat _ iden pats -> let freshVars = (newKVars num (length pats - 1)) in
    -- Posso por aqui pats em vez de updateHeadPattern eqs ??
      (L.ACon iden freshVars, compileEquations (num+length freshVars) (freshVars++vars) (updateHeadPattern eqs) def):(foo num vars eqss def)
    E.IntPat _ n -> (L.ALit $ L.LInt n, compileEquations num vars (updateHeadPattern eqs) def) : (foo num vars eqss def)
    E.FloatPat _ n -> (L.ALit $ L.LFloat n, compileEquations 0 [] (updateHeadPattern eqs) def) : (foo num vars eqss def)
    E.CharPat _ c -> (L.ALit $ L.LChar c, compileEquations 0 [] (updateHeadPattern eqs) def) : (foo num vars eqss def)

newKVars :: Int -> Int -> [B.Variable]
newKVars from size = [generatePrimitiveVar ("arg"++(show n)++"__") | n <- [from..from+size]]

updateHeadPattern :: [Equation] -> [Equation]
updateHeadPattern eqs = map (\(pats, exp) -> (updateHeadPattern' pats, exp)) eqs

updateHeadPattern' :: [E.Pat] -> [E.Pat]
updateHeadPattern' ((E.DConsPat _ _ []):pats) = pats 
updateHeadPattern' ((E.DConsPat _ _ innerPats):pats) = innerPats++pats 
updateHeadPattern' (pat:pats) = pats

-- TODO: rename this for function for something better
-- TODO: support functions that take type argument. For now just ignore it
bar :: [([B.Level E.Pat B.Variable], E.RHS)] -> [([E.Pat], L.Exp)]
bar patRHS = map (\(levels, rhs) -> (map (\(B.ExpLevel pat) -> pat) (filter (\level -> case level of 
  B.ExpLevel pat -> True
  B.TypeLevel _ -> False) levels), translateRHS rhs)) patRHS

generateError :: L.Exp
generateError = L.Var $ generatePrimitiveVar "error__"
