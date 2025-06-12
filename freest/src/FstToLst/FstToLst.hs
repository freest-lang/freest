module FstToLst.FstToLst where

import qualified Syntax.Module as M
import qualified LeaST.LeaST as L
import LeaST.Interpreter ( builtins )
import qualified Syntax.Expression as E
import qualified Syntax.Base as B
import qualified Syntax.Type as T

import Data.List ( find )
import Data.Maybe ( maybe )
import Debug.Trace

fstToLst :: [M.Module] -> L.Exp
fstToLst modules = traceShow modules $ translateTopLevelLetDecls (concatMap M.definitions modules) 

translateTopLevelLetDecls :: [E.LetDecl] -> L.Exp
translateTopLevelLetDecls letDecls = fst $ translateLetDecls 0 letDecls [] generateUnit

translateLetDecls :: Int -> [E.LetDecl] -> [(B.Variable, T.Type)] -> L.Exp -> (L.Exp, Int)
translateLetDecls counter [] _ cont = (cont, counter)
translateLetDecls counter ((E.ValDef pat@(E.VarPat _ var) rhs):letDecls) typeSigs cont =
  let (rhsExp, counter1) = translateRHS counter rhs
      (translateLetDeclsRes, counter2) = translateLetDecls counter1 letDecls typeSigs cont in
  (L.App (translatePat (pat, getTypeFromTypeSigs typeSigs var) translateLetDeclsRes) (L.App (L.App (L.Var $ generatePrimitiveVar "fatbar__") rhsExp) generateError), counter2)
translateLetDecls counter ((E.ValDef pat rhs):letDecls) typeSigs cont =
  let (translateLetDeclsRes, counter1) = translateLetDecls counter letDecls typeSigs cont
      (counter2, var) = nextFreshVar counter1
      (compileEquationsRes, counter3) = compileEquations counter2 [var] [([removeAsPat pat], foldr (\(var, exp) acc -> L.App (L.Abs var (T.Int B.nullSpan) acc) exp) translateLetDeclsRes (getAsPatBindings pat))] generateError
      (translateRhsRes, counter4) = translateRHS counter3 rhs in
  (L.App (L.Abs var (T.Int B.nullSpan) (L.App (L.App (L.Var $ generatePrimitiveVar "fatbar__") compileEquationsRes) generateError)) translateRhsRes, counter3)
translateLetDecls counter ((E.FnDef var patRhss):letDecls) typeSigs cont =
  let (translateLetDeclsRes, counter1) = translateLetDecls counter letDecls typeSigs cont
      (eqs, counter2) = bar counter1 patRhss
      argsNum = length $ (fst . head) eqs
      (counter3, vars) = nextFreshVars counter2 argsNum
      (compileEquationsRes, _) = compileEquations counter3 vars (handleAsPatInEqs eqs) generateError
      (generateArgsRes, counter5) = generateArgs counter2 argsNum (L.App (L.App (L.Var $ generatePrimitiveVar "fatbar__") compileEquationsRes) generateError) in
  (L.App (L.Abs var (T.Int B.nullSpan) translateLetDeclsRes) (L.App generateFixPoint (L.Abs var (T.Int B.nullSpan) generateArgsRes)), counter5)
-- TODO: remover ctx das assinaturas
translateLetDecls counter ((E.Mutual mutualLetDecls):letDecls) typeSigs cont = undefined
translateLetDecls counter ((E.TypeSig vars ty):letDecls) typeSigs cont = translateLetDecls counter letDecls [] cont

-- TODO: generate TAbs, for now TAbs is an Abs with a varPat
generateArgs :: Int -> Int -> L.Exp -> (L.Exp, Int)
generateArgs n 0 cont = (cont, n)
generateArgs n size cont =
  let (counter, var) = nextFreshVar n
      (generateArgsRes, counter1) = generateArgs counter (size-1) cont in
  (L.Abs var (T.Int B.nullSpan) generateArgsRes, counter1)

-- Removes AsPats transforming the expression in the equation
handleAsPatInEqs :: [Equation] -> [Equation]
handleAsPatInEqs = map (\(pats, exp) ->
  let newPats = map removeAsPat pats
      patsBindings = concatMap getAsPatBindings pats in
  (newPats, foldr (\(var, bindingExp) acc -> L.App (L.Abs var (T.Int B.nullSpan) acc) bindingExp) exp patsBindings))

removeAsPat :: E.Pat -> E.Pat
removeAsPat (E.DConsPat span iden pats) = E.DConsPat span iden (map removeAsPat pats) 
removeAsPat (E.ChoicePat span iden pat) = (E.ChoicePat span iden (removeAsPat pat))
removeAsPat (E.AsPat _ _ pat) = removeAsPat pat
removeAsPat pat = pat

getAsPatBindings :: E.Pat -> [(B.Variable, L.Exp)]
getAsPatBindings (E.DConsPat _ __ pats) = concat $ map getAsPatBindings pats
getAsPatBindings (E.ChoicePat _ _ pat) = getAsPatBindings pat
getAsPatBindings (E.AsPat _ var pat) = (var, patToLExp pat) : (getAsPatBindings pat)
getAsPatBindings _ = []

translateRHS :: Int -> E.RHS -> (L.Exp, Int)
translateRHS counter (E.UnguardedRHS exp (Just letDecls)) =
  let (cont, counter1) = translateExp counter exp in translateLetDecls counter letDecls [] cont
translateRHS counter (E.UnguardedRHS exp Nothing) = translateExp counter exp
translateRHS counter (E.GuardedRHS guards (Just letDecls)) =
  let (cont, counter1) =
        foldr (\(cond, exp) (accExp, accCounter) ->
        let (cond1, counter1) = translateExp accCounter cond
            (exp1, counter2) = translateExp counter1 exp
        in (generateLeastIf cond1 exp1 accExp, counter2)) (generateFail, counter) guards
  in translateLetDecls counter1 letDecls [] cont
translateRHS counter (E.GuardedRHS guards Nothing) = foldr (\(cond, exp) (accExp, accCounter) ->
  let (cond1, counter1) = translateExp accCounter cond
      (exp1, counter2) = translateExp counter1 exp
  in (generateLeastIf cond1 exp1 accExp, counter2)) (generateFail, counter) guards

translateExp :: Int -> E.Exp -> (L.Exp, Int)
translateExp counter (E.Int _ int) = (L.Lit (L.LInt int), counter)
translateExp counter (E.Float _ float) = (L.Lit (L.LFloat float), counter)
translateExp counter (E.Char _ char) = (L.Lit (L.LChar char), counter)
translateExp counter (E.DCons _ iden) = (L.Con iden, counter)
translateExp counter (E.Var _ var) = (L.Var var, counter)
translateExp counter (E.App _ exp args) =
  foldl (\(accExp, accCounter) arg -> case arg of
    B.ExpLevel exp -> let (exp3, counter) = translateExp accCounter exp in (L.App accExp exp3, counter)
    B.TypeLevel ty -> (L.TApp accExp (L.Type ty), accCounter)) (translateExp counter exp) args
translateExp counter (E.Abs _ levels _ exp) = foldr (\abs (accExp, accCounter) -> case abs of
  B.ExpLevel (pat, ty) ->
    let (counter1, var) = nextFreshVar accCounter
        (compileEquationsRes, counter2) = compileEquations counter1 [var] [([removeAsPat pat], foldr (\(var, exp) acc -> L.App (L.Abs var (T.Int B.nullSpan) acc) exp) accExp (getAsPatBindings pat))] generateError in
    ((L.Abs var (T.Int B.nullSpan) compileEquationsRes), counter2)
-- TODO: give the correct type
  B.TypeLevel (var, kind) -> (translatePat (E.VarPat B.nullSpan var, T.Int B.nullSpan) accExp,  accCounter)) (translateExp counter exp) levels
translateExp counter (E.Let _ letDecls exp) =
  let (exp2, counter1) = translateExp counter exp in translateLetDecls counter1 letDecls [] exp2
translateExp counter (E.If _ cond t f) =
  let (condExp, counter1) = translateExp counter cond
      (tExp, counter2) = translateExp counter1 t
      (fExp, counter3) = translateExp counter2 f in
  (generateLeastIf condExp tExp fExp, counter3)
translateExp counter (E.Case _ exp patRhss) =
  let (caseExp, counter1) = translateExp counter exp
      (counter2, var) = nextFreshVar counter1
      (rhss, counter3) = mapWithCounter counter2 (\counter (pat, rhs) -> let (rhsExp, counter1) = translateRHS counter rhs in (([removeAsPat pat], foldr (\(var, exp) acc -> L.App (L.Abs var (T.Int B.nullSpan) acc) exp) rhsExp (getAsPatBindings pat)), counter1)) patRhss
      (compiledEquationsExp, counter4) = compileEquations counter3 [var] rhss generateError in
  (L.App (L.Abs var (T.Int B.nullSpan) compiledEquationsExp) caseExp, counter4)
translateExp counter (E.Channel _ _) = (L.App (L.Var $ generatePrimitiveVar "chan") generateUnit, counter)
translateExp counter (E.Select _ (B.Identifier _ iden)) =
  ((L.TApp (L.TApp (L.TApp (L.Var $ generatePrimitiveVar "send") generateUnit) generateUnit) (lstString iden)) , counter)

mapWithCounter :: Int -> (Int -> a -> (b, Int)) -> [a] -> ([b], Int)
mapWithCounter n _ [] = ([], n)
mapWithCounter n f (x:xs) =
  let (xs', counter1) = mapWithCounter n f xs
      (x', counter2) = f counter1 x in
  (x':xs', counter2)

generateLeastIf :: L.Exp -> L.Exp -> L.Exp -> L.Exp
-- generateLeastIf cond t f = L.Case cond [(L.ACon (B.Identifier B.nullSpan "True") [], t), (L.ACon (B.Identifier B.nullSpan "False") [], f)]
generateLeastIf cond t f = L.App (L.App (L.App (L.Var $ generatePrimitiveVar "if__") cond) t) f

generatePrimitiveVar :: String -> B.Variable
generatePrimitiveVar name = B.Variable {B.internal=(-1), B.external=name, B.varSpan=B.Span{B.filepath="", B.startPos=(0,0), B.endPos=(0,0)}}

generateFail :: L.Exp
generateFail = L.Con (B.Identifier B.nullSpan "Fail__")

generateUnit :: L.Exp
generateUnit = L.Con (B.Identifier B.nullSpan "()")

lstString :: String -> L.Exp
lstString = foldr (\char acc ->
  L.App (L.App (L.Con $ B.Identifier B.nullSpan "::") (L.Lit $ L.LChar char)) acc) (L.TApp (L.Con $ B.Identifier B.nullSpan "[]") (L.Type $ T.Char B.nullSpan))

-- TODO: am i using this?
-- Transforms a pattern in the "equivalent" least expression
-- used for compiling Choice patterns and as-patterns
patToLExp :: E.Pat -> L.Exp
patToLExp (E.IntPat _ n) = L.Lit $ L.LInt n
patToLExp (E.FloatPat _ n) = L.Lit $ L.LFloat n
patToLExp (E.CharPat _ c) = L.Lit $ L.LChar c
patToLExp (E.WildPat _ _) = L.Var $ generatePrimitiveVar "wild__"
patToLExp (E.VarPat _ var) = L.Var var
patToLExp (E.DConsPat _ iden pats) = foldl (\acc pat -> L.App acc (patToLExp pat)) (L.Con iden) pats
patToLExp (E.ChoicePat _ iden (E.VarPat _ var)) = L.Var var
-- TODO: can treat asPat as varPat??
patToLExp (E.AsPat _ _ pat) = patToLExp pat

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

nextFreshVar :: Int -> (Int, B.Variable)
nextFreshVar n = (n+1, generatePrimitiveVar $ "var"++show n++"__")

nextFreshVars :: Int -> Int -> (Int, [B.Variable])
nextFreshVars n size = (n+size, [generatePrimitiveVar $ "var"++show n++"__" | n <- [n..n+size-1]])

type Equation = ([E.Pat], L.Exp)

compileEquations :: Int -> [B.Variable] -> [Equation] -> L.Exp -> (L.Exp, Int)
-- TODO: empty rule is not correct, maybe?
-- compileEquations _ [] eqs def = let (hd:tl) = [e |(_,e) <- eqs] in 
--   L.App (L.App (L.Var $ generatePrimitiveVar "fatbar__") (foldl (\acc exp -> L.App (L.App (L.Var $ generatePrimitiveVar "fatbar__") acc) exp) hd tl)) def
compileEquations counter [] [] def = (def, counter)
compileEquations counter [] [(_, exp)] _ = (exp, counter)
compileEquations counter [] eqs _ = (foldr (\(_, exp) acc-> L.App (L.App (L.Var $ generatePrimitiveVar "fatbar__") exp) acc) (snd . last $ eqs) (init eqs), counter)
compileEquations counter vars eqs def | allVars eqs =
                                        compileEquations counter (tail vars) (updateHeadPattern (replaceVar (head vars) eqs)) def
                                      | allCons eqs && firstEqIsChoicePat eqs =
                                        let (counter1, freshVars) = nextFreshVars counter 2
                                            (fooRes, counter2) = foo counter1 (tail freshVars ++ tail vars ) (groupEqs eqs) def
                                        in (L.Case (generateReceive generateUnit generateUnit (L.Var $ head vars)) [(L.ACon (B.Identifier B.nullSpan "(,)") freshVars, (L.Case (L.Var (head freshVars)) fooRes))], counter2)
                                      | allCons eqs = let (fooRes, counter1) = foo counter (tail vars) (groupEqs eqs) def in (L.Case (L.Var (head vars)) fooRes, counter1)
                                      | otherwise = foldr (\groupedEqs (accExp, accCounter) -> compileEquations accCounter vars groupedEqs accExp) (def, counter) (reverse $ mixtureGroup eqs)

allVars :: [Equation] -> Bool
allVars [] = True 
allVars (eq:eqs) = case (head . fst) eq of
  E.VarPat _ _ -> allVars eqs
  E.WildPat _ _ -> allVars eqs
  _ -> False

allCons :: [Equation] -> Bool
allCons [] = True
allCons (eq:eqs) = case (head . fst) eq of
  E.DConsPat _ _ _ -> allCons eqs
  E.IntPat _ _ -> allCons eqs
  E.FloatPat _ _ -> allCons eqs
  E.CharPat _ _ -> allCons eqs
  E.ChoicePat _ _ _ -> allCons eqs
  _ -> False

firstEqIsChoicePat :: [Equation] -> Bool
firstEqIsChoicePat ((((E.ChoicePat _ _ _):_), _):_) = True
firstEqIsChoicePat _ = False

generateReceive :: L.Exp -> L.Exp -> L.Exp -> L.Exp
generateReceive arg1 arg2 arg3 = L.App (L.TApp (L.TApp (L.Var $ generatePrimitiveVar "receive") arg1) arg2) arg3

replaceVar :: B.Variable -> [Equation] -> [Equation]
replaceVar var eqs = map (\(pats, exp) -> case pats of
  ((E.VarPat _ patVar):_) -> (pats, subs patVar var exp)
  ((E.WildPat _ _):_) -> (pats, exp)
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
altSub target var (pat, exp) = (pat, subs target var exp)

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
foo :: Int -> [B.Variable] -> [[Equation]] -> L.Exp -> ([(L.Alt, L.Exp)], Int)
-- def makes sense here?
foo counter vars [] def = ([(L.AWildCard, def)], counter)
-- foo counter vars (eqs:eqss) def =
--   let E.DConsPat _ iden pats = (head . fst . head) eqs
--       freshVars = (newKVars counter (length pats))
--   in (L.ACon iden freshVars, compileEquations (counter+length freshVars) (freshVars++vars) (updateHeadPattern eqs) def):(foo counter vars eqss def)
foo counter vars (eqs:eqss) def = 
  case (head . fst . head) eqs of
    E.DConsPat _ iden pats ->
      let (counter1, nextVars) = nextFreshVars counter (length pats)
          (compileEquationsRes, counter2) = compileEquations counter1 (nextVars++vars) (updateHeadPattern eqs) def 
          (fooRes, counter3) = foo counter2 vars eqss def in
      ((L.ACon iden nextVars, compileEquationsRes):fooRes, counter3)
    E.IntPat _ n ->
      let (compileEquationsRes, counter1) = compileEquations counter vars (updateHeadPattern eqs) def
          (fooRes, counter2) = foo counter1 vars eqss def in
      ((L.ALit $ L.LInt n, compileEquationsRes):fooRes, counter2)
    E.FloatPat _ n ->
      let (compileEquationsRes, counter1) = compileEquations counter vars (updateHeadPattern eqs) def
          (fooRes, counter2) = foo counter1 vars eqss def in
      ((L.ALit $ L.LFloat n, compileEquationsRes):fooRes, counter2)
    E.CharPat _ n ->
      let (compileEquationsRes, counter1) = compileEquations counter vars (updateHeadPattern eqs) def
          (fooRes, counter2) = foo counter1 vars eqss def in
      ((L.ALit $ L.LChar n, compileEquationsRes):fooRes, counter2)
    E.ChoicePat _ label (E.VarPat _ var) ->
      let (compileEquationsRes, counter1) = compileEquations counter vars (updateHeadPattern eqs) def 
          (fooRes, counter2) = foo counter1 vars eqss def in
      ((L.ACon label [], compileEquationsRes):fooRes, counter2)
    E.ChoicePat _ label (E.WildPat _ var) ->
      let (compileEquationsRes, counter1) = compileEquations counter vars (updateHeadPattern eqs) def 
          (fooRes, counter2) = foo counter1 vars eqss def in
      ((L.ACon label [], compileEquationsRes):fooRes, counter2)
    E.ChoicePat _ _ _ -> undefined

-- TODO: remove this function
newKVars :: Int -> Int -> [B.Variable]
newKVars from size = [generatePrimitiveVar ("arg"++(show n)++"__") | n <- [from..from+size]]

updateHeadPattern :: [Equation] -> [Equation]
updateHeadPattern eqs = map (\(pats, exp) -> (updateHeadPattern' pats, exp)) eqs

updateHeadPattern' :: [E.Pat] -> [E.Pat]
updateHeadPattern' ((E.DConsPat _ _ []):pats) = pats 
updateHeadPattern' ((E.DConsPat _ _ innerPats):pats) = innerPats++pats 
updateHeadPattern' ((E.ChoicePat _ _ varPat@(E.VarPat _ _)):pats) = varPat:pats 
updateHeadPattern' ((E.ChoicePat _ _ varPat@(E.WildPat _ _)):pats) = varPat:pats 
updateHeadPattern' ((E.ChoicePat _ _ pat):pats) = undefined 
updateHeadPattern' (pat:pats) = pats

-- TODO: rename this for function for something better
bar :: Int -> [([B.Level E.Pat B.Variable], E.RHS)] -> ([([E.Pat], L.Exp)], Int)
bar counter patRHS =
  mapWithCounter counter (\counter (levels, rhs) ->
    let (translateRHSRes, counter1) = translateRHS counter rhs in
    (((map (\level -> case level of
      B.ExpLevel pat -> pat
      B.TypeLevel var -> E.VarPat B.nullSpan var) levels), translateRHSRes), counter1)) patRHS

generateError :: L.Exp
generateError = L.Var $ generatePrimitiveVar "error__"

removeBuiltins :: M.Module -> M.Module
removeBuiltins m = m{M.definitions = filter notBuiltin (M.definitions m)}
  where notBuiltin = \case
          (E.ValDef (E.VarPat _ x) _) ->
            case lookup (B.external x) builtins of
              Nothing -> True
              Just _  -> False
          (E.FnDef x _) ->
            case lookup (B.external x) builtins of
              Nothing -> True
              Just _  -> False
          _ -> True
  