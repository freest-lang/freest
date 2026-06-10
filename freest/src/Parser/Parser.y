{
{- |
Module      :  Parser.Parser
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements a layout-sensitive parser for FreeST.
If further includes support for parsing FreeSTi commands and test cases.
-}
module Parser.Parser
  ( runParseModule
  -- freesti
  , parseExp
  , parseDeclList
  , parseItDecl
  , parseType
  , parseTwoTypes
  , parseTypes
  , parseLowerId
  , parseUpperId
  -- testing
  , parseEquivalenceTests
  , parseKindingTests
  ) where

import Parser.Lexer ( scan )
import Parser.Token
import Parser.LexerUtils
import Parser.ParserUtils
import Syntax.Base 
import Syntax.Names
import Syntax.Expression qualified as E 
import Syntax.Kind qualified as K 
import Syntax.Type.Unkinded qualified as T 
import Syntax.Module qualified as M
import UI.Error

import Control.Monad.Except
import Data.Bifunctor
import Data.Function ( on )
import Data.List ( sortBy )

}

-- Parser entry points for FreeST modules
%name parseModule Module
-- Parser entry points for FreeSTi commands
%name parseDeclList DeclList
%name parseItDecl ItDecl
%name parseType Type
%name parseExp Exp
%name parseTwoTypes TwoTypes
%name parseTypes TypePrimaryListWS
%name parseLowerId LowerId
%name parseUpperId UpperId
-- Parser entry points for test cases
%name parseEquivalenceTests EquivalenceTestCases
%name parseKindingTests KindingTestCases

%tokentype { Token }
%monad { Lexer }
%lexer { lexer } { TkEOF _ }

%errorhandlertype explist
%error { parseError }

%token
  -- Layout
  OPEN    { TkVOpen _ }
  PIPE    { TkVPipe _ }
  CLOSE   { TkVClose _ }
  -- Keywords
  'module' { TkModule _ }
  'where'  { TkWhere _ }
  'import' { TkImport _ }
  'data'   { TkData _ }
  'type'   { TkType _ }
  'let'    { TkLet _ }
  'in'     { TkIn _ }
  'mutual' { TkMutual _ }
  'case'   { TkCase _ }
  'of'     { TkOf _ }
  'channel'{ TkChannel _ }
  'select' {TkSelect _ }
  'sendType'    { TkSendType _ }
  'receiveType' { TkReceiveType _ }
  'if'     { TkIf _ }
  'then'   { TkThen _ }
  'else'   { TkElse _ }
  'forall' { TkForall _ }
  'exists' { TkExists _ }
  -- Punctuation
  '.'     { TkDot _ }
  '='     { TkEqual _ }
  '{'     { TkOpen _ }
  '}'     { TkClose _ }
  '('     { TkLParen _ }
  ')'     { TkRParen _ }
  '['     { TkLSquare _ }
  ']'     { TkRSquare _ }
  '\\'    { TkBackslash _ }
  '->'    { TkArrow _ }
  -- Operators
  '|'     { TkPipe _ }
  ':'     { TkColon _ }
  '::'    { TkColonColon _ }
  ';'     { TkSemi _ }
  '@'     { TkAt _ }
  '#'     { TkHash _}
  ','     { TkComma _ }
  '$'     { TkDollar _ }
  '|>'    { TkPipeGT _ }
  '||'    { TkPipePipe _ }
  '&&'    { TkAmpAmp _ }
  '+'     { TkPlus _ }
  '++'    { TkPlusPlus _ }
  '+.'    { TkPlusDot _ }
  '-'     { TkMinus _ }
  '-.'    { TkMinusDot _ }
  '*'     { TkStar _ }
  '**'    { TkStarStar _ }
  '*.'    { TkStarDot _ }
  '/'     { TkSlash _ }
  '/.'    { TkSlashDot _ }
  '^'     { TkCaret _ }
  '^^'    { TkCaretCaret _ }
  CMP     { TkCmp _ _ }
  -- Types
  'Int'   { TkIntType _ }
  'Float' { TkFloatType _ }
  'Char'  { TkCharType _ }
  'Skip'  { TkSkipType _ }
  'Close' { TkCloseType _ }
  'Wait'  { TkWaitType _ }
  'Dual'  { TkDualType _ }
  'Void'  { TkVoidType _ }
  '?'     { TkQuestion _ }
  '!'     { TkBang _ }
  '&'     { TkAmp _ }

  -- Expression literals
  INT_LIT { TkIntLit _ _ }
  FLOAT_LIT { TkFloatLit _ _ }
  CHAR_LIT { TkCharLit _ _ }
  STRING_LIT {TkStringLit _ _ }

  -- Identifiers
  UPPER_ID { TkUpperId _ _ }  
  QUALIFIED_UPPER_ID { TkQualifiedUpperId _ _ }
  WILDCARD { TkWildcard _ _ }
  LOWER_ID { TkLowerId _ _ }
  LOWER_ID_AT { TkLowerIdAt _ _ }

%nonassoc LAMBDA    
%right    ':'
%right    'in' 'else' 'case'
%right    '.'
%right    '->' ARROW
%right    ';' SEMI
%left     '@'
%right    '$'
%left     '|>'
%left     '||'
%left     '&&'
%nonassoc CMP
%right    '::' '++' '^^'
%left     '+' '-' '+.' '-.'
%left     '*' '/' '*.' '/.'
%right    '^' '**'
%left     NEG not
%right    MSG

%%

Module :: { M.ParsedModule }
  : 'module' ModuleName 'where' ImportModuleDeclBlock { M.setName (split '.' $ getText $2) $4 }
  -- TODO: no module declaration. See notes in Lexer.
  -- | ImportModuleDeclBlock { $1 }

ModuleName :: { Token } : UPPER_ID { $1 } | QUALIFIED_UPPER_ID { $1 }

ImportModuleDeclBlock :: { M.ParsedModule }
  : OPEN ImportModuleDeclListPIPE Close { $2 }

ImportModuleDeclListPIPE :: { M.ParsedModule }
  : ImportDecl PIPE ImportModuleDeclListPIPE { $1 $3 }
  | ModuleDecl PIPE ModuleDeclListPIPE       { $1 $3 }
  | ImportDecl { $1 M.emptyParsedModule }
  | ModuleDecl { $1 M.emptyParsedModule }
  | {- empty -} { M.emptyParsedModule }

ImportDecl :: { M.ParsedModule -> M.ParsedModule }
  : 'import' QUALIFIED_UPPER_ID { M.insertImport (split '.' $ getText $2) }
  | 'import' UPPER_ID           { M.insertImport [getText $2] }

ModuleDeclListPIPE :: { M.ParsedModule }
  : ModuleDecl PIPE ModuleDeclListPIPE { $1 $3 }
  | ModuleDecl                         { $1 M.emptyParsedModule }
  | {- empty -}                        { M.emptyParsedModule }

ModuleDecl :: { M.ParsedModule -> M.ParsedModule }
  : LetDecl  { M.insertDef $1 }
  | DataDecl { $1 }
  | TypeDecl { $1 }
  | KindSig  { $1 }

DataDecl :: { M.ParsedModule -> M.ParsedModule }
  : 'data' UPPER_ID KindedVarListWS '=' DataConsListPipe { M.insertDataDecl (mkIdTk $2) $3 $5 }

TypeDecl :: { M.ParsedModule -> M.ParsedModule }
  : 'type' UPPER_ID KindedVarListWS '=' Type             { M.insertTypeDecl (mkIdTk $2) $3 $5 }

KindSig :: { M.ParsedModule -> M.ParsedModule }
  : 'type' UpperIdListComma ':' Kind { M.insertKindSig $2 $4  }

LetDecl :: { E.ParsedLetDecl }
  : PatDecl { $1 }
  | FnDef { $1 }
  | TypeSig { $1 }
  | 'mutual' OPEN MutualDecls Close { E.Mutual $3 }

PatDecl :: { E.ParsedLetDecl }
  : Pat RHS('=') { E.ValDef $1 $2 }

MutualDecls :: { [E.ParsedLetDecl] }
  : MutualDecl                  { [$1]    }
  | MutualDecl PIPE MutualDecls { $1 : $3 }

MutualDecl :: { E.ParsedLetDecl }
  : FnDef { $1 }
  | TypeSig { $1 }

TypeSig :: { E.ParsedLetDecl }
  : ExpVarListComma ':' Type { E.TypeSig $1 $3 }

FnDef :: { E.ParsedLetDecl }
  : ExpVar FnDefParams RHS('=') { E.FnDef $1 [($2, $3)] }
  | PatPrimary OpOrMinus FnDefParams RHS('=') { E.FnDef $2 [(ExpLevel $1 : $3, $4)] }

ExpVar :: { Variable }
  : LOWER_ID   { mkVarTk $1 }
  | '(' OpOrMinus ')' { $2 }

TypeVar :: { Variable }
  : LOWER_ID { mkVarTk $1 }

MultVar :: { Variable }
  : LOWER_ID { mkVarTk $1 }

TypeVarNEListWS :: { [Variable] }
  : TypeVar { [$1] }
  | TypeVar TypeVarNEListWS { $1 : $2 }

RHS(sep) :: { E.ParsedRHS }
  : sep Exp Where          { E.UnguardedRHS $2 $3 }
  | GuardedExps(sep) Where { E.GuardedRHS $1 $2   }

GuardedExps(sep) :: { [(E.ParsedExp, E.ParsedExp)] }
  : '|' Exp sep Exp GuardedExps(sep) { ($2,$4) : $5 }
  | '|' Exp sep Exp                  { [($2,$4)]    }
  -- otherwise is simply a variable defined as True

Where :: { Maybe [E.ParsedLetDecl] }
  : 'where' LetDeclBlock { Just $2 }
  | {- empty -}          { Nothing }

ExpVarListComma :: { [Variable] }
  : ExpVar ',' ExpVarListComma { $1 : $3 }
  | ExpVar                     { [$1] }

UpperIdListComma :: { [Identifier] }
  : UPPER_ID ',' UpperIdListComma { mkIdTk $1 : $3 }
  | UPPER_ID                      { [mkIdTk $1] }

DataConsListPipe :: { [(Identifier, [T.ParsedType])] }
  : DataCons '|' DataConsListPipe { $1 : $3 }
  | DataCons                      { [$1]    }

DataCons :: { (Identifier, [T.ParsedType]) }
  : UPPER_ID TypePrimaryListWS { (mkIdTk $1, $2) }

TypePrimaryListWS :: { [T.ParsedType] }
  : TypePrimary TypePrimaryListWS { $1 : $2 }
  | {- empty -}                   { []      }

KindPrimary :: { K.Kind }
  : ProperKind   { $1 }
  | '(' Kind ')' { $2 }

Kind :: { K.Kind }
  : Kind '->' Kind %prec ARROW { K.Arrow (spanFromTo $1 $3) $1 $3 }
  | KindPrimary                { $1 }

ProperKind :: { K.Kind }
  : MultiplicityPrimary Prekind { K.Proper (spanFromTo $1 (fst $2)) $1 (snd $2) }

Prekind :: { (Span, K.Prekind) }
  : UPPER_ID {% fmap (getSpan $1,) 
    case getText $1 of { "T" -> pure K.Top
                       ; "S" -> pure K.Session
                       ; "C" -> pure K.Channel
                       ; s -> invalidPrekindError s $1}}

TypePrimary :: { T.ParsedType }
  -- Builtins (necessary?)
  : 'Int'    { T.Int   (getSpan $1)       }
  | 'Float'  { T.Float (getSpan $1)       }
  | 'Char'   { T.Char  (getSpan $1)       }
  | 'Skip'   { T.Skip  (getSpan $1)       }
  | 'Close'  { T.End   (getSpan $1) T.Out }
  | 'Wait'   { T.End   (getSpan $1) T.In  }
  | 'Void' '@' Kind { T.Void (spanFromTo $1 $3) $3 }
  -- Unit, Tuples, Operators
  | '(' ')'        { T.Tuple (spanFromTo $1 $2) [] } -- { T.DName (spanFromTo $1 $2) (mkUnitId (spanFromTo $1 $2)) }
  | '(' Type ',' TypeListComma ')' { T.Tuple (spanFromTo $1 $5) ($2 : $4) }
  | '(' Commas ')' {% prefixTupleTypeConsError $1 $3 }
                -- { T.DName (spanFromTo $1 $3) (mkTupleId $2 (spanFromTo $1 $3)) }
  | '(' MultArrow ')'  { T.Arrow (spanFromTo $1 $3) (snd $2) }
  | '(' Type MultArrow ')' { T.App (spanFromTo $1 $4) (uncurry T.Arrow $3) [$2] }
  | '(' MultArrow Type ')' { let {s = spanFromTo $1 $4; a = mkDefaultVar "_a" s} 
                         in T.Abs s [(a, K.lt s)] (T.App s (uncurry T.Arrow $2) [T.Var s a, $3]) }
  | '(' Polarity ')'     {let {s = spanFromTo $1 $3} in T.Message s (K.Lin s) (snd $2)}
  | '(' '*' Polarity ')' {let {s = spanFromTo $1 $4} in T.Message s (K.Un  s) (snd $3)}
  -- | '(' Type ';' ')' -- TODO: sections
  -- | '(' ';' Type ')' -- TODO: sections
  -- Messages
  | Polarity TypePrimary %prec MSG     { let {s = spanFromTo (fst $1) $2} in T.AppMessage s (K.Lin s) (snd $1) $2 }
  | '*' Polarity TypePrimary %prec MSG { let {s = spanFromTo $1       $3} in T.AppMessage s (K.Un  s) (snd $2) $3 }
  -- Choices
  | View '{' LabelTypeListComma '}'     { T.AppLinChoice (spanFromTo (fst $1) $4) (snd $1) $3 } -- sorted by AppLinChoice
  | '*' View '{' LabelListComma '}'     { T.UnChoice (spanFromTo $1 $5) (snd $2) $4 }       -- sorted by UnChoice
  -- Variables and constructors
  | UPPER_ID { T.TName (getSpan $1) (mkIdTk $1) }
  | TypeVar { T.Var (getSpan $1) $1 }
  -- Lists
  | '[' ']' {% prefixListTypeConsError $1 $2 }
         -- { T.DName (spanFromTo $1 $2) (mkListId (spanFromTo $1 $2)) } -- TODO: multiplicities
  | '[' Type ']' { T.AppDName (spanFromTo $1 $3) (mkNilId (spanFromTo $1 $3)) [$2] }
  -- Parenthesized type
  | '(' Type ')' { setSpan (spanFromTo $1 $3) $2 }

Type :: { T.ParsedType }
  : Type MultArrow Type %prec ARROW { T.AppArrow (fst $2) (snd $2) $1 $3 }
  | TypeNotArrow { $1 }

TypeNotArrow
  : 'forall' MultOrKindedVars MultArrow Type %prec ARROW
    { foldr (\cases { (Left φs  ) t -> T.ForallM   (spanFromTo (head φs)        t) (snd $3) φs  t 
                    ; (Right aks) t -> T.AppForall (spanFromTo (fst $ head aks) t) (snd $3) aks t
                    })
            $4 $2
                                                             }
  | '(' 'exists' KindedVars ',' Type ')' { T.AppExists (spanFromTo $1 $6) $3 $5 }
  | Polarity 'type' KindedVar '.' Type %prec SEMI { let (a, k) = $3 in T.AppQuantS (spanFromTo (fst $1) $5) (snd $1) a k $5 }
  | '\\' KindedVars '->' Type   %prec  ARROW { T.Abs (spanFromTo $1 $4) $2 $4 }
  | TypeApp ';' TypeNotArrow { T.AppSemi (spanFromTo $1 $3) $1 $3 }
  | TypeApp %prec SEMI { $1 }

TypeApp :: { T.ParsedType }
  : TypeApp TypePrimary { addArgType $2 $1 }
  | 'Dual' TypePrimary  { T.AppDual (spanFromTo $1 $2) $2 }
  | TypePrimary { $1 }

MultArrow :: { (Span, K.Multiplicity) }
  : '->' { (getSpan $1, K.Un $ getSpan $1) }
  | '-' Multiplicity '->' { (spanFromTo $1 $3, $2) }

Multiplicity :: { K.Multiplicity }
  : MultiplicityPrimary { $1 }
  | Multiplicity '+' Multiplicity 
    { let s = (spanFromTo $1 $3) in
      case ($1, $3) of {(K.Lin{}, _) -> K.Lin s
                       ;(_, K.Lin{}) -> K.Lin s
                       ;(K.Sup _ lvφs1, K.Sup _ lvφs2) -> K.Sup s (lvφs1 ++ lvφs2)}}

MultiplicityPrimary :: { K.Multiplicity }
  : '*' { (K.Un $ getSpan $1) }
  | INT_LIT {% let i = read (getText $1) in if i == 1 then pure (K.Lin $ getSpan $1) else invalidMultiplicityError i $1 }
  | MultVar { K.VarM (getSpan $1) ObjLv $1 }
  | '(' Multiplicity ')' { $2 }

MultOrKindedVars :: { [Either [Variable] [(Variable, K.Kind)]] }
  : '#' MultVar MultOrKindedVars { case $3 of { (Left  φs  : φaks) -> Left  ($2 : φs ) : φaks
                                              ; φaks -> Left  [$2] : φaks
                                              }}
  | KindedVar   MultOrKindedVars { case $2 of { (Right aks : φaks) -> Right ($1 : aks) : φaks
                                              ; φaks -> Right [$1] : φaks
                                              }}
  | '#' MultVar { [Left  [$2]] }
  | KindedVar   { [Right [$1]] }


TypeListComma :: { [T.ParsedType] }
  : Type ',' TypeListComma { $1 : $3 }
  | Type                   { [$1] }

AtTypeList :: { [T.ParsedType] }
  : '@' TypePrimary            { [$2] }
  | '@' TypePrimary AtTypeList { $2 : $3 }

Quant :: { (Span, T.Polarity) }
  : 'forall' { (getSpan $1, T.In ) }
  | 'exists' { (getSpan $1, T.Out) }

Commas :: { Int }
  : ',' { 1 }
  | ',' Commas { succ $2 }

Polarity :: { (Span, T.Polarity) }
  : '!'  { (getSpan $1, T.Out) }
  | '?'  { (getSpan $1, T.In) }

Polarity2 :: { (Span, T.Polarity) }
  : '!' '!' {(spanFromTo $1 $2, T.Out) }
  | '?' '?' {(spanFromTo $1 $2, T.In ) }

View :: { (Span, T.Polarity) }
  : '+' { (getSpan $1, T.Out) }
  | '&' { (getSpan $1, T.In) }

LabelTypeListComma :: { [(Identifier, T.ParsedType)] }
  : UPPER_ID ':' Type ',' LabelTypeListComma { (mkIdTk $1, $3) : $5 }
  | UPPER_ID ':' Type { [(mkIdTk $1, $3)] }

LabelListComma :: { [Identifier] }
  : UPPER_ID ',' LabelListComma { mkIdTk $1 : $3 }
  | UPPER_ID                    { [mkIdTk $1] }

KindedVarListWS :: { [(Variable, K.Kind)] }
  : {- empty -} { [] }
  | KindedVar KindedVarListWS { $1 : $2 }

KindedVars :: { [(Variable, K.Kind)] }
  : TypeVar KindedVars { ($1, dummyKindVar $1) : $2 }
  | '(' TypeVarNEListWS ':' Kind ')' KindedVars { map (, $4) $2 ++ $6 }
  | TypeVar { [($1, dummyKindVar $1)] }
  | '(' TypeVarNEListWS ':' Kind ')' { map (, $4) $2 }

KindedVar :: { (Variable, K.Kind) }
  : TypeVar { ($1, dummyKindVar $1) }
  | '(' TypeVar ':' Kind ')' { ($2, $4) }

ExpPrimary :: { E.ParsedExp }
  : INT_LIT     { E.Int    (getSpan $1) (read $ getText $1) }
  | FLOAT_LIT   { E.Float  (getSpan $1) (read $ getText $1) }
  | CHAR_LIT    { E.Char   (getSpan $1) (read $ getText $1) }
  | STRING_LIT  { E.listExp (getSpan $1) (T.Char (getSpan $1)) (map (E.Char (getSpan $1)) (getText $1)) }
  | ExpVar      { E.Var    (getSpan $1) $1 }
  | UPPER_ID    { E.DCons  (getSpan $1) (mkIdTk $1) }
  | 'receiveType' { E.ReceiveType (getSpan $1) }
  | '(' ')'     { E.Tuple (spanFromTo $1 $2) [] } -- {let s = spanFromTo $1 $2 in E.DCons s (mkTupleId 0 s)}
  | '(' Commas ')' {% prefixTupleExpConsError $1 $3 } 
                -- { let s = spanFromTo $1 $3 in E.DCons s (mkTupleId $2 s) } -- TODO: multiplicities
  | '(' AtTypeList ',' Exp ')' { E.Pack (spanFromTo $1 $5) $2 $4 }
  | '(' Exp ',' ExpListComma ')' { E.Tuple (spanFromTo $1 $5) ($2 : $4) }
  -- | TupleSection { ... } -- TODO: tuple sections
  | '(' Exp ')' { setSpan  (spanFromTo $1 $3) $2 }
  | '(' Op ')'  { E.Var (spanFromTo $1 $3) (setSpan (spanFromTo $1 $3) $2) }
  | '(' '::' ')' {% prefixListConsError $1 $3 }
  | '(' ConsOp ')' { E.DCons (spanFromTo $1 $3) (setSpan (spanFromTo $1 $3) $2) }
  | '(' '-' ')' { E.Var (spanFromTo $1 $3) (mkMinusVar (spanFromTo $1 $3))}
  | '(' '-.' ')' { E.Var (spanFromTo $1 $3) (mkMinusDotVar (spanFromTo $1 $3))}
  -- | '(' Op Exp ')' { setSpan (spanFromTo $1 $4) (leftSection $2 $3) } -- TODO: waiting for type inference
  | '(' Exp Op ')'  { setSpan (spanFromTo $1 $4) (unOp (E.Var (getSpan $3) $3) $2) }
  | '(' Exp ConsOp ')'  { setSpan (spanFromTo $1 $4) (unOp (E.DCons (getSpan $3) $3) $2) }
  | '(' Exp '-' ')' { setSpan (spanFromTo $1 $4) (unOp (E.Var (getSpan $3) (mkMinusVar $3)) $2) }
  | '(' Exp '-.' ')' { setSpan (spanFromTo $1 $4) (unOp (E.Var (getSpan $3) (mkMinusDotVar $3)) $2) }
  | '[' ']' {% listMissingTypeAppError $1 $2 }
  | '[' ExpListComma ']' {% listMissingTypeAppError $1 $3 }

Exp :: { E.ParsedExp }
  -- Keyword expressions
  : 'let' LetDeclBlock 'in' Exp { E.Let (spanFromTo $1 $4) $2 $4 }
  | '\\' ExpParamsArrow Exp %prec LAMBDA{ E.Abs (spanFromTo $1 $3) (fst $2) (snd $2) $3 }
  | 'if' Exp 'then' Exp 'else' Exp { E.If (spanFromTo $1 $6) $2 $4 $6 }
  | 'case' Exp 'of' CaseBlock { E.Case (spanFromTo $1 (snd $ last $4)) $2 $4 }
  | Exp ':' Type { E.Asc (spanFromTo $1 $3) $1 $3 }
  -- Operators
  -- TODO: handle operators more elegantly. They are responsible for most s/r 
  -- conflicts. We should:
  -- * Allow programmers to define operators (x op y = e, (op) x y = e)
  -- * Define precedences:
  --   * à la Haskell (declared by programmer) 
  --   * à la F# (depends on leading chars)
  | Exp '.'  Exp { binOp $1 (E.Var (getSpan $2) $ mkDotVar $2) $3 }
  | Exp ';'  Exp { E.Semi (spanFromTo $1 $3) $1 $3 }
  | Exp '$'  Exp { addArgExp (ExpLevel $3) $1 } -- { binOp $1 (E.Var (getSpan $2) $ mkDollarVar $2) $3 }
  | Exp '|>' Exp { addArgExp (ExpLevel $1) $3 } -- { binOp $1 (E.Var (getSpan $2) $ mkRTriangleVar $2) $3 }
  | Exp '||' Exp { binOp $1 (E.Var (getSpan $2) $ mkOrVar $2) $3 }
  | Exp '&&' Exp { binOp $1 (E.Var (getSpan $2) $ mkAndVar $2) $3 }
  | Exp CMP  Exp { binOp $1 (E.Var (getSpan $2) $ mkCmpVar (getText $2) $2) $3 }
  | Exp '+'  Exp { binOp $1 (E.Var (getSpan $2) $ mkPlusVar $2) $3 }
  | Exp '+.' Exp { binOp $1 (E.Var (getSpan $2) $ mkPlusDotVar $2) $3 }
  | Exp '-'  Exp { binOp $1 (E.Var (getSpan $2) $ mkMinusVar $2) $3 }
  | Exp '-.' Exp { binOp $1 (E.Var (getSpan $2) $ mkMinusDotVar $2) $3 }
  | Exp '*'  Exp { binOp $1 (E.Var (getSpan $2) $ mkTimesVar $2) $3 }
  | Exp '*.' Exp { binOp $1 (E.Var (getSpan $2) $ mkTimesDotVar $2) $3 }
  | Exp '/'  Exp { binOp $1 (E.Var (getSpan $2) $ mkDivVar $2) $3 }
  | Exp '/.' Exp { binOp $1 (E.Var (getSpan $2) $ mkDivDotVar $2) $3 }
  | Exp '^'  Exp { binOp $1 (E.Var (getSpan $2) $ mkPowerVar $2) $3 }
  | Exp '**' Exp { binOp $1 (E.Var (getSpan $2) $ mkTimesTimesVar $2) $3 }
  | Exp '++' Exp { binOp $1 (E.Var (getSpan $2) $ mkPlusPlusVar $2) $3 }
  | Exp '^^' Exp { binOp $1 (E.Var (getSpan $2) $ mkCaretCaretVar $2) $3 }
  | Exp '::' Exp { binOp $1 (E.DCons(getSpan $2) $ mkConsId $2) $3 }
  -- Unary minus
  -- Should we do something like GHC's NegativeLiterals or LexicalNegation instead?
  -- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/negative_literals.html
  | '-' ExpApp  %prec NEG { unOp (E.Var (getSpan $1) (mkNegateVar $1)) $2 }    
  | '-.' ExpApp %prec NEG { unOp (E.Var (getSpan $1) (mkNegateFVar $1)) $2 }    
  -- Application etc.  
  | ExpApp               { $1 }

ExpApp :: { E.ParsedExp }
  : ExpApp ExpPrimary { addArgExp (ExpLevel $2) $1 }
  | 'select' UPPER_ID { E.Select (spanFromTo $1 $2) (mkIdTk $2) }
  | 'sendType' '@' TypePrimary { E.SendType (spanFromTo $1 $3) $3 }
  | 'channel' '@' TypePrimary { E.Channel (spanFromTo $1 $3) $3 }
  | '[' ']' '@' TypePrimary { let s = spanFromTo $1 $2 in E.App (spanFromTo $1 $4) (E.DCons s (mkNilId s)) [TypeLevel $4] } -- TODO: multiplicities
  | '[' ExpListComma ']' '@' TypePrimary { E.listExp (spanFromTo $1 $3) $5 $2 } -- TODO: multiplicities
  | ExpApp '@' TypePrimary { addArgExp (TypeLevel $3) $1 }
  | ExpApp '#' MultiplicityPrimary { addArgExp (MultLevel $3) $1 }
  | ExpPrimary        { $1 }

Op :: { Variable }
  : CMP  { mkCmpVar (getText $1) $1 }
  | '||' { mkOrVar $1 }
  | '&&' { mkAndVar $1 }
  | '+'  { mkPlusVar $1 }
  | '*'  { mkTimesVar $1 }
  | '/'  { mkDivVar $1 }
  | '^'  { mkPowerVar $1 }
  | '+.' { mkPlusDotVar $1 }
  | '*.' { mkTimesDotVar $1 }
  | '/.' { mkDivDotVar $1 }
  | '**' { mkTimesTimesVar $1 }
  | '++' { mkPlusPlusVar $1 }
  | '^^' { mkCaretCaretVar $1 }
  | '|>' { mkRTriangleVar $1 }
  | '$'  { mkDollarVar $1 }
  | ';'  { mkSemiVar $1 }
  | '.'  { mkDotVar $1 }

OpOrMinus :: { Variable }
  : Op  { $1 }
  | '-' { mkMinusVar $1 }
  | '-.' { mkMinusDotVar $1 }

ConsOp :: { Identifier }
  : '::' { mkConsId $1 }

ExpListComma :: { [E.ParsedExp] }
  : Exp ',' ExpListComma { $1 : $3 }
  | Exp                  { [$1] }

TypedPat :: { (E.Pat, T.ParsedType) }
  : '(' Pat ':' Type ')' { ($2, $4) }
  -- | PatPrimary { ($1, ?) } -- TODO: type inference var?

ExpParamsArrow :: { ([Level (E.Pat, T.ParsedType) (Variable, K.Kind) Variable], K.Multiplicity) } 
  :     TypedPat  ExpParamsArrow { first (ExpLevel  $1 :) $2 }
  | '@' KindedVar ExpParamsArrow { first (TypeLevel $2 :) $3 }
  | '#' MultVar   ExpParamsArrow { first (MultLevel $2 :) $3 }
  |     TypedPat  MultArrow { ([ExpLevel  $1], snd $2) }
  | '@' KindedVar MultArrow { ([TypeLevel $2], snd $3) }
  | '#' MultVar   MultArrow { ([MultLevel $2], snd $3) }

CaseBlock :: { [(E.Pat, E.ParsedRHS)] }
  : OPEN CaseListPIPE Close { $2 }

CaseListPIPE :: { [(E.Pat, E.ParsedRHS)] }
  : Case PIPE CaseListPIPE { $1 : $3 }
  | Case                   { [$1] }

Case :: { (E.Pat, E.ParsedRHS) }
  : Pat RHS('->') { ($1, $2) }

PatPrimary :: { E.Pat }
  : INT_LIT          { E.IntPat    (getSpan $1) (read (getText $1)) }
  | FLOAT_LIT        { E.FloatPat  (getSpan $1) (read (getText $1)) }
  | CHAR_LIT         { E.CharPat   (getSpan $1) (read (getText $1)) }
  | STRING_LIT       { E.stringPat (getSpan $1) (read (getText $1)) }
  | WILDCARD         { E.WildPat   (getSpan $1) (mkVarTk $1)}
  | ExpVar           { E.VarPat    (getSpan $1) $1 }
  | 'Wait'           { E.WaitPat   (getSpan $1) }
  | '[' PatListComma ']'           { E.listPat (spanFromTo $1 $3) $2 }
  | '(' ')'                        { E.TuplePat (spanFromTo $1 $2) [] }
  | '(' Pat ',' PatNEListComma ')' { E.TuplePat (spanFromTo $1 $5) ($2 : $4) }
  | '(' '@' KindedVar ',' AtKindedVarListCommaPat ')'{ uncurry (E.PackPat (spanFromTo $1 $6)) (first ($3:) $5) }
  | DataConstructor                { E.DConsPat   (getSpan $1) $1 [] }
  | '(' Pat ')'                    { setSpan  (spanFromTo $1 $3) $2 }
  | LOWER_ID_AT PatPrimary         { E.AsPat (spanFromTo $1 $2) (mkVarTk $1) $2 }

Pat :: { E.Pat }
  : DataConstructor PatPrimaryListWS { E.DConsPat (spanFromTo $1 (last $2)) $1 $2 }
  | '?' PatPrimary ';' Pat           { E.InPat (spanFromTo $1 $4) $2 $4 } 
  | '&' DataConstructor PatPrimary   { E.ChoicePat (spanFromTo $1 $3) $2 $3 }
  | '?' '@' KindedVar '.' Pat        { E.TypeInPat (spanFromTo $1 $5) $3 $5 } 
  | Pat '::' Pat                     { E.ConsPat (spanFromTo $1 $3) $1 $3 }
  | PatPrimary                       { $1 }

DataConstructor :: { Identifier }
  : UPPER_ID { mkIdTk $1 }
  -- | '(' Commas ')' { mkTupleId $2 (spanFromTo $1 $3) } -- TODO: multiplicities
  -- | '(' '::'   ')' { mkConsId  (spanFromTo $1 $3) } -- TODO: multiplicities
  -- | '[' ']' { mkNilId (spanFromTo $1 $2) } -- TODO: multiplicities

PatPrimaryListWS :: { [E.Pat] } 
  : PatPrimary PatPrimaryListWS { $1 : $2 }
  | PatPrimary { [$1] }

FnDefParams :: { [Level E.Pat Variable Variable] } 
  : PatPrimary  FnDefParams { ExpLevel  $1 : $2 }
  | '@' TypeVar FnDefParams { TypeLevel $2 : $3 }
  | '#' MultVar FnDefParams { MultLevel $2 : $3 }
  | PatPrimary   { [ExpLevel  $1] }
  | '@' TypeVar  { [TypeLevel $2] }
  | '#' MultVar  { [MultLevel $2] }

PatListComma :: { [E.Pat] }
  : {- empty -} { [] }
  | PatNEListComma { $1 }

PatNEListComma :: { [E.Pat] }
  : Pat { [$1] }
  | Pat ',' PatNEListComma { $1 : $3 }

AtKindedVarListCommaPat :: { ([(Variable, K.Kind)], E.Pat) }
  : '@' KindedVar ',' AtKindedVarListCommaPat { first ($2 :) $4 }
  | Pat { ([], $1) }

LetDeclBlock :: { [E.ParsedLetDecl] }
  : OPEN LetDeclListPIPE Close { $2 }

LetDeclListPIPE :: { [E.ParsedLetDecl] }
  : LetDecl PIPE LetDeclListPIPE { $1 : $3 }
  | LetDecl                      { [$1] }
  | {- empty -}                  { [] }

Close
  : CLOSE { () }
  | error {% popLayout }

-- Parsing FreeSTi commands

ItDecl :: { M.ParsedModule }
  : Exp { let s = getSpan $1 in
          M.insertDef (E.ValDef
            (E.VarPat s (mkVarTk (TkLowerId s "it")))
            (E.UnguardedRHS $1 Nothing)) M.emptyParsedModule }

DeclList :: { M.ParsedModule }
  : OPEN ModuleDeclListPIPE Close { $2 }

TwoTypes :: { (T.ParsedType, T.ParsedType) }
  : TypePrimary TypePrimary { ($1, $2) }

-- Standalone entry points used by the REPL's :info command.
LowerId :: { Variable }
  : LOWER_ID { mkVarTk $1 }

UpperId :: { Identifier }
  : UPPER_ID { mkIdTk $1 }

-- Parsing test cases

EquivalenceTestCases :: { [((T.ParsedType, T.ParsedType, K.Kind), M.ParsedModule)] }
  : TypeTestCases(EquivalenceTest) { $1 }

KindingTestCases :: {[((T.ParsedType, Maybe K.Kind), M.ParsedModule)]}
  : TypeTestCases(KindingTest) {$1}

TypeTestCases(t)
  : TypeTestCase(t) TypeTestCases(t) { $1 : $2 }
  | {- empty -}    { [] }

TypeTestCase(t)
  : 'case' t 'where' TypeTestBlock { ($2, $4) }
  | 'case' t { ($2, M.emptyParsedModule) }

EquivalenceTest :: { (T.ParsedType, T.ParsedType, K.Kind) }
  : Type CMP Type ':' Kind { ($1, $3, $5) }

KindingTest :: { (T.ParsedType, Maybe K.Kind) }
  : Type ':' Kind { ($1, Just $3) }
  | Type { ($1, Nothing) }

TypeTestBlock :: { M.ParsedModule }
  : OPEN TypeTestDeclListPIPE Close { $2 }

TypeTestDeclListPIPE :: { M.ParsedModule }
  : TypeTestDecl PIPE TypeTestDeclListPIPE { $1 $3 }
  | TypeTestDecl { $1 M.emptyParsedModule }

TypeTestDecl :: { M.ParsedModule -> M.ParsedModule }
  : KindSig  { $1 }
  | TypeDecl { $1 }
  | DataDecl { $1 }

{

lexer cont = scan >>= cont

parseError :: (Token, [String]) -> Lexer a
parseError (tk, ss) = throwError [ParseError s (tk, ss)]
  where
    s'@Span{startPos, endPos} = (getSpan tk)
    s | startPos == endPos = s'{endPos = second (+ 1) endPos}
      | otherwise          = s'

invalidMultiplicityError :: Int -> Token -> Lexer a
invalidMultiplicityError i tk =
  throwError [UnsupportedError (getSpan tk) ("Invalid multiplicity: `" ++ show i++ "`") ("(Valid multiplicities include `" ++ show (K.Lin $ getSpan tk) ++ "`, `" ++ show (K.Un $ getSpan tk) ++ "` and variables)")]

invalidPrekindError :: String -> Token -> Lexer a
invalidPrekindError s tk = 
  throwError [UnsupportedError (getSpan tk) ("Invalid prekind: `" ++ s ++ "`") ("(Valid prekinds include `" ++ show K.Top ++ "`, `" ++ show K.Session ++ "` and `" ++ show K.Channel ++"`)")]

listMissingTypeAppError :: Token -> Token -> Lexer a
listMissingTypeAppError tk1 tk2 =
  throwError [UnsupportedError (spanFromTo tk1 tk2) "List expressions require a type application" "Please provide a type application after this expression"]

prefixListConsError :: Token -> Token -> Lexer a
prefixListConsError tk1 tk2 =
  throwError [UnsupportedError (spanFromTo tk1 tk2) "The prefix list constructor is not yet supported" "(Consider using it infixed)"]

prefixListTypeConsError :: Token -> Token -> Lexer a
prefixListTypeConsError tk1 tk2 =
  throwError [UnsupportedError (spanFromTo tk1 tk2) "The prefix list type constructor is not yet supported" "Please provide a type between the brackets"]

prefixTupleTypeConsError :: Token -> Token -> Lexer a
prefixTupleTypeConsError tk1 tk2 = 
  throwError [UnsupportedError (spanFromTo tk1 tk2) "Prefix tuple type constructors are not yet supported" "(Consider using a tuple type)"] 

prefixTupleExpConsError :: Token -> Token -> Lexer a
prefixTupleExpConsError tk1 tk2 = 
  throwError [UnsupportedError (spanFromTo tk1 tk2) "Prefix tuple constructors are not yet supported" "(Consider using a tuple expression)"] 

runParseModule :: FilePath -> String -> Either [Error] M.ParsedModule
runParseModule = runLexer parseModule 

}
