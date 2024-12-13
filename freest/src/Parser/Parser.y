{
{-# LANGUAGE TupleSections #-}
{- |
Module      :  Parser.Parser
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements a layout-sensitive parser for FreeST.
-}
module Parser.Parser where

import Parser.Lexer (scan)
import Parser.Token
import Parser.LexerUtils
import Parser.ParserUtils
import Syntax.Base 
import Syntax.Names
import qualified Syntax.Expression as E 
import qualified Syntax.Kind       as K 
import qualified Syntax.Type       as T 
import qualified Syntax.Module     as M
import UI.Error

import Control.Monad.Except
import Data.Bifunctor
import qualified Data.List.NonEmpty as NE
import Debug.Trace
}

%name parseExp Exp
%name parseType Type
%name parseModuleDecl ModuleDecl
%name parseModule Module
%name parseEquivalenceTests EquivalenceTests
%name parseKindingTests KindingTests

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
  'case'   { TkCase _ }
  'of'     { TkOf _ }
  'channel'{ TkChannel _ }
  'select' {TkSelect _ }
  'if'     { TkIf _ }
  'then'   { TkThen _ }
  'else'   { TkElse _ }
  'forall' { TkForall _ }
  'rec'    { TkRec _ }
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
  '*->'   { TkUnArrow _ }
  '1->'   { TkLinArrow _ }
  -- Operators
  '|'     { TkPipe _ }
  ':'     { TkColon _ }
  '::'    { TkColonColon _ }
  ';'     { TkSemi _ }
  '@'     { TkAt _ }
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
  '?'     { TkQuestion _ }
  '!'     { TkBang _ }
  '&'     { TkAmp _ }
  -- Kinds
  '1T'    { TkLinTopKind _ }
  '*T'    { TkUnTopKind _ }
  '1S'    { TkLinSessionKind _ }
  '*S'    { TkUnSessionKind _ }
  '1A'    { TkLinAbsorbKind _ }
  '*A'    { TkUnAbsorbKind _ }

  -- Expression literals
  INT_LIT { TkIntLit _ _ }
  FLOAT_LIT { TkFloatLit _ _ }
  CHAR_LIT { TkCharLit _ _ }
  -- STRING_LIT {TkStringLit _ _ }

  -- Identifiers
  UPPER_ID { TkUpperId _ _ }  
  QUALIFIED_UPPER_ID { TkQualifiedUpperId _ _ }
  WILDCARD { TkWildcard _ _ }
  LOWER_ID { TkLowerId _ _ }

%right    'in' 'else' 'case'
%right    '.'
%right    '=>' '->' '1->' '*->' ARROW
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

Module :: { M.Module }
  : 'module' ModuleName 'where' ImportModuleDeclBlock { M.setName (split '.' $ getText $2) $4 }
  -- TODO: no module declaration. See notes in Lexer.
  -- | ImportModuleDeclBlock { $1 }

ModuleName :: { Token } : UPPER_ID { $1 } | QUALIFIED_UPPER_ID { $1 }

ImportModuleDeclBlock :: { M.Module }
  : OPEN ImportModuleDeclListPIPE Close { $2 }

ImportModuleDeclListPIPE :: { M.Module }
  : ImportDecl PIPE ImportModuleDeclListPIPE { $1 $3 }
  | ModuleDecl PIPE ModuleDeclListPIPE       { $1 $3 }
  | ImportDecl { $1 M.empty }
  | ModuleDecl { $1 M.empty }
  | {- empty -} { M.empty }

ImportDecl :: { M.Module -> M.Module }
  : 'import' QUALIFIED_UPPER_ID { M.insertImport (split '.' $ getText $2) }
  | 'import' UPPER_ID           { M.insertImport [getText $2] }

ModuleDeclListPIPE :: { M.Module }
  : ModuleDecl PIPE ModuleDeclListPIPE { $1 $3 }
  | ModuleDecl                         { $1 M.empty }
  | {- empty -}                        { M.empty }

ModuleDecl :: { M.Module -> M.Module }
  : LetDecl  { M.insertDef $1 }
  | DataDecl { $1 }
  | TypeDecl { $1 }
  | KindSig  { $1 }

DataDecl :: { M.Module -> M.Module }
  : 'data' UPPER_ID VarListWS '=' DataConsListPipe { M.insertDataDecl (mkIdTk $2) $3 $5 }

TypeDecl :: { M.Module -> M.Module }
  : 'type' UPPER_ID VarListWS '=' Type             { M.insertTypeDecl (mkIdTk $2) $3 $5 }

KindSig :: { M.Module -> M.Module }
  : 'type' UPPER_ID ':' Kind { M.insertKindSig (mkIdTk $2) $4 }

LetDecl
  : Pat DefRHS { E.ValDecl $1 ($2 Nothing) }
  | Pat DefRHS 'where' LetDeclBlock { E.ValDecl $1 ($2 (Just $4)) }
  | LOWER_ID PatPrimaryOrAtVarListWS DefRHS                      { E.FnDecl (mkVarTk $1) [($2, $3 Nothing)] }
  | LOWER_ID PatPrimaryOrAtVarListWS DefRHS 'where' LetDeclBlock { E.FnDecl (mkVarTk $1) [($2, $3 (Just $5))] }
  | LowerIdListComma ':' Type { E.SigDecl $1 $3 }

DefRHS :: { Maybe [E.LetDecl] -> E.RHS }
  : '=' Exp     { E.UnguardedRHS $2 }
  | GuardedExps { E.GuardedRHS $1 }

GuardedExps :: { [(E.Exp, E.Exp)] }
  : '|' Exp '=' Exp GuardedExps { ($2,$4) : $5 }
  | '|' Exp '=' Exp             { [($2,$4)] }
  -- otherwise is simply a variable defined as True

-- LowerIdListWS :: { [Variable] }
--   : LOWER_ID LowerIdListWS { mkVarTk $1 : $2 }
--   | {- empty -}            { [] }

LowerIdListComma :: { [Variable] }
  : LOWER_ID ',' LowerIdListComma { mkVarTk $1 : $3 }
  | LOWER_ID                  { [mkVarTk $1] }

DataConsListPipe :: { [(Identifier, [T.Type])] }
  : DataCons '|' DataConsListPipe { $1 : $3 }
  | DataCons                      { [$1] }

DataCons :: { (Identifier, [T.Type]) }
  : UPPER_ID TypePrimaryListWS { (mkIdTk $1, $2) }

TypePrimaryListWS :: { [T.Type] }
  : TypePrimary TypePrimaryListWS { $1 : $2 }
  | {- empty -}                   { [] }

Kind :: { K.Kind }
  : Kind '->' Kind %prec ARROW { K.Arrow (spanFromTo $1 $3) $1 $3 }
  | '(' Kind ')'                { $2 }
  | ProperKind                  { $1 }

ProperKind :: { K.Kind }
  : '1T' { K.Proper (getSpan $1) K.Lin K.Top }
  | '*T' { K.Proper (getSpan $1) K.Un K.Top }
  | '1S' { K.Proper (getSpan $1) K.Lin K.Session }
  | '*S' { K.Proper (getSpan $1) K.Un K.Session }
  | '1A' { K.Proper (getSpan $1) K.Lin K.Absorb }
  | '*A' { K.Proper (getSpan $1) K.Un K.Absorb }

TypePrimary :: { T.Type }
  -- Builtins (necessary?)
  : 'Int'    { T.Int (getSpan $1) }
  | 'Float'  { T.Float (getSpan $1) }
  | 'Char'   { T.Char (getSpan $1) }
  | 'Skip'   { T.Skip (getSpan $1) }
  | 'Close'  { T.End (getSpan $1) T.Out }
  | 'Wait'   { T.End (getSpan $1) T.In }
  -- Unit, Tuples, Operators
  | '(' ')'        { T.DName (spanFromTo $1 $2) (mkUnit (spanFromTo $1 $2)) }
  | '(' Type ',' TypeListComma ')' 
      { T.AppDName (spanFromTo $1 $5) (mkTupleCons (length $4) (spanFromTo $1 $5)) ($2 : $4) }
  | '(' Commas ')' { T.TName (spanFromTo $1 $3) (mkTupleCons $2 (spanFromTo $1 $3)) }
  | '(' Arrow ')'  {T.Arrow (spanFromTo $1 $3) (snd $2)}
  -- | '(' Type Arrow ')' -- TODO: sections
  -- | '(' Arrow Type ')' -- TODO: sections
  | '(' Polarity ')'     {T.Message (spanFromTo $1 $3) K.Lin (snd $2)}
  | '(' '*' Polarity ')' {T.Message (spanFromTo $1 $4) K.Un (snd $3)}
  -- | '(' Type ';' ')' -- TODO: sections
  -- | '(' ';' Type ')' -- TODO: sections
  -- Messages
  | Polarity TypePrimary %prec MSG     { T.AppMessage (spanFromTo (fst $1) $2) K.Lin (snd $1) $2 }
  | '*' Polarity TypePrimary %prec MSG { T.AppMessage (spanFromTo $1 $3) K.Un  (snd $2) $3 }
  -- Choices
  | View '{' LabelTypeListComma '}'     { T.Choice (spanFromTo (fst $1) $4) K.Lin (snd $1) $3 }
  | '*' View '{' LabelTypeListComma '}' { T.Choice (spanFromTo $1 $5)       K.Un  (snd $2) $4 }
  -- Variables and constructors
  | UPPER_ID { T.TName (getSpan $1) (mkIdTk $1) }
  | LOWER_ID { T.Var (getSpan $1) (mkVarTk $1) }
  -- Lists
  | '[' ']'      { T.DName (spanFromTo $1 $2) (mkNil (spanFromTo $1 $2))   }
  | '[' Type ']' { T.AppDName (spanFromTo $1 $3) (mkNil (spanFromTo $1 $3)) [$2] }
  -- Parenthesized type
  | '(' Type ')' { setSpan (spanFromTo $1 $3) $2 }

Type :: { T.Type }
  : Type Arrow Type %prec ARROW { T.AppArrow (fst $2) (snd $2) $1 $3 }
  | Type ';' Type               { T.AppSemi (spanFromTo $1 $3) $1 $3 }
  -- If forall is just a constant, remove this rule and uncomment the one below and the declaration of Forall.
  | 'forall' KindedVar KindedVarListWS '.' Type   { T.variadicForall (spanFromTo $1 $5) ($2 NE.:| $3) $5 }
  -- | 'forall' KindedVar Forall   { T.App (spanFromTo $1 $3) (T.Forall (getSpan $1) (snd $2)) [(T.Abs (spanFromTo (fst $2) $3) [(fst $2, snd $2)] $3)] }
  -- | 'rec'    KindedVar '.' Type { T.App (spanFromTo $1 $4) (T.Rec    (getSpan $1) (snd $2)) [(T.Abs (spanFromTo (fst $2) $4) [(fst $2, snd $2)] $4)] }
  | TypeApp                     { $1 }

TypeApp :: { T.Type }
  : TypeApp TypePrimary { addArgType $2 $1 }
  | 'Dual' TypePrimary  { T.AppDual (spanFromTo $1 $2) $2 }
  | TypePrimary { $1 }

TypeListComma :: { [T.Type] }
  : Type ',' TypeListComma { $1 : $3 }
  | Type                   { [$1] }

-- Forall :: { T.Type }
--   : '.' Type { $2 }
--   | KindedVar Forall { T.App (spanFromTo (fst $1) $2) (T.Forall (getSpan (fst $1)) (snd $1)) [(T.Abs (spanFromTo (fst $1) $2) [(fst $1, snd $1)] $2)]}

Commas :: { Int }
  : ',' { 1 }
  | ',' Commas { succ $2 }

Polarity :: { (Span, T.Polarity) }
  : '!'  { (getSpan $1, T.Out) }
  | '?'  { (getSpan $1, T.In) }

View :: { (Span, T.Polarity) }
  : '+' { (getSpan $1, T.Out) }
  | '&' { (getSpan $1, T.In) }

LabelTypeListComma :: { [(Identifier, T.Type)] }
  : UPPER_ID ':' Type ',' LabelTypeListComma { (mkIdTk $1, $3) : $5 }
  | UPPER_ID ':' Type { [(mkIdTk $1, $3)] }

VarListWS :: { [Variable] }
  : {- empty -} { [] }
  | LOWER_ID VarListWS { mkVarTk $1 : $2 }

KindedVarListWS :: { [(Variable, K.Kind)] }
  : {- empty -} { [] }
  | KindedVar KindedVarListWS { $1 : $2 }

KindedVar :: { (Variable, K.Kind) }
  : LOWER_ID { (mkVarTk $1, dummyKindVar $1) }
  | LOWER_ID ':' Kind { (mkVarTk $1, $3) }

ExpPrimary :: { E.Exp }
  : INT_LIT     { E.Int    (getSpan $1) (read $ getText $1) }
  | FLOAT_LIT   { E.Float  (getSpan $1) (read $ getText $1) }
  | CHAR_LIT    { E.Char   (getSpan $1) (read $ getText $1) }
  -- | STRING_LIT  { E.String (getSpan $1) (read $ getText $1) }
  | LOWER_ID    { E.Var    (getSpan $1) (mkVarTk $1) }
  | UPPER_ID    { E.Cons   (getSpan $1) (mkIdTk $1) }
  | '(' ')'     { E.Tuple  (spanFromTo $1 $2) [] }
  | '(' Commas ')' { let s = spanFromTo $1 $3 in E.Cons s (mkTupleCons $2 s) }
  | '(' Exp ',' ExpListComma ')' {E.Tuple (spanFromTo $1 $5) ($2 : $4) }      -- with tuples in the Exp AST
                              -- { tupleAppExp (spanFromTo $1 $5) ($2 : $4) } -- using tuple constructors (,+)
  -- | TupleSection { ... }                                                   -- TODO: tuple sections
  | '(' Exp ')' { setSpan  (spanFromTo $1 $3) $2 }
  | '(' Op ')'  { E.Var (spanFromTo $1 $3) (setSpan (spanFromTo $1 $3) $2) }
  | '(' ConsOp ')' { E.Cons (spanFromTo $1 $3) (setSpan (spanFromTo $1 $3) $2) }
  | '(' '-' ')' { E.Var (spanFromTo $1 $3) (mkNegate (spanFromTo $1 $3))}
  -- | '(' Op Exp ')' { setSpan (spanFromTo $1 $4) (leftSection $2 $3) } -- TODO: waiting for type inference
  | '(' Exp Op ')'  { setSpan (spanFromTo $1 $4) (unOp (E.Var (getSpan $3) $3) $2) }
  | '(' Exp ConsOp ')'  { setSpan (spanFromTo $1 $4) (unOp (E.Cons (getSpan $3) $3) $2) }
  | '(' Exp '-' ')' { setSpan (spanFromTo $1 $4) (unOp (E.Var (getSpan $3) (mkMinus $3)) $2) }
  | '[' ']'     { let s = spanFromTo $1 $2 in E.Cons s (mkNil s)}
  | '[' ExpListComma ']' { consAppExp (spanFromTo $1 $3) $2 }

Exp :: { E.Exp }
  -- Keyword expressions
  : 'let' LetDeclBlock 'in' Exp { E.Let (spanFromTo $1 $4) $2 $4 }
  | '\\' PatTypeOrKindedVarListArrow Exp   { E.Abs (spanFromTo $1 $3) (fst $2) (snd $2) $3 }
  | 'if' Exp 'then' Exp 'else' Exp { E.If (spanFromTo $1 $6) $2 $4 $6 }
  | 'case' Exp 'of' CaseBlock { E.Case (spanFromTo $1 (snd $ last $4)) $2 $4 }
  -- Operators
  -- TODO: handle operators more elegantly. They are responsible for most s/r conflicts.
  -- * Allow programmers to define operators (x op y = e, (op) x y = e)
  -- * Define precedences:
  --   * à la Haskell (declared by programmer) 
  --   * à la F# (depends on leading chars)
  | Exp ';'  Exp { binOp $1 (E.Var (getSpan $2) $ mkSemi $2) $3 }
  | Exp '$'  Exp { binOp $1 (E.Var (getSpan $2) $ mkDollar $2) $3 }
  | Exp '|>' Exp { binOp $1 (E.Var (getSpan $2) $ mkRTriangle $2) $3 }
  | Exp '||' Exp { binOp $1 (E.Var (getSpan $2) $ mkOr $2) $3 }
  | Exp '&&' Exp { binOp $1 (E.Var (getSpan $2) $ mkAnd $2) $3 }
  | Exp CMP  Exp { binOp $1 (E.Var (getSpan $2) $ mkCmp (getText $2) $2) $3 }
  | Exp '+'  Exp { binOp $1 (E.Var (getSpan $2) $ mkPlus $2) $3 }
  | Exp '+.' Exp { binOp $1 (E.Var (getSpan $2) $ mkPlusDot $2) $3 }
  | Exp '-'  Exp { binOp $1 (E.Var (getSpan $2) $ mkMinus $2) $3 }
  | Exp '-.' Exp { binOp $1 (E.Var (getSpan $2) $ mkMinusDot $2) $3 }
  | Exp '*'  Exp { binOp $1 (E.Var (getSpan $2) $ mkTimes $2) $3 }
  | Exp '*.' Exp { binOp $1 (E.Var (getSpan $2) $ mkTimesDot $2) $3 }
  | Exp '/'  Exp { binOp $1 (E.Var (getSpan $2) $ mkDiv $2) $3 }
  | Exp '/.' Exp { binOp $1 (E.Var (getSpan $2) $ mkDivDot $2) $3 }
  | Exp '^'  Exp { binOp $1 (E.Var (getSpan $2) $ mkPower $2) $3 }
  | Exp '**' Exp { binOp $1 (E.Var (getSpan $2) $ mkTimesTimes $2) $3 }
  | Exp '++' Exp { binOp $1 (E.Var (getSpan $2) $ mkPlusPlus $2) $3 }
  | Exp '^^' Exp { binOp $1 (E.Var (getSpan $2) $ mkCaretCaret $2) $3 }
  | Exp '::' Exp { binOp $1 (E.Cons(getSpan $2) $ mkCons $2) $3 }
  -- Unary minus
  -- Should we do something like GHC's NegativeLiterals or LexicalNegation instead?
  -- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/negative_literals.html
  | '-' ExpApp %prec NEG { unOp (E.Var (getSpan $1) (mkNegate $1)) $2 }    
  -- Application etc.  
  | ExpApp               { $1 }

ExpApp :: { E.Exp }
  : ExpApp ExpPrimary { addArgExp (ExpLevel $2) $1 }
  | 'select' UPPER_ID { E.Select (spanFromTo $1 $2) (mkIdTk $2) }
  | 'channel' '@' TypePrimary { E.Channel (spanFromTo $1 $3) $3 }
  | ExpApp '@' TypePrimary { addArgExp (TypeLevel $3) $1 }
  | ExpPrimary        { $1 }

Op :: { Variable }
   : CMP  { mkCmp (getText $1) $1 }
   | '||' { mkOr $1 }
   | '&&' { mkAnd $1 }
   | '+'  { mkPlus $1 }
   | '*'  { mkTimes $1 }
   | '/'  { mkDiv $1 }
   | '^'  { mkPower $1 }
   | '+.' { mkPlusDot $1 }
   | '*.' { mkTimesDot $1 }
   | '/.' { mkDivDot $1 }
   | '**' { mkTimesTimes $1 }
   | '++' { mkPlusPlus $1 }
   | '^^' { mkCaretCaret $1 }
   | '|>' { mkRTriangle $1 }
   | '$'  { mkDollar $1 }
   | ';'  { mkSemi $1 }

ConsOp :: { Identifier }
  : '::' { mkCons $1 }

ExpListComma :: { [E.Exp] }
  : Exp ',' ExpListComma { $1 : $3 }
  | Exp                  { [$1] }

UnArrow :: { (Span, K.Multiplicity) }
  : '->'  { (getSpan $1, K.Un ) }
  | '*->' { (getSpan $1, K.Un ) }

LinArrow :: { (Span, K.Multiplicity) }
  : '1->'  { (getSpan $1, K.Lin ) }

Arrow :: { (Span, K.Multiplicity) }
  : UnArrow  { $1 }
  | LinArrow { $1 }

PatTypeOrKindedVarListArrow :: { ([Level (E.Pat, T.Type) (Variable, K.Kind)], K.Multiplicity) } 
  : PatPrimary   ':' TypePrimary PatTypeOrKindedVarListArrow { first (ExpLevel  ($1        , $3) :) $4 }
  | '@' KindedVar PatTypeOrKindedVarListArrow { first (TypeLevel $2 :) $3 }
  | PatPrimary   ':' TypePrimary Arrow { ([ExpLevel  ($1, $3)], snd $4) }
  | '@' KindedVar UnArrow { ([TypeLevel $2], snd $3) }

CaseBlock :: { [(E.Pat, E.Exp)] }
  : OPEN CaseListPIPE Close { $2 }

CaseListPIPE :: { [(E.Pat, E.Exp)] }
  : Case PIPE CaseListPIPE { $1 : $3 }
  | Case                   { [$1] }

Case :: { (E.Pat, E.Exp) }
  : Pat '->' Exp { ($1, $3) }

PatPrimary :: { E.Pat }
  : INT_LIT          { E.IntPat    (getSpan $1) (read (getText $1)) }
  | FLOAT_LIT        { E.FloatPat  (getSpan $1) (read (getText $1)) }
  | CHAR_LIT         { E.CharPat   (getSpan $1) (read (getText $1)) }
  -- | STRING_LIT       { E.StringPat (getSpan $1) (read (getText $1)) }
  | WILDCARD         { E.WildPat   (getSpan $1) (mkVarTk $1)}
  | LOWER_ID         { E.VarPat    (getSpan $1) (mkVarTk $1) }
  | DataConstructor  { E.ConsPat   (getSpan $1) $1 [] }
  | '(' Pat ',' PatListComma ')' { E.TuplePat (spanFromTo $1 $5) ($2 : $4) }
  | '(' Pat ')'     { setSpan  (spanFromTo $1 $3) $2 }
  | LOWER_ID '&' PatPrimary { E.AsPat (spanFromTo $1 $3) (mkVarTk $1) $3 }

Pat :: { E.Pat }
  : DataConstructor PatPrimaryListWS { E.ConsPat (spanFromTo $1 (last $2)) $1 $2 }
  | Pat '::' Pat { E.ConsPat (spanFromTo $1 $3) (mkCons $2) [$1, $3] }
  | PatPrimary { $1 }

DataConstructor :: { Identifier }
  : UPPER_ID { mkIdTk $1 }
  | '(' Commas ')' { mkTupleCons $2 (spanFromTo $1 $3) }
  | '[' ']' { mkNil (spanFromTo $1 $2) }

PatPrimaryListWS :: { [E.Pat] } 
  : PatPrimary PatPrimaryListWS { $1 : $2 }
  | PatPrimary { [$1] }

PatPrimaryOrAtVarListWS :: { [Level E.Pat Variable] } 
  : PatPrimary   PatPrimaryOrAtVarListWS { ExpLevel $1            : $2 }
  | '@' LOWER_ID PatPrimaryOrAtVarListWS { TypeLevel (mkVarTk $2) : $3 }
  | PatPrimary   { [ExpLevel  $1          ] }
  | '@' LOWER_ID { [TypeLevel (mkVarTk $2)] }

PatListComma :: { [E.Pat] }
  : Pat { [$1] }
  | Pat ',' PatListComma { $1 : $3 }

LetDeclBlock :: { [E.LetDecl] }
  : OPEN LetDeclListPIPE Close { $2 }

LetDeclListPIPE :: { [E.LetDecl] }
  : LetDecl PIPE LetDeclListPIPE { $1 : $3 }
  | LetDecl                      { [$1] }
  | {- empty -}                  { [] }

Close
  : CLOSE { () }
  | error {% popLayout }

KindingTests :: { [(T.Type, M.Module)] }
  : KindingTest KindingTests { $1 : $2 }
  | {- empty -} { [] }

KindingTest :: { (T.Type, M.Module) }
  : 'case' Type 'where' TypeTestBlock {($2, $4)}
  | 'case' Type { ($2, M.empty)}

EquivalenceTests :: { [(T.Type, T.Type, M.Module)] }
  : EquivalenceTest EquivalenceTests { $1 : $2 }
  | {- empty -} { [] }

EquivalenceTest :: { (T.Type, T.Type, M.Module) }
  : 'case' Type CMP Type 'where' TypeTestBlock  { ($2, $4, $6) }
  | 'case' Type CMP Type { ($2, $4, M.empty) }

TypeTestBlock :: { M.Module }
  : OPEN TypeTestDeclListPIPE Close { $2 }

TypeTestDeclListPIPE :: { M.Module }
  : TypeTestDecl PIPE TypeTestDeclListPIPE { $1 $3 }
  | TypeTestDecl { $1 M.empty }

TypeTestDecl :: { M.Module -> M.Module }
  : KindSig  { $1 }
  | TypeDecl { $1 }
  | DataDecl { $1 }

{
lexer cont = scan >>= cont

parseError :: (Token, [String]) -> Lexer a
parseError (tk,ss) = throwError [(ParseError (getSpan tk) (tk, ss))] 
}