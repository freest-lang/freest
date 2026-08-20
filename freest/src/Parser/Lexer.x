{
{- |
Module      :  Parser.Lexer
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements a layout-sensitive lexer for FreeST, 
inspired by [Amélia Liao's tutorial](https://amelia.how/posts/parsing-layout.html).
-}
module Parser.Lexer where

import Parser.LexerUtils
import Parser.Token 
import Syntax.Base
import UI.Error

import Control.Monad.State
import Control.Monad.Except
}

%encoding "latin1"

-- Literals
@numspc = _*
$digit = [ 0-9 ]
@decimal = $digit (@numspc $digit)*
@exponent = @numspc [eE] [\-\+]? @decimal
@intLit = @decimal 
@floatLit = @numspc @decimal \. @decimal @exponent? | @numspc @decimal @exponent
@charLit = \'(\\n|[\\.]|.) \'
@stringLit = \"(\\.|[^\"]|\n)*\"

-- Identifiers
$lower = [ a-z ]
$upper = [ A-Z ]
@lowerId = $lower [ $lower $upper $digit _ ' ]*
@lowerIdAt = @lowerId \@
@upperId = $upper [ $lower $upper $digit _ ' ]*
@qualifiedUpperId = @upperId (\. @upperId)+
@wildcard = _ [ $lower $upper $digit _ ' ]*

:-
-- Whitespace and comments
    [\ \t]+ ;
    "{-" (\-[^\}]|[^\-]|\n)* "-}" ;
<0> "--" .* \n { \_ -> pushStartCode newlineSC *> scan }
<0> \n         { \_ -> pushStartCode newlineSC *> scan }
<0> "--" .* ; -- when files end in a comment and no newline. TODO: check this

-- Keywords
<0> "module" { token TkModule }
<0> "where"  { layoutKw TkWhere }
<0> "import" { token TkImport }
<0> "data"   { token TkData }
<0> "type"   { token TkType }
<0> "let"    { layoutKw TkLet }
<0> "in"     { token TkIn }
<0> "mutual" { layoutKw TkMutual }
<0> "case"   { token TkCase }
<0> "of"     { layoutKw TkOf }
<0> "if"     { token TkIf }
<0> "then"   { token TkThen }
<0> "else"   { token TkElse }
<0> "forall" { token TkForall }
<0> "exists" { token TkExists }
<0> "rec"    { token TkRec }
<0> "channel"{ token TkChannel }
<0> "select_" { token TkSelectUn }
<0> "select" { token TkSelect }
<0> "sendType"    { token TkSendType }
<0> "receiveType" { token TkReceiveType }

-- Punctuation
<0> "\"    { token TkBackslash }
<0> "->"   { token TkArrow }
<0> "-{"   { token TkArrowButt }
<0> "}->"  { token TkArrowHead }
<0> "="    { token TkEqual }
<0> ":"    { token TkColon }
<0> "."    { token TkDot }
<0> "@"    { token TkAt }
<0> "#"    { token TkHash }
<0> ","    { token TkComma }
<0> "("    { token TkLParen }
<0> ")"    { token TkRParen }
<0> "{"    { token TkOpen }
<0> "}"    { token TkClose }
<0> "|"    { token TkPipe }
<0> "["    { token TkLSquare }
<0> "]'"   { token TkRSquarePrime }
<0> "]"    { token TkRSquare }

-- Operators
<0> "::'" { token TkColonColonPrime }
<0> "::"  { token TkColonColon }
<0> ";"   { token TkSemi }
<0> "$"   { token TkDollar }
<0> "||"  { token TkPipePipe }
<0> "&&"  { token TkAmpAmp }
<0> "|>"  { token TkPipeGT }
<0> "+"   { token TkPlus }
<0> "+."  { token TkPlusDot }
<0> "++'" { token TkPlusPlusPrime }
<0> "++"  { token TkPlusPlus }
<0> "-"   { token TkMinus }
<0> "-."  { token TkMinusDot }
<0> "*"   { token TkStar }
<0> "*."  { token TkStarDot }
<0> "**"  { token TkStarStar }
<0> "/"   { token TkSlash }
<0> "/."  { token TkSlashDot }
<0> "^"   { token TkCaret }
<0> ">"   { emit TkCmp }
<0> "<"   { emit TkCmp }
<0> ">."  { emit TkCmp }
<0> "<."  { emit TkCmp }
<0> ">="  { emit TkCmp }
<0> "<="  { emit TkCmp }
<0> ">=." { emit TkCmp }
<0> "<=." { emit TkCmp }
<0> "=="  { emit TkCmp }
<0> "/="  { emit TkCmp }

-- Types
<0> "Int"   { token TkIntType }
<0> "Float" { token TkFloatType }
<0> "Char"  { token TkCharType }
<0> "Dual"  { token TkDualType }
<0> "Skip"  { token TkSkipType }
<0> "Close" { token TkCloseType }
<0> "Wait"  { token TkWaitType }
<0> "Void"  { token TkVoidType }
<0> \!      { token TkBang }
<0> \?      { token TkQuestion }
<0> \&      { token TkAmp }

-- Literals
<0> @intLit    { emit TkIntLit }
<0> @floatLit  { emit TkFloatLit }
<0> @charLit   { emit TkCharLit }
<0> @stringLit { emit TkStringLit }

-- Identifiers
<0> @wildcard         { emit TkWildcard }
<0> @lowerId          { emit TkLowerId }
<0> @lowerIdAt        { emit TkLowerIdAt . init }
<0> @upperId          { emit TkUpperId }
<0> @qualifiedUpperId { emit TkQualifiedUpperId }

-- TODO: no module declaration. 
-- Tried inserting this startcode before parsing, but something is not quite right here. 
-- The problem is that matching the empty string () still increments a column in alexGetByte.
-- Here I tried to decrement the column manually but this messed up the nested layouts. 
-- Trying again later.
-- <initModuleSC> {
--   \n         ;
--   "--" .* \n ;
--   "module" { \x -> popStartCode >> token TkModule x }
--   -- This code is wrong:
--   () { \x -> do 
--                 popStartCode
--                 lin <- gets (inpLine . lexerInput)
--                 col <- gets (inpColumn . lexerInput) 
--                 if lin == 0 
--                   then pushLayout (LayoutColumn (col - 1)) >> token TkVOpen x 
--                   else startLayout x 
--      }
-- }

<layoutSC> {
  -- Skip comments and whitespace
  "--" .* \n ;
  \n       ;

  \{ { openBrace }
  () { startLayout }
}

<emptyLayoutSC> () { emptyLayout }

<newlineSC> {
  \n         ;
  "--" .* \n ;

  () { offsideRule }
}

<eofSC> () { doEOF }

{
handleEOF = pushStartCode eofSC *> scan

doEOF s = do
  t <- layout
  case t of
    Nothing -> do
      popStartCode
      token TkEOF s
    (Just (LayoutColumn p)) -> do
      popLayout
      token (\sp -> TkVClose sp (Just (FileEnded p))) s
    -- (Just ExplicitLayout) -> do -- removed from Liao's version


scan :: Lexer Token
scan = do
  input@(Input _ _ _ string _) <- gets lexerInput
  startcode <- startCode
  case alexScan input startcode of
    AlexEOF -> handleEOF
    AlexError (Input l c _ inp f) ->
      let sp = Span{startPos=(l, c), endPos=(l, c + 1), filepath=f}
      in throwError [ case inp of
           ch : _ -> LexicalError sp ch
           []     -> UnexpectedEOF sp ]
    AlexSkip input' _ -> do
      modify' $ \s -> s { lexerInput = input' }
      scan
    AlexToken input' tokl action -> do
      modify' $ \s -> s { lexerInput = input' }
      action (take tokl string)

layoutKw t x = do
  setBlockKw x
  pushStartCode layoutSC
  token t x

openBrace s = do
  popStartCode
  -- pushLayout ExplicitLayout -- removed from Liao's version
  token TkOpen s

startLayout s = do
  popStartCode

  Input{inpLine=lin, inpColumn=col} <- gets lexerInput
  block <- Block <$> takeBlockKw <*> pure (lin, col)
  layout >>= \case
    Just (LayoutColumn enclosing) | col <= blockColumn enclosing ->
      setLayoutNote lin (EmptyBlock block enclosing) *> pushStartCode emptyLayoutSC
    _ -> pushLayout (LayoutColumn block)

  token TkVOpen s

emptyLayout s = do
  popStartCode
  pushStartCode newlineSC
  token (\sp -> TkVClose sp Nothing) s

offsideRule s = do
  context <- layout
  Input{inpLine=lin, inpColumn=col} <- gets lexerInput

  let continue = popStartCode *> scan

  case context of
    Just (LayoutColumn p) -> do
      case col `compare` blockColumn p of
        EQ -> do
          popStartCode
          token TkVPipe s
        GT -> setLayoutNote lin (Continues p) *> continue
        LT -> do
          popLayout
          end <- blockEndAt p
          token (\sp -> TkVClose sp (Just end)) s
    _ -> continue

}
