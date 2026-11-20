{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- |
Module      :  Parser.LexerUtils
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains utilities for lexing. It defines the types and functions
that handle the input, state, and actions of the lexer. Not all actions are 
defined here: some depend on start codes names that are only in scope in the
Lexer.x file.
-}
module Parser.LexerUtils where

import Parser.Token 
import Syntax.Base 
import UI.Error


import Data.Word ( Word8 )
import Data.List.NonEmpty qualified as NE
import Data.Bifunctor ( first )
import Data.Char ( chr, ord, digitToInt, isControl, isDigit, isHexDigit, isOctDigit, isSpace )
import Data.List ( find, intercalate, isPrefixOf, uncons )
import Control.Monad.State ( gets, modify', MonadState, StateT(..) )
import Control.Monad.Except ( MonadError, throwError )

data AlexInput
  = Input { inpLine   :: {-# UNPACK #-} !Int
          , inpColumn :: {-# UNPACK #-} !Int
          , inpLast   :: {-# UNPACK #-} !Char
          , inpStream :: String
          , inpFile   :: FilePath
          }
  deriving (Eq, Show)

alexPrevInputChar :: AlexInput -> Char
alexPrevInputChar = inpLast

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte inp@Input{inpStream = str, inpFile = f} = advance <$> uncons str where
  advance ('\n', rest) =
    ( fromIntegral (ord '\n')
    , Input { inpLine = inpLine inp + 1
            , inpColumn = 1
            , inpLast = '\n'
            , inpStream = rest 
            , inpFile = f
            }
    )
  advance (c, rest) =
    ( fromIntegral (ord c)
    , Input { inpLine = inpLine inp
            , inpColumn = if c == '\t' then nextTabStop (inpColumn inp) else inpColumn inp + 1
            , inpLast = c
            , inpStream = rest 
            , inpFile = f 
            }
    )

-- | The byte 'alexGetByte' returns truncates characters outside Latin-1.
alexGetChar :: AlexInput -> Maybe (Char, AlexInput)
alexGetChar inp = (\(_, inp') -> (inpLast inp', inp')) <$> alexGetByte inp

-- | As in GHC, only @{-@ and @-}@ are significant inside a block comment.
skipNestedComment :: AlexInput -> Maybe AlexInput
skipNestedComment = go (1 :: Int) where
  go 0 inp = Just inp
  go n inp = alexGetChar inp >>= \case
    ('-', inp') | Just ('}', inp'') <- alexGetChar inp' -> go (n - 1) inp''
    ('{', inp') | Just ('-', inp'') <- alexGetChar inp' -> go (n + 1) inp''
    (_, inp') -> go n inp'

newtype Lexer a = Lexer { _getLexer :: StateT LexerState (Either [Error]) a }
  deriving (Functor, Applicative, Monad, MonadState LexerState, MonadError [Error])

data Layout = ExplicitLayout | LayoutColumn Block
  deriving (Eq, Show)

data LexerState
  = LS { lexerInput      :: {-# UNPACK #-} !AlexInput
       , lexerStartCodes :: {-# UNPACK #-} !(NE.NonEmpty Int)
       , lexerLayout     :: [Layout]
       -- | What the offside rule last made of a line, and which line.
       , lexerNote       :: Maybe (Int, LayoutNote)
       -- | The keyword that opened the block about to start, if a keyword did.
       , lexerBlockKw    :: Maybe String
       , counter         :: Int
       }
  deriving (Eq, Show)

startCode :: Lexer Int
startCode = gets (NE.head . lexerStartCodes)

pushStartCode :: Int -> Lexer ()
pushStartCode i = modify' $ \st ->
  st { lexerStartCodes = NE.cons i (lexerStartCodes st)
     }

popStartCode :: Lexer ()
popStartCode = modify' $ \st ->
  st { lexerStartCodes =
         case lexerStartCodes st of
           _ NE.:| [] -> 0 NE.:| []
           _ NE.:| (x:xs) -> x NE.:| xs
     }

layout :: Lexer (Maybe Layout)
layout = gets (fmap fst . uncons . lexerLayout)

pushLayout :: Layout -> Lexer ()
pushLayout i = modify' $ \st ->
  st { lexerLayout = i:lexerLayout st }

popLayout :: Lexer ()
popLayout = modify' $ \st ->
  st { lexerLayout =
         case lexerLayout st of
           _:xs -> xs
           [] -> []
     }

-- | Why block @b@ ends here. A file that ends in a newline is offside at the
-- phantom line that follows it, so running out of input, not the indentation,
-- is what closed the block.
blockEndAt :: Block -> Lexer BlockEnd
blockEndAt b = gets (inpStream . lexerInput) >>= \case
  [] -> pure (FileEnded b)
  _  -> pure (Outdented b)

setBlockKw :: String -> Lexer ()
setBlockKw kw = modify' $ \st -> st { lexerBlockKw = Just kw }

-- | The keyword that opened the block now starting, if one did: the top-level
-- block is opened by seeding the start code instead. Clearing it keeps a
-- keyword whose block never started, an explicit brace following it, from
-- being picked up by a later block.
takeBlockKw :: Lexer (Maybe String)
takeBlockKw = gets lexerBlockKw <* modify' (\st -> st { lexerBlockKw = Nothing })

-- | Record what the offside rule made of line @l@.
setLayoutNote :: Int -> LayoutNote -> Lexer ()
setLayoutNote l n = modify' $ \st -> st { lexerNote = Just (l, n) }

-- | What the offside rule made of line @l@, if anything worth reporting.
layoutNoteAt :: Int -> Lexer (Maybe LayoutNote)
layoutNoteAt l = gets lexerNote >>= \case
  Just (l', n) | l == l' -> pure (Just n)
  _                      -> pure Nothing

incCounter :: Lexer Int
incCounter = modify' (\st -> st{counter = succ $ counter st}) >> gets counter

initState :: FilePath -> String -> LexerState
initState f s = LS { lexerInput      = Input 1 1 '\n' s f
                   , lexerStartCodes = 0 NE.:| []
                   , lexerLayout     = []
                   , lexerNote       = Nothing
                   , lexerBlockKw    = Nothing
                   , counter         = 0
                   }

emit :: (Span -> String -> Token) -> String -> Lexer Token
emit t a = do 
  Input{inpLine=l, inpColumn=c, inpFile=f} <- gets lexerInput
  return (t Span{startPos=(l,c - length a), endPos=(l,c), filepath=f} a)

token :: (Span -> Token) -> String -> Lexer Token
token t s = do 
  Input{inpLine=l, inpColumn=c, inpFile=f} <- gets lexerInput
  return (t Span{startPos=(l,c - length s), endPos=(l,c), filepath=f})

-- | Lexes a string literal from just after its opening quote.
stringLit :: String -> Lexer Token
stringLit _ = stringBody 1 (concatMap (either id pure))

-- | Lexes a multi-line string literal from just after its opening @"""@,
-- turns its line breaks into @\\n@, expands the tabs that start its lines, and
-- removes its indentation.
multilineStringLit :: String -> Lexer Token
multilineStringLit _ = stringBody 3 (concatMap (either id pure) . dedent)

-- | Lexes the body of a string literal closed by the given number of quotes,
-- as raw characters (Right) and resolved escapes (Left), and makes a token of
-- the string the given function builds from them.
stringBody :: Int -> ([Either String Char] -> String) -> Lexer Token
stringBody quotes finish = do
  open <- gets lexerInput
  let start = (inpLine open, inpColumn open - quotes)
      body lead inp = case alexGetChar inp of
        Just ('"', inp')
          | quotes == 1 -> return ([], inp')
          | take 2 (inpStream inp') == "\"\"" -> return ([], skip 2 inp')
        Just ('\\', inp') -> case inpStream inp' of
          '&' : _ -> first (Left "" :) <$> body Nothing (skip 1 inp')
          c : _ | isSpace c -> case alexGetChar (skipSpace inp') of
            Just ('\\', inp'') -> first (Left "" :) <$> body Nothing inp''
            _ -> invalidEscape inp
          s | Just (c, n) <- escape s -> first (Left [c] :) <$> body Nothing (skip n inp')
            | otherwise -> invalidEscape inp
        Just (c, inp') | quotes == 3, c `elem` "\n\r\f" ->
          first (Right '\n' :) <$> body (Just 0) (case inpStream inp' of
            '\n' : _ | c == '\r' -> skip 1 inp'
            _ -> inp')
        Just ('\t', inp') | Just col <- lead ->
          let n = nextTabStop (col + 1) - col - 1
          in first (replicate n (Right ' ') ++) <$> body (Just (col + n)) inp'
        Just (c, inp') | not (isControl c) ->
          first (Right c :) <$> body (if isSpace c then (+ 1) <$> lead else Nothing) inp'
        Just (c, inp') | c /= '\n' -> controlChar inp inp' c
        _ -> throwError [UnterminatedString (spanFrom start open) (replicate quotes '"')]
  (ps, inp) <- body (if quotes == 3 then Just 0 else Nothing) open
  modify' $ \st -> st { lexerInput = inp }
  return (TkStringLit (spanFrom start inp) (finish ps))

-- | Removes the indentation common to all lines but the first, empties lines
-- of whitespace, and drops a newline right after the opening and right before
-- the closing delimiter.
dedent :: [Either String Char] -> [Either String Char]
dedent ps = reverse (dropNewline (reverse (dropNewline (intercalate [Right '\n'] (strip l : map (drop n . strip) ls)))))
  where
    l : ls = foldr (\p acc@(x : xs) -> if p == Right '\n' then [] : acc else (p : x) : xs) [[]] ps
    white = either (const False) isSpace
    strip x = if all white x then [] else x
    n = minimum (maxBound : [length (takeWhile white x) | x <- ls, not (all white x)])
    dropNewline (Right '\n' : xs) = xs
    dropNewline xs = xs

charLit :: String -> Lexer Token
charLit _ = do
  open <- gets lexerInput
  let invalid :: AlexInput -> Lexer a
      invalid inp = throwError [InvalidCharLit (spanFrom (quoteAt open) inp)]
  (c, inp) <- case alexGetChar open of
    Just ('\\', inp)
      | Just (c, n) <- escape (inpStream inp) -> return (c, skip n inp)
      | otherwise -> invalidEscape open
    Just (c, inp) | c /= '\'' && not (isControl c) -> return (c, inp)
    Just (c, inp) | c /= '\n' -> controlChar open inp c
    _ -> invalid open
  case alexGetChar inp of
    Just ('\'', inp') -> do
      modify' $ \st -> st { lexerInput = inp' }
      return (TkCharLit (spanFrom (quoteAt open) inp') c)
    _ -> invalid inp

-- | The character an escape denotes, given the text after its backslash, and
-- the number of characters it takes.
escape :: String -> Maybe (Char, Int)
escape s = case s of
  c : _ | Just e <- lookup c (zip "abfnrtv\\\"'" "\a\b\f\n\r\t\v\\\"'") -> Just (e, 1)
  '^' : c : _ | c >= '@' && c <= '_' -> Just (chr (ord c - ord '@'), 2)
  'x' : ds -> number 16 isHexDigit ds 1
  'o' : ds -> number 8 isOctDigit ds 1
  _ | Just (name, e) <- find ((`isPrefixOf` s) . fst) asciiEscapes -> Just (e, length name)
    | otherwise -> number 10 isDigit s 0
  where
    asciiEscapes = zip (words "NUL SOH STX ETX EOT ENQ ACK BEL BS HT LF VT FF CR SO SI DLE DC1 DC2 DC3 DC4 NAK SYN ETB CAN EM SUB ESC FS GS RS US SP") ['\NUL' ..]
      ++ [("DEL", '\DEL')]
    number base isD ds k = case takeWhile isD ds of
      [] -> Nothing
      n | v <= toInteger (ord maxBound) -> Just (chr (fromInteger v), k + length n)
        | otherwise -> Nothing
        where v = foldl (\a d -> a * base + toInteger (digitToInt d)) 0 n

invalidEscape :: AlexInput -> Lexer a
invalidEscape Input{inpLine=l, inpColumn=c, inpStream=s, inpFile=f} =
  throwError [InvalidEscape Span{startPos=(l, c), endPos=(l, c + length e), filepath=f} e]
  where
    e = '\\' : case drop 1 s of
      d : ds | isDigit d -> d : takeWhile isDigit ds
      'x' : ds -> 'x' : takeWhile isHexDigit ds
      'o' : ds -> 'o' : takeWhile isOctDigit ds
      d : _ | not (isSpace d) -> [d]
      _ -> ""

controlChar :: AlexInput -> AlexInput -> Char -> Lexer a
controlChar inp inp' ch =
  throwError [ControlCharInLiteral (spanFrom (inpLine inp, inpColumn inp) inp') ch]

quoteAt :: AlexInput -> Pos
quoteAt Input{inpLine=l, inpColumn=c} = (l, c - 1)

spanFrom :: Pos -> AlexInput -> Span
spanFrom p Input{inpLine=l, inpColumn=c, inpFile=f} = Span{startPos=p, endPos=(l, c), filepath=f}

skip :: Int -> AlexInput -> AlexInput
skip n inp = iterate (\i -> maybe i snd (alexGetChar i)) inp !! n

skipSpace :: AlexInput -> AlexInput
skipSpace inp = case alexGetChar inp of
  Just (c, inp') | isSpace c -> skipSpace inp'
  _ -> inp

runLexer :: Lexer a -> FilePath -> String -> Either [Error] a
runLexer act f s = fst <$> runStateT (_getLexer act) (initState f s)
