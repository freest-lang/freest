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
import Data.List ( uncons )
import Data.List.NonEmpty qualified as NE
import Data.Char ( ord )
import Control.Monad.State ( gets, modify', MonadState, StateT(..) )
import Control.Monad.Except ( MonadError )

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
            , inpColumn = inpColumn inp + 1
            , inpLast = c
            , inpStream = rest 
            , inpFile = f 
            }
    )

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

runLexer :: Lexer a -> FilePath -> String -> Either [Error] a
runLexer act f s = fst <$> runStateT (_getLexer act) (initState f s)
