module FreeST where

import Parser.LexerUtils
import Parser.Lexer 
import Parser.Token 
import Debug.Trace (traceM)
import Control.Monad.RWS
import Utils.CmdLine
import Options.Applicative
import Parser.Parser
import Syntax.Module

main :: IO ()
main = do 
  execParser opts >>= freest 

freest :: RunOpts -> IO ()
freest RunOpts{file=f} = do 
  ans <- runLexer parseModule f <$> readFile f
  case ans of 
    Left s -> error "parse error"
    Right mod -> print mod

lexAll :: Lexer ()
lexAll = do
  tok <- scan
  case tok of
    TkEOF _ -> pure ()
    x -> do
      traceM (show x)
      lexAll