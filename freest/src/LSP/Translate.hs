module LSP.Translate
  ( errorTypeToDiagnostic,
    spanToRange,
  )
where

import LSP.Util (buildDiagnostic)
import Language.LSP.Protocol.Types
import Syntax.Base (Located (getSpan), Pos, Span (endPos, filepath, startPos), nextTabStop)
import UI.CLI (RunOpts)
import UI.Error (Error, Source, lookupSrc, toMessage)

errorTypeToDiagnostic :: Source -> RunOpts -> Error -> Diagnostic
errorTypeToDiagnostic s runOpts err =
  buildDiagnostic
    (toMessage s err)
    (spanToRange s $ getSpan err)

-- | LSP counts characters where FreeST counts columns to tab stops.
posToPosition :: [String] -> Pos -> Position
posToPosition ls (line, column) =
  Position
    (fromIntegral (max 0 (line - 1)))
    (fromIntegral (max 0 (charIndex 1 0 (concat (take 1 (drop (line - 1) ls))))))
  where
    charIndex c i (x : s) | c < column = charIndex (if x == '\t' then nextTabStop c else c + 1) (i + 1) s
    charIndex c i [] | c < column = i + column - c
    charIndex _ i _ = i

spanToRange :: Source -> Span -> Range
spanToRange src s =
  Range (posToPosition ls (startPos s)) (posToPosition ls (endPos s))
  where
    ls = lookupSrc src (filepath s)
