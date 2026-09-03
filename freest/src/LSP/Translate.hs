module LSP.Translate
  ( errorTypeToDiagnostic,
    spanToRange,
  )
where

import LSP.Util (buildDiagnostic)
import Language.LSP.Protocol.Types
import Syntax.Base (Located (getSpan), Pos, Span (endPos, startPos))
import UI.CLI (RunOpts)
import UI.Error (Error, Source, toMessage)

errorTypeToDiagnostic :: Source -> RunOpts -> Error -> Diagnostic
errorTypeToDiagnostic s runOpts err =
  buildDiagnostic
    (toMessage s err)
    (spanToRange $ getSpan err)

posToPosition :: Pos -> Position
posToPosition (line, column) =
  Position
    (fromIntegral (max 0 (line - 1)))
    (fromIntegral (max 0 (column - 1)))

spanToRange :: Span -> Range
spanToRange s =
  Range (posToPosition (startPos s)) (posToPosition (endPos s))
