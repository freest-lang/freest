module LSP.Util
  ( buildDiagnostic,
    originRange,
    originPosition,
    isPositionInsideRange,
    isRangeInsideRange,
  )
where

import Data.Text
import Language.LSP.Diagnostics
import Language.LSP.Protocol.Types

originRange :: Range
originRange = Range originPosition originPosition

originPosition :: Position
originPosition = Position 0 0

isPositionInsideRange :: Position -> Range -> Bool
isPositionInsideRange
  (Position l c)
  (Range (Position l1 c1) (Position l2 c2)) =
    l1 <= l && l <= l2 && c1 <= c && c <= c2

isRangeInsideRange :: Range -> Range -> Bool
isRangeInsideRange
  (Range (Position l1 c1) (Position l2 c2))
  (Range (Position l1' c1') (Position l2' c2')) =
    l1' <= l1 && l2 <= l2' && c1' <= c1 && c2 <= c2'

buildDiagnostic :: String -> Range -> Diagnostic
buildDiagnostic msg range =
  Diagnostic
    range
    (Just DiagnosticSeverity_Error)
    Nothing
    Nothing
    (Just (pack "freest-lsp"))
    (pack msg)
    Nothing
    Nothing
    Nothing
