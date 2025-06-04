module InvalidExtractPair where

extractPair : Bool
extractPair = True

-- invalid extract pair: Expecting a pair type; found Bool
fun : Bool
fun = let (x, y) = extractPair in x

