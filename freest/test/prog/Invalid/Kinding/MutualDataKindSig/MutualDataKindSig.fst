module MutualDataKindSig where

-- Mutually recursive datatypes without a kind signature are not yet inferrable
-- (the multiplicity of one depends cyclically on the other); a signature is
-- required. Self-recursive and non-recursive datatypes are inferred.
data A = MkA (!Int ; Close) B
data B = MkB A

main : ()
main = ()
