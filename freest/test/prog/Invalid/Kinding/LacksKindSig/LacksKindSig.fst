module LacksKindSig where

-- Type-declaration kinds are inferred, but datatype declarations still require
-- an explicit kind signature.
data Foo = Bar Int
