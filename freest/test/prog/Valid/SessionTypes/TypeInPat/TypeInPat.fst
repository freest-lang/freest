module TypeInPat where

foo : (??(a : *T). Skip) -> Skip
foo (??a. s) = s