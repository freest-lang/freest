module TypeInPat where

foo : (?type (a : *T). Skip) -> Skip
foo (?type (a : *T). s) = s