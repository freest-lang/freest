module TypeInPat where

foo : (?type (a : *T). Skip) -> Skip
foo (?@(a : *T). s) = s