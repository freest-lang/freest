module InPat where

foo : ?Int -> (Int, Skip)
foo (?n; s) = (n, s)