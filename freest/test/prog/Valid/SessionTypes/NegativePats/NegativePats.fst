module NegativePats where

foo : &{A: ?type (a : *T). ?Bool; ?a, B: Skip} -> ()
foo (&A (?@(a : *T). ?True ; ?x; _)) = ()
foo (&A (?@(a : *T). ?False; ?x; _)) = ()
foo (&B _)             = ()