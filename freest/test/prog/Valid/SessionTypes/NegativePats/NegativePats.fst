module NegativePats where

foo : &{A: ?type (a : *T). ?Bool; ?a, B: Skip} -> ()
foo (&A (?type (a : *T). ?True ; ?x; _)) = ()
foo (&A (?type (a : *T). ?False; ?x; _)) = ()
foo (&B _)             = ()