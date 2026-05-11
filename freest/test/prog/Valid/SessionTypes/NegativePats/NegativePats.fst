module NegativePats where

foo : &{A: ?type (a : *T). ?Bool; ?a, B: Skip} -> ()
foo (&A (?@a. ?True ; ?x; _)) = ()
foo (&A (?@a. ?False; ?x; _)) = ()
foo (&B _)             = ()