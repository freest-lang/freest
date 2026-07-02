module NegativePats where

foo : &{A: ?type (a : *T). ?Bool; ?a, B: Skip} -> ()
foo (&A (?type a. ?True ; ?x; _)) = ()
foo (&A (?type a. ?False; ?x; _)) = ()
foo (&B _)             = ()