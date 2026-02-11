module MatchOnInternalChoice where

foo : +{A: Skip, B: Skip} -> ()
foo c = 
  case c of
    &A _ -> ()
    &B _ -> ()