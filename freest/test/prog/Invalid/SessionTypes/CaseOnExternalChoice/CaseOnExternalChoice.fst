module CaseOnExternalChoice where

f : +{A: Skip} -> Int
f c = case c of &A _ -> 5
