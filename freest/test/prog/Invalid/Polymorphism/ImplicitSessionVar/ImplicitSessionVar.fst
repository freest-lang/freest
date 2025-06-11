module ImplicitSessionVar where

f : Close *-> ()
f = \(c1 : Close) (x : ()) -> close c1