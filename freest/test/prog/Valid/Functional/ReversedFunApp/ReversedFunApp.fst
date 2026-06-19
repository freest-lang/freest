module ReversedFunApp where

f : forall #m #n (a : m T) (b : 1T) -> a -> (a -n-> b) -m-> b
f = (|>)

main : ()
main = print (f 5 (\(x : Int) -> x))
