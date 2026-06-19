module TypeNameInSig where

type F : *T
type F = Int -> Int

f : F
f x = x + x

main : ()
main = print (f 6)
