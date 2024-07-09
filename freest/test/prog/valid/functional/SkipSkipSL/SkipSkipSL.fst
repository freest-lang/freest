module SkipSkipSL where

f : Skip;Skip;Close -> Int
f x = close x; 1

main : Int
main = 
    let (c, s) = channel @(Skip;Skip;Close) in
    fork (\_:() 1-> wait s);
    f c
