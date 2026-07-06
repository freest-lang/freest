module PartialAppliedLinFun where

f : Int -1-> Int -*-> Int
f x y = x + y

partialLinApplication : ()
partialLinApplication = 
    let g = f 1 in print (g 3 + g 1 + g 2)