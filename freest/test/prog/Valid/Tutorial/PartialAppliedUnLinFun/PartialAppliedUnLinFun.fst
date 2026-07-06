module PartialAppliedUnLinFun where

f : Int -*-> Int -1-> Int
f x y = x + y

partialUnApplication : ()
partialUnApplication = 
    let g1 = f 1
        g2 = f 2 in
    print (g1 3 + g2 4)