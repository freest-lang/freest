module Hungry where

-- Types and Programming Languages, Benjamin Pierce, Page 270

type Hungry : *T
type Hungry = Int -> Hungry
 
f : Int -> Hungry
f n = f

g : Hungry
g = f 0 1 2 3 4 5

