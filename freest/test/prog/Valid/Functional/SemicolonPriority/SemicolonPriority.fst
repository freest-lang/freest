module SemicolonPriority where

main : ()
main = 1 + 1; ()

g : ()
g = 1 - 1; ()

h : ()
h = 1 * 1; ()

i : ()
i = 1 / 1; ()

j : ()
j = True && False; ()

k : ()
k = True || False; ()

l : Int -> Int
l n = id; n

m : Int -> Int 
m n = id $ True; 1
