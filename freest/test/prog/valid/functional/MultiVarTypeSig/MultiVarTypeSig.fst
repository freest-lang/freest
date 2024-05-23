module MultiVarTypeSig where

x, y, z : Int
x = 1
y = 2
z = 3

double, triple : Int -> Int
double n = n * 2
triple n = n * 3

main : Int
main = double x + triple y + z