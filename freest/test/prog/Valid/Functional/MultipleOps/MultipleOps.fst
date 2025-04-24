module MultipleOps where

a : Int
a = -5 + 8 * 6

b : Int
b = rem (55+9) 9

c : Int
c = 20 + (div (-3 * 5) 5)

d : Int
d = 5 + (div 15 3) * 2 - (rem 8 3)

main : Int
main = a + b + c + d


