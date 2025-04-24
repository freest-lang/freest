module ImplicitForall where

id' : a -> a 
id' x = x 

const' : a -> forall b . b -> a 
const' x y = x 

main : ()
main = id' @() (const' @() () @Int 0) 
