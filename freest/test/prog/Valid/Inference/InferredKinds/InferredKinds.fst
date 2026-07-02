module InferredKinds where

id' : forall a -> a -> a
id' @a x = x

dot : forall a b c -> (b -> c) -> (a -> b) -> a -> c
dot @a @b @c f g x = f (g x)

inc : Int -> Int
inc x = x + 1

main : ()
main = print (dot @Int @Int @Int inc inc (id' @Int 40))
