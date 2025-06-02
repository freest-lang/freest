module FstSend where

fst' : forall (a : 1T) (b : *T). (a, b) -> a
fst' @a @b p = let (x, _) = p in x

snd' : forall (a : *T) (b : 1T). (a, b) -> b
snd' @a @b p = let (_, y) = p in y

main : Int
main = fst' @Int @Char (5, 'h') + snd' @Bool @Int (True, 7)
