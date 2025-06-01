module SendList where

type List : *T
data List = Cons Int List | Nil

type ListC : 1C
type ListC = &{NilC: Wait, ConsC: ?Int ; ListC}

read : ListC -> List
read (&ConsC c) =
  let (x, c) = receive @Int @ListC c in
  Cons x (read c)
read (&NilC c) = 
  let _ = wait c in 
  Nil

write : List -> Dual ListC -> ()
write (Cons x xs) c =
  write xs (send @Int x @(Dual ListC) (select ConsC c))
write Nil c =
  close (select NilC c)

aList, main : List

aList = Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil)))
main = read (forkWith @ListC @() (write aList))

