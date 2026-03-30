module NewSkipForall where

myNew : forall (a : 1C). () -> (a, Dual a)
myNew @a _ = channel @a

main : (Skip, Skip)
main = myNew () -- STRANGE ERROR
