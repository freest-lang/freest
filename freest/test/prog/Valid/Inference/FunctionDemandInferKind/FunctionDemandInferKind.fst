{- An abstraction passed as an argument takes its binder kind from the domain it
   faces in the callee's signature — here `1C`, as `channel` demands — including
   after an explicit type application. An implicit instantiation stays out of
   reach: kinding cannot compute the witness. -}

type Maker = forall (a : 1C) -> (a, Dual a)

use : Maker -> ()
use _ = ()

idm : forall (b : 1T) -> b -> b
idm @b x = x

direct : ()
direct = use (\@a -> channel @a)

viaTypeApp : ()
viaTypeApp = use (idm @Maker (\@a -> channel @a))

main : ()
main = ()
