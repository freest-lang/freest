-- `G` is passed where `H` wants a higher-kinded argument, and the two disagree in
-- an arrow *domain*. The unifier flips the sides on its way there, so the mismatch
-- must be reported back in the goal's orientation: `*T` is what `G` accepts, and
-- `*T -> *T` is what `H` requires it to accept.
type H : ((*T -> *T) -> *T) -> *T
type H f = Int

type G (a : *T) = a

type Bad = H G

main : ()
main = ()
