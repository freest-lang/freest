module MutualDataKinds where

-- Three mutually recursive datatypes with no signatures. The complete
-- multiplicity unifier plus the SCC least fixpoint infer the whole group as
-- `*T` (no field forces linearity); before the fix the solver rejected this
-- group outright. Being `*T`, a constructed value may be discarded.
data Aa = MkA Int Bb
data Bb = MkB Cc
data Cc = MkC Aa | CEnd

main : ()
main =
  let a = MkA 5 (MkB CEnd) in
  print 8
