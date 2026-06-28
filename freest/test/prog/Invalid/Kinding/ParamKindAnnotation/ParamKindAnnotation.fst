module ParamKindAnnotation where

-- A per-parameter kind annotation below the top of its column must be enforced:
-- `C` is `*S -> 1S`, so `C Int` (Int is `*T`) is ill-kinded. Guards against the
-- annotation silently widening to the column top.
type C (a : *S) = !Int ; a
type Bad = C Int

main : ()
main = ()
