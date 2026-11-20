{- 
A `?type` binder defaults to the most-general `1T` (the `∀` default, since
`?type ≅ ∀`). This program discards the received value `?a`, which needs
`a : *T`. Passes today only with the annotation `?type (a : *T)`.
-}

type Chan : 1S
type Chan = ?type a. ?a ; Skip

server : Chan -> ()
server c =
  let (@a, c) = receiveType c
      (_, c) = receive c
  in ()

{-
Type-threading pattern forcing (item 2, face c).

The forceable binder is the `?type a` (`?type ≅ ∀`, defaults `1T`); it needs `*T`
because the received value is discarded. Learning that requires kinding to walk
the receive pattern against its session type (`Expose`, as `checkPat` does) — the
kinding/typing duplication the fused kinding+typing pass removes (design doc §13,
item 2). Once solved expect empty output.
-}