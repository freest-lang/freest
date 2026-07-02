{- A `?type` binder defaults to the most-general `1T` (the `∀` default, since
   `?type ≅ ∀`). This program discards the received value `?a`, which needs
   `a : *T`. Passes today only with the annotation `?type (a : *T)`. -}
module ReceiveDiscard where

type Chan : 1S
type Chan = ?type a. ?a ; Skip

server : Chan -> ()
server c =
  let (@a, c) = receiveType c
      (_, c) = receive c
  in ()
