{- An omitted `!type` binder defaults to unrestricted (*T), the output-polarity
   twin of a functional existential (both are polarity `Out`, covariant in the
   binder kind). So the abstract value the receiver unpacks at the dual `?type`
   endpoint is freely usable — here discarded — without an annotation. (A
   *linear* sent type is the annotated case `!type (a:1T)`.) Dual to a `?type`
   binder's most-general `1T`, matching forall/exists. -}
module SendTypeDefaultUn where

type Chan : 1S
type Chan = !type a. !a ; Skip

client : Chan -> Skip
client c = c |> sendType @Int |> send 5

server : Dual Chan -> ()
server c =
  let (@a, c) = receiveType c
      (_, c) = receive c            -- discards the abstract value => needs a : *T
  in ()
