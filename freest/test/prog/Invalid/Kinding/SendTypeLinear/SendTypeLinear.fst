{- A `!type` binder bounds the type sent through it, as an existential's binder
   bounds the packed witness. Without that, a linear type travels through an
   unrestricted binder and the receiver at the dual `?type` may discard it —
   which `server` does here. -}
type Chan : 1S
type Chan = !type a. !a ; Skip

client : Chan -> Skip
client c = c |> sendType @(Int -1-> Int) |> send (\(x:Int) -1-> x)

server : Dual Chan -> ()
server c = let (@a, c) = receiveType c
               (_, c) = receive c
           in ()

main : ()
main = ()
