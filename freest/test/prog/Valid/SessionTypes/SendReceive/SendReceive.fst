module SendReceive where

client : !Int;?Bool;Close -> Bool 
client c = receiveAndClose @Bool (send @Int 5 @(?Bool;Close) c)

main : ()
main =
  let (w, r)  = channel @(!Int;?Bool;Close) in
  (;) @() @()
    (fork @Bool (\(_ : ()) 1-> client w))
    (let (n, r) = receive @Int @(!Bool;Wait) r in wait (send @Bool (n >= 0) @Wait r))

