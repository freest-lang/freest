-- Ends with a linear channel endpoint in the buffer of a shared channel: the
-- main thread requests a session on a service that no server ever accepts. The
-- integer left in transit on another shared channel is not reported: nothing
-- obliges anyone to receive what is sent on a shared channel.

type Service : *C
type Service = *!(Dual (?Int ; Close))

main : ()
main =
  let (service, _) = channel @Service
      (state, _)   = channel @(*!Int)
      s            = request service in
  send_ 42 state;
  fork (\_ -1-> let (x, s) = receive s in close s; print x);
  putStrLn "done"
