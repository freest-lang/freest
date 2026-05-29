module CloseSkipEnd where

main : ()
main =
  let (w, v) = channel @(Skip;Close) in
  fork (\(_ : ()) -1-> close w);
  wait v
