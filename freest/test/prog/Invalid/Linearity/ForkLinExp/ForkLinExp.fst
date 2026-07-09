main : ()
main = fork @(Close, Wait) (\(_ : ()) -1-> channel @Close)
