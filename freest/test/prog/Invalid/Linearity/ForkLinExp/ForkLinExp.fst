module ForkLinExp where

main : ()
main = fork @(Close, Wait) (\(_ : ()) -1-> channel @Close)
