module ForkLinExp where

main : ()
main = fork #1 (\(_ : ()) -1-> channel @Close)
