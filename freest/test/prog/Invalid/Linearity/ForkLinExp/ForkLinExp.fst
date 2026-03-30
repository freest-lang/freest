module ForkLinExp where

main : ()
main = fork (\(_ : ()) 1-> channel @Close)
