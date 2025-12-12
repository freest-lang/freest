module WaitOnClose where

foo : Close -> ()
foo c = wait c