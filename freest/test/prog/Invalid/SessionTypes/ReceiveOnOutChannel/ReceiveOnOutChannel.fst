module ReceiveOnOutChannel where

f : !Int -> (Int, Skip)
f c = receive c

