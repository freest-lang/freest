module ReceiveTypePatOnTypeOutChannel where

foo : (!!(a : *T). Skip) -> ()
foo (??a. _) = ()