module ReceiveTypePatOnTypeOutChannel where

foo : (!type (a : *T). Skip) -> ()
foo (?@a. _) = ()