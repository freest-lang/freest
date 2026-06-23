module ReceiveTypePatOnTypeOutChannel where

foo : (!type (a : *T). Skip) -> ()
foo (?type a. _) = ()