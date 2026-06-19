module TypeInAndVar where

foo : (?type (a : *T). Skip) -> Skip
foo (?type (a : *T). s) = s
foo c = let (@(a : *T), s) = receiveType c in s