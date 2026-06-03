module RecTypeAndVar where

foo : (?type (a : *T). Skip) -> Skip
foo (?@(a : *T). s) = s
foo c = let (@(a : *T), s) = receiveType c in s