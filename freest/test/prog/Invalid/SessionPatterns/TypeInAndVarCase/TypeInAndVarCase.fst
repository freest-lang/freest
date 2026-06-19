module TypeInAndVarCase where

foo : (?type (a : *T). Skip) -> Skip
foo c = case c of
  ?type (a : *T). s -> s
  c' -> let (@(a : *T), s) = receiveType c' in s
