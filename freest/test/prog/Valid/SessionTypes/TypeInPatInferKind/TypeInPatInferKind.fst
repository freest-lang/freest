{- Type-input pattern with the binder kind omitted: `?type a.` (not
   `?type (a : *T).`). The kind is inferred from the session's binder kind. -}
module TypeInPatInferKind where

foo : (?type (a : *T). Skip) -> Skip
foo (?type a. s) = s
