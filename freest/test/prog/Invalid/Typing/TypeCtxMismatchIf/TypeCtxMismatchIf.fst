module TypeCtxMismatchIf where

bar : Int -> Close -> ()
bar n c = if n > 0 then close c else ()
