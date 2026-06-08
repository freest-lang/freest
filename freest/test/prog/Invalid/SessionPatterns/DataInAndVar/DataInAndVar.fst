module DataInAndVar where

type D : 1T
data D = D (?Int ; Wait)

f : D -> ()
f (D (?1; Wait)) = ()
f (D c) = c |> receive |> snd |> wait