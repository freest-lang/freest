module IntLinType where

type LinInt : 1T
type LinInt = Int

copy : LinInt -> (LinInt, LinInt)
copy x = (x, x)