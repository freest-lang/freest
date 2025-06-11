module InvalidInChoice where

fun : &{L1: !Int} -> Int
fun c = select L1 c
