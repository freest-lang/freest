module InvalidOutChoice where

fun : +{L1: !Int} -> Int
fun c = case c of &L1 c1 -> let x = send 23 c1 in 23

