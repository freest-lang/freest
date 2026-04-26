module EndTwice where

main : ()
main = 
    let (x, y) = channel @Close in
    close x;
    close x;
    wait y
