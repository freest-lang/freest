-- https://learnyouahaskell.github.io/input-and-output.html#hello-world

main : () -> ()
main () =
    let c = getChar () in
    if ord c /= 32 
    then putChar c ; main ()
    else ()

_ = main ()