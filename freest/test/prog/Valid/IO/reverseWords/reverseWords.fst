-- https://learnyouahaskell.github.io/input-and-output.html#hello-world

reverseWords : String -> String  
reverseWords = unwords . map reverse . words  

main : () -> ()
main () =
  let line = getLine () in
  if null line  
  then ()
  else
    putStrLn $ reverseWords line ;
    main ()

_ = main ()