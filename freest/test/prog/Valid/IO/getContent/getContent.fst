-- | Reads the entire content from an `InStream` (i.e. until EOF is reached).
hGetContent : InStream -> (String, InStream)
hGetContent c = 
  let (isEOF, c) = hIsEOF c in
  if isEOF
  then ("", c)
  else 
    let (line,     c) = hGetLine c in 
    let (contents, c) = hGetContent c in
    (line ++ "\n" ++ contents, c)

_ =
  let (str, instream) = stdin |> receive_ |> hGetContent in
  hCloseIn instream;
  print str