-- Composition joins the multiplicities of what it composes: `plusTwo` is
-- unrestricted, `sendPlusTwo` linear, capturing the channel end `o`.
main : ()
main =
  let plusTwo = succ . succ
      (o, i) = channel @(!Int; Close)
      sendPlusTwo = close . (flip send o) . plusTwo
  in sendPlusTwo 0;
     print (receiveAndWait i)
