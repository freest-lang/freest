{-
Benjamin C. Pierce:
Types and programming languages. MIT Press 2002
-}

type IntRef : *C
type IntRef = *?IntRefSession

type IntRefSession : 1C
type IntRefSession = +{Read: ?Int, Write: !Int} ; Close

write : Int -> IntRef -> ()
write x r = r |> receive_ |> select Write |> sendAndClose x

read : IntRef -> Int
read r = r |> receive_ |> select Read |> receiveAndClose

intRef : Int -> IntRef
intRef x = forkWith (handle x)
  where
    handle : Int -> Dual IntRef -> ()
    handle x r = case accept r of
      &Write s -> handle (receiveAndWait s) r
      &Read  s -> sendAndWait x s; handle x r

type MCounter : *T
type MCounter = (exists a, (() -> a, a -> Int, a -> ()))

mCounterADT : MCounter
mCounterADT = (@IntRef, ( \_     -> intRef 0                -- new
                        , \x -> read x                  -- get
                        , \x -> write (succ (read x)) x -- inc
                        )
              ) 
            : MCounter

main : ()
main = inc x; print (get x)
  where
    (@c, (new, get, inc)) = mCounterADT
    x = new ()
