{-
Benjamin C. Pierce:
Types and programming languages. MIT Press 2002
-}

module MCounter where

type IntRef : *C
type IntRef = *?IntRefSession

type IntRefSession : 1C
type IntRefSession = +{Read: ?Int, Write: !Int} ; Close

write : Int -> IntRef -> ()
write x r = r |> receive_ @IntRefSession |> select Write |> sendAndClose @Int x

read : IntRef -> Int
read r = r |> receive_ @IntRefSession |> select Read |> receiveAndClose @Int

intRef : Int -> IntRef
intRef x = forkWith @IntRef @() (handle x)
  where
    handle : Int -> Dual IntRef -> ()
    handle x r = case accept @IntRefSession r of
      &Write s -> handle (receiveAndWait @Int s) r
      &Read  s -> sendAndWait @Int x s; handle x r

type MCounter : *T
type MCounter = exists (a : *T) . (() -> a, a -> Int, a -> ())

mCounterADT : MCounter
mCounterADT = (@IntRef, ( \(_ : ())     -> intRef 0                -- new
                        , \(x : IntRef) -> read x                  -- get
                        , \(x : IntRef) -> write (succ (read x)) x -- inc
                        )
              ) 
            : MCounter

main : Int
main = inc x; get x
  where
    (@(c : *T), (new, get, inc)) = mCounterADT
    x = new ()