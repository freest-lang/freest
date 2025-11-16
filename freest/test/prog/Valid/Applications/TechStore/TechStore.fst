module TechStore where

---------------------------------- SharedCounter ----------------------------------

type Counter : *C
type Counter = *?Int

runCounter : Int -> Dual Counter -> ()
runCounter i counter =
  send_ @Int i counter;
  runCounter (i + 1) counter

initCounter : Counter
initCounter = 
  forkWith @Counter @() (\(ch : *!Int) 1-> runCounter 0 ch)

---------------------------------- SharedQueue ----------------------------------

{- channel types -}

-- type Head : *S = {- Dequeue -} *?Int
-- type Tail : *S = {- Enqueue -} dualof Head

-- type Internal = ?Int; ?Internal

{- nodes -}

type T : *T -> 1C
type T a = ?a; ?(T a); Wait

runHeadNode : forall (a : *T). T a -> Dual *?a 1-> ()
runHeadNode @a prev head = 
  -- receive value |> next node endpoint
  let (i, prev) = receive prev in
  let (prev', prev) = receive prev in
  wait prev;
  -- send value to client
  send_ @a i head;
  -- run node with new endpoint
  runHeadNode @a prev' head

runTailNode : forall (a : *T). Dual (T a) -> Dual *!a 1-> ()
runTailNode @a next tail =
  let i = receive_ @a tail in
  let next' = forkWith @(Dual (T a)) @()
                (\(c : T a) 1-> send i next |> send c |> close) in
  runTailNode @a next' tail 

{- queue -}     

initQueue : forall (a : *T). () -> (*?a, *!a)
initQueue @a _ =
  let (internalC, internalS) = channel @(T a) in
  ( forkWith @(*?a) @() (runHeadNode @a internalC)
  , forkWith @(*!a) @() (runTailNode @a internalS)
  )

enqueue : forall (a : *T). a -> (*?a, *!a) 1-> ()
enqueue @a i queue = 
  send_ @a i $ snd @*?a @*!a queue

dequeue : forall (a : *T). (*?a, *!a) -> a
dequeue @a queue = 
  receive_ @a $ fst @*?a @*!a queue

---------------------------------- SharedList ----------------------------------

{- list structure (while there's no native one) -}
type List : *T
data List = Nil 
          | Cons (ProductId, Issue, RmaNumber) List

{- channel types -}

type SharedList : *C
type SharedList = *?ListC

type ListC : 1C
type ListC = +{ Append: !ProductId; !Issue; !RmaNumber; ListC
              , Stop: Close  
              }

{- list server -}

runListService : List -> Dual ListC 1-> List
runListService list ch = 
  case ch of
    &Append ch -> 
      let (productId, ch) = receive ch in
      let (issue    , ch) = receive ch in
      let (rmaNumber, ch) = receive ch in
      -- logging
      receive_ @OutStream stdout
      |> hPutStr "RMA processed \t\t @ product id: "
      |> hPutStr (show @Int productId)
      |> hPutStr ", issue: "
      |> hPutStr issue
      |> hPutStr ", RMA id: "
      |> hPutStrLn (show @Int rmaNumber)
      |> hCloseOut;
      --
      runListService (Cons (productId, issue, rmaNumber) list) ch
    &Stop c ->
      wait c; 
      list

runListServer : Dual SharedList 1-> ()
runListServer ch =
    runServer @ListC @List runListService Nil ch


initList : SharedList
initList = forkWith @SharedList @() runListServer

{- client functions -}

append : SharedList -> (ProductId, Issue, RmaNumber) -> ()
append ch (productId, issue, rmaNumber) =
  receive_ @ListC ch
  |> select Append
  |> send productId
  |> send issue
  |> send rmaNumber
  |> select Stop
  |> close 

---------------------------------- SharedMap ----------------------------------

{- types for the map (while there's no type ops) -}

type ProductName, Amount, Price : *T
type ProductName = Char
type Amount      = Int
type Price       = Int

{- map structure -}

type Map : *T
data Map = Empty 
         | Entry ProductName (Amount, Price) Map

type MaybeValue : *T
data MaybeValue = NothingValue | JustValue (Amount, Price)

mapPut : ProductName -> (Amount, Price) -> Map -> Map
mapPut pName val map =
  case map of
    Empty -> Entry pName val Empty
    Entry pName' val' map' ->
      if ord pName == ord pName'
      then
        -- if already exist, replace value 
        Entry pName' val map'
      else
        -- else, recur
        Entry pName' val' $ mapPut pName val map'

mapGet : ProductName -> Map -> MaybeValue
mapGet pName map =
  case map of
    Empty -> NothingValue
    Entry pName' val' map' ->
      if ord pName == ord pName'
      then JustValue val'
      else mapGet pName map'

mapHas : ProductName -> Map -> Bool
mapHas pName map = 
  case map of
    Empty -> False
    Entry pName' _ map' ->
      if ord pName == ord pName'
      then True
      else mapHas pName map'

isNothing : MaybeValue -> Bool
isNothing maybeVal =
  case maybeVal of
    JustValue _  -> False
    NothingValue -> True

fromJustOrDefault :  (Amount, Price) -> MaybeValue -> (Amount, Price)
fromJustOrDefault default maybeVal =
  case maybeVal of 
    JustValue val -> val
    NothingValue -> default

{- channel types -}

type SharedMap : *S
type SharedMap = *?MapC

type MapC : 1C
type MapC = +{ Put: !ProductName; ValueC     ; MapC
             , Get: !ProductName; MaybeValueC; MapC
             , Stop: Close
             }

type ValueC : 1S
type ValueC = !Amount; !Price

type MaybeValueC : 1S
type MaybeValueC = &{ JustVal: Dual ValueC
                    , NothingVal: Skip
                    }

{- map server -}

runMapService : Map -> Dual MapC 1-> Map
runMapService map ch =
  case ch of
    &Put ch ->
      let (pName , ch) = receive ch in
      let (amount, ch) = receive ch in
      let (price , ch) = receive ch in
      runMapService (mapPut pName (amount, price) map) ch
    &Get ch -> 
      let (pName , ch) = receive ch in
      let maybeVal = mapGet pName map in
      let ch = case maybeVal of
                  NothingValue  -> select NothingVal ch
                  JustValue val -> 
                    let (amount, price) = val in
                    select JustVal ch |> 
                    send amount |>
                    send price in 
      runMapService map ch
    &Stop ch -> 
      wait ch; 
      map

runMapServer : Map -> dualof SharedMap 1-> ()
runMapServer map ch = 
    runServer @MapC @Map runMapService map ch

initMapWith : Map -> SharedMap
initMapWith map = forkWith @SharedMap @() (runMapServer map)

{- client functions -}

putLin : ProductName -> (Amount, Price) -> MapC 1-> MapC
putLin pName val ch = 
  let (amount, price) = val in
  select Put ch
  |> send pName
  |> send amount
  |> send price

getLin : ProductName -> MapC 1-> (MaybeValue, MapC)
getLin pName ch =
  let ch = select Get ch |> 
           send pName in
  case ch of
    &JustVal ch -> 
      let (amount, ch) = receive ch in
      let (price, ch)  = receive ch in
      (JustValue (amount, price), ch)
    &NothingVal ch -> 
      (NothingValue, ch)

---------------------------------- Bank ----------------------------------

{- channel types -}

type Bank : *S
type Bank = *?BankService

type BankService : 1C
type BankService = {- CreatePayment: -} !Price; ?PaymentC; Close 

type PaymentC : 1C
type PaymentC = !CCNumber; !CCCode; Close 

{- bank worker -}

-- TODO: Expand this function
-- | Executes a function
runWith : forall (a : 1S). (Dual a 1-> ()) -> a
runWith @a f =
  let (c, s) = new @a () in
  f s;
  c

runPayment : Price -> Dual PaymentC -> ()
runPayment price ch =
  -- mock up 
  let (ccnumber, ch) = receive ch in
  let cccode = receiveAndWait @Int ch in 
  -- logging
  receive_ @OutStream stdout
  |> hPutStr "Payment processed \t @ amount: "
  |> hPutStr (show @Int price)
  |> hPutStr ", credit card: "
  |> hPutStr (show @Int ccnumber)
  |> hPutStr ", credit card code: "
  |> hPutStrLn (show @Int cccode)
  |> hCloseOut


runBankService : () -> Dual BankService 1-> ()
runBankService _ ch =
  let (price, ch) = receive ch in
  runWith @(Dual PaymentC) (\(c : PaymentC) 1-> send c ch |> wait)
  |> runPayment price

bankWorker : Dual Bank -> ()
bankWorker =
  runServer @BankService @() (runBankService) ()


initBank : Bank
initBank = 
  -- runWith [Bank] $
  --     \bank:dualof Bank 1-> parallel 3 (bankWorker bank)
  let (c, s) = channel @Bank in
  parallel @() 2 (\(_ : ()) -> bankWorker s);
  c

{- client functions -}

createPayment : Price -> Bank -> PaymentC
createPayment price bank =
  let ch = receive_ @BankService bank in
  let (p, ch) = receive $ send price ch in
  close ch; p


---------------------------------- Tech Store ----------------------------------

type ProductId, Issue, RmaNumber : *T
type ProductId = Int
type Issue = String
type RmaNumber = Int

type CCNumber, CCCode : *T
type CCNumber = Int
type CCCode = Int

{- channel types -}

type TechStore : *S
type TechStore   = *?TechService

type TechService : 1C
type TechService = +{ Buy: ?BuyC
                    , Rma: ?RmaC
                    };Close 

type BuyC, RmaC : 1C
type BuyC = !ProductName; AvailabilityC
type RmaC = !ProductId; !Issue; ?RmaNumber; Close  

type AvailabilityC, CheckoutC : 1C
type AvailabilityC = &{ Available : ?Price; CheckoutC
                      , OutOfStock: Wait 
                      }

type CheckoutC = +{ Confirm: ?PaymentC; Close 
                  , Cancel : Close
                  }


{- store front -}
type BuyQueue, RmaQueue : 1T
type BuyQueue = (*?(Dual BuyC), *!(Dual BuyC))
type RmaQueue = (*?(Dual RmaC), *!(Dual RmaC))

runStoreFront : BuyQueue -> RmaQueue -> Dual TechStore 1-> ()
runStoreFront buyQueue rmaQueue store =
  (case accept @TechService store of
    &Buy ch ->
      let (c, s) = channel @BuyC in
      send c ch |> wait;
      enqueue @(Dual BuyC) s buyQueue
    &Rma ch ->
      let (c, s) = channel @RmaC in
      send c ch |> wait;
      enqueue @(Dual RmaC) s rmaQueue);
      -- enqueue [dualof RmaC] (fst [dualof RmaC, Skip] (accept [RmaC, Skip] ch)) rmaQueue
  runStoreFront buyQueue rmaQueue store

{- buy workers -}


getFromStock : ProductName -> SharedMap -> MaybeValue
getFromStock pName map =
  -- get map access
  let mapS = receive_ @MapC map in
  -- get from map
  let (maybeVal, mapS) = getLin pName mapS in
  -- 
  (case maybeVal of
      NothingValue -> mapS
      JustValue val -> 
        let (amount, price) = val in
        if amount > 0
        -- if stock > 0, decrement stock (reserves it)
        then putLin pName (amount-1, price) mapS
        -- if no stock, nothing
        else mapS) |> select Stop |> close;
  maybeVal

returnToStock : ProductName -> SharedMap -> ()
returnToStock pName map =
  -- get map access
  let mapS = receive_ @MapC map in
  -- get from map
  let (maybeVal, mapS) = getLin pName mapS in
  (case maybeVal of
      NothingValue -> mapS
      JustValue val -> 
          let (amount, price) = val in
          putLin pName (amount+1, price) mapS
  ) |> select Stop |> close 

buyWorker : BuyQueue -> SharedMap -> Bank -> ()
buyWorker buyQueue map bank = 
  let ch = dequeue @(Dual BuyC) buyQueue in
  --
  let (pName, ch) = receive ch in
  -- (try to) reserve from stock
  let (amount, price) = fromJustOrDefault (0, 0) $ getFromStock pName map in
  if amount < 1
  then select OutOfStock ch |> close 
  else
      let ch = select Available ch |> send price in
          (case ch of
              &Confirm ch -> send (createPayment price bank) ch |> wait
              &Cancel ch  -> wait ch; returnToStock pName map)
  ;
  --
  buyWorker buyQueue map bank

{- rma workers -}

rmaWorker : RmaQueue -> Counter -> SharedList -> ()
rmaWorker rmaQueue counter rmaList =
  let ch = dequeue @(Dual RmaC) rmaQueue in
  --
  let (productId, ch) = receive ch in
  let (issue    , ch) = receive ch in
  let rmaNumber = receive_ @Int counter in
  append rmaList (productId, issue, rmaNumber);
  send rmaNumber ch |> wait ;
  --
  rmaWorker rmaQueue counter rmaList

{- store setup -}

initialStock : Map
initialStock = 
  mapPut 'C' (2, 20) $
  mapPut 'B' (3, 5 ) $
  mapPut 'A' (1, 50) $
  Empty


setupStore : Bank -> TechStore 
setupStore bank =
  -- buy
  let buyQueue = initQueue @(Dual BuyC) () in
  let stockMap = initMapWith initialStock in
  parallel @() 3 (\(_ : ()) -> buyWorker buyQueue stockMap bank);
  -- rma
  let rmaQueue = initQueue @(Dual RmaC) () in
  let counter = initCounter in
  let rmaList = initList in
  parallel @()  1 (\(_ : ()) -> rmaWorker rmaQueue counter rmaList);
  -- store front
  forkWith @TechStore @() $ runStoreFront buyQueue rmaQueue

---------------------------------- Clients ----------------------------------

{- buy clients -}

client0 : TechStore -> ()
client0 ch = 
  let buyC = receive_ @TechService ch -- wait to be served by store
              |> select Buy            -- go to the buy queue
              |> receiveAndClose @BuyC  
              |> send 'A' in 
  case buyC of
    &OutOfStock c ->
      wait c; 
      putStrLn "[Client 0] I was unable to buy product 'A'"
    &Available buyC -> 
      let (price, buyC) = receive buyC in
      -- buyer's price limit
      if price > 100 
      then buyC |> select Cancel
                |> close
      else buyC |> select Confirm 
                |> receiveAndClose @(PaymentC; Close)
                |> send 123123123
                |> send 123 
                |> close

{- rma clients -}

client1 : TechStore -> ()
client1 ch = 
  ch |> receive_ @TechService 
      |> select Rma 
      |> receiveAndClose @RmaC 
      |> send 1234567890
      |> send "Monitor flickers when punched"
      |> receiveAndClose @Int; 
  ()

---------------------------------- Main ----------------------------------

{- main -}

diverge : () -> ()
diverge u = diverge u

main : ()
main =
  let bank = initBank in
  let store = setupStore bank in
  fork (\(_ : ()) 1-> client0 store);
  fork (\(_ : ()) 1-> client0 store);
  fork (\(_ : ()) 1-> client1 store);
  diverge ()
