module SharedBag where

-- | The client view of a linear interaction with a bag (multiset) of integer values
type Bag : 1C
type Bag = +{Put: !Int, Get: ?Int}; Close 
  
-- | The client view of a shared interaction with a bag
type SharedBag : *C
type SharedBag = *?Bag

-- | The state of the shared bag: integer messages in transit
type State : *T
type State = (*?Int, *!Int)

-- Server side

-- | Handling a linear interaction with a particular client
handleClient : State -> Dual Bag -> ()
handleClient state chan =
  let (readFromState, writeOnState) = state in
  case chan of
    &Get chan -> let (n, _) = receive readFromState in send n chan |> wait 
    &Put chan -> let _ = send (receiveAndWait @Int chan) writeOnState in ()
    
-- | A shared bag server with a state
bagServer : State -> Dual SharedBag -> Void@*T
bagServer state serverChannel =
  let (clientSide, serverSide) = channel @Bag in
  send clientSide serverChannel;
  fork (\(_ : ()) 1-> handleClient state serverSide);
  bagServer state serverChannel

-- | An empty shared bag
emptyBagServer : Dual SharedBag -> Void@*T
emptyBagServer = bagServer (channel @*?Int)

-- Client side, utilities

-- | Put an integer on a shared bag
put : Int -> SharedBag -> ()
put n q =
  let (c, _) = receive q in
  let c = select Put c in
  send n c |> close

-- | Get an integer from a shared bag
get : SharedBag -> Int
get q =
  let (c, _) = receive q in
  c |> select Get |> receiveAndClose @Int

-- An application

-- | Put three numbers and get two; return the sum
main : Int
main =
  let (clientSide, serverSide) = channel @SharedBag in
  fork (\(_ : ()) 1-> emptyBagServer serverSide);
  fork (\(_ : ()) 1-> put 7 clientSide);
  fork (\(_ : ()) 1-> put 5 clientSide);
  fork (\(_ : ()) 1-> put 1 clientSide);
  get clientSide + get clientSide
