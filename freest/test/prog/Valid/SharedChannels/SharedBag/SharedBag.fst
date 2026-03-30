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
    &Get chan -> send (receive_ readFromState) chan |> wait 
    &Put chan -> send_ (receiveAndWait chan) writeOnState
    
-- | A shared bag server with a state
bagServer : State -> Dual SharedBag -> Void@*T
bagServer state serverChannel =
  let (clientSide, serverSide) = channel @Bag in
  send_ clientSide serverChannel;
  fork (\(_ : ()) 1-> handleClient state serverSide);
  bagServer state serverChannel

-- | An empty shared bag
emptyBagServer : Dual SharedBag -> Void@*T
emptyBagServer = bagServer (channel @*?Int)

-- Client side, utilities

-- | Put an integer on a shared bag
put : Int -> SharedBag -> ()
put n q = receive_ q |> select Put |> send n |> close

-- | Get an integer from a shared bag
get : SharedBag -> Int
get q = receive_ q |> select Get |> receiveAndClose

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
