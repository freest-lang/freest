module FtpServer where

-- 1 _ State

-- |The elements in the state
type File : *T
type File = Int

-- |A bag of files managed by a shared channel.
-- |The elements in the bag are messages in transit.
type State : *T
type State = (*?File, *!File)

-- |Read a file from the state
readFrom : State -> File
readFrom state =
  receive_ @File $ fst @*?File @*!File state

-- |Write a file to the state
writeTo : File -> State -> ()
writeTo file state =
  send file $ snd @*?File @*!File state; ()

-- 2 _ Types for the FTP server

-- |An FTP server, as seen from the side of an FTP client
-- |Connects clients to the server
type FTP : *C
type FTP = *?FTPSession
-- | An FTP session seen from the side of the client
type FTPSession : 1C
type FTPSession = +
  { Get: ?File ; FTPSession
  , Put: !File ; FTPSession
  , Bye: Close
  }
-- |An FTP thread channel as seen from the side of the FTP thread
-- |Connects the FTP demon to its threads
type FTPThread : *C
type FTPThread = *?(Dual FTPSession)

-- 3 _ The FTP server

-- |FTP demon: wait for a client, wait for a thread;
-- |pass the client to the thread
ftpd : Dual FTP -> Dual FTPThread -> Void@*T
ftpd pid b = 
  send (accept @FTPSession pid) b;
  ftpd pid b

mutual
  -- |An FTP thread: receive a request from the demon;
  -- |authenticate the client; pass the thread to the actions loop
  ftpThread : State -> FTPThread -> Void@*T
  ftpThread state b =
    -- TODO: authenticate the client
    actions state (receive_ @(Dual FTPSession) b) b

  -- |A linear interaction with the client;
  -- |once done become an FTP thread
  actions : State -> Dual FTPSession -> FTPThread 1-> Void@*T
  actions state s b =
    case s of
      &Get s ->
          let file = readFrom state in
          print @Int (- file);
          actions state (send file s) b
      &Put s ->
          let (file, s) = receive s in
          print @Int  file;
          writeTo file state;
          actions state s b
      &Bye s -> wait s; ftpThread state b

-- Should be in the prelude
parallel : forall (a : *T) . Int -> (() -> a) -> ()
parallel @a n thunk = repeat @() n (\(_ : ()) -> fork @a thunk)

-- |Initialise the server: create n FTP threads and launch the demon
init : Int -> Dual FTP -> Void@*T
init n pid =
  let (r, w) = channel @(Dual FTPThread) in
  let state  = channel @*?File in
  parallel @() n (\(_ : ()) -> ftpThread state w);
  ftpd pid r

-- Sample clients

-- |Put a file and terminate
putClient : FTP -> File -> ()
putClient pid file =
  let (c, _) = receive pid in
  select Put c |> send file |> select Bye |> close 

-- |Get a file and terminate
getClient : FTP -> ()
getClient pid =
  let (c, _) = receive pid in
  let c = select Get c in
  let (file, c) = receive c in
  select Bye c |> close

-- |Put two files and terminate
putClient' : FTP -> File -> File -> ()
putClient' pid file1 file2 =
  let c = receive_ @FTPSession pid in
  select Put c |> send file1 |>
  select Put   |> send file2 |>
  select Bye |> close

-- |Get a file and terminate
putgetClient : FTP -> File -> ()
putgetClient pid file =
  let (c, _)    = receive pid in
  let c         = select Put c in
  let c         = send file c in
  let c         = select Get c in
  let (file, c) = receive c in
  let c         = select Put c in
  let c         = send file c in
  select Bye c |> close

-- Application

main : Void@*T
main =
  let (ftpc, ftps) = channel @FTP in
  -- A few clients
  fork (\(_ : ()) 1-> putClient ftpc 27);
  fork (\(_ : ()) 1-> getClient ftpc);
  fork (\(_ : ()) 1-> getClient ftpc);
  fork (\(_ : ()) 1-> putClient' ftpc 93 66);
  fork (\(_ : ()) 1-> putgetClient ftpc 14);
  fork (\(_ : ()) 1-> putClient ftpc 59);
  -- A server with three threads
  init 3 ftps
