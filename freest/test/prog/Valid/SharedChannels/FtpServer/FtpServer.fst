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
readFrom (files, _) =
  receive_ files

-- |Write a file to the state
writeTo : File -> State -> ()
writeTo file (_, files) =
  send_ file files; ()

-- 2 _ Types for the FTP server

-- |An FTP server, as seen from the side of an FTP client
-- |Connects clients to the server
type FTP : *C
type FTP = *!(Dual FTPSession)
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
ftpd : Dual FTP -> Dual FTPThread -> Void @*T
ftpd ftp threads = 
  threads |> send_ (accept ftp) |> ftpd ftp

mutual
  -- |An FTP thread: receive a request from the demon;
  -- |authenticate the client; pass the thread to the actions loop
  ftpThread : State -> FTPThread -> Void @*T
  ftpThread state threads =
    -- TODO: authenticate the client
    actions state threads (receive_ threads)

  -- |A linear interaction with the client;
  -- |once done become an FTP thread
  actions : State -> FTPThread -> Dual FTPSession -> Void @*T
  actions state threads (&Get s) =
    actions state threads (send (readFrom state) s)
  actions state threads (&Put s) =
    let (file, s) = receive s in
    writeTo file state;
    actions state threads s
  actions state threads (&Bye s) =
    wait s;
    ftpThread state threads

-- |Initialise the server: create n FTP threads and launch the demon
init : Int -> Dual FTP -> Void @*T
init n ftp =
  let (toThreads, fromDaemon) = channel @(Dual FTPThread) in
  let state = channel @*?File in
  parallel n (\(_ : ()) -> ftpThread state fromDaemon);
  ftpd ftp toThreads

-- Sample clients

-- |Put a file and terminate
putClient : FTP -> File -> ()
putClient ftp file =
  request ftp |> select Put |> send file |> select Bye |> close 

-- |Get a file and terminate, returning the file
getClient : FTP -> File
getClient ftp =
  let (file, c) = request ftp |> select Get |> receive in
  c |> select Bye |> close;
  file

-- |Put two files and terminate
putClient' : FTP -> File -> File -> ()
putClient' ftp file1 file2 =
  request ftp |> select Put |> send file1
              |> select Put |> send file2
              |> select Bye |> close

-- |Get a file and terminate
putgetClient : FTP -> File -> ()
putgetClient ftp file =
  let (file, c) = request ftp |> select Put |> send file
                              |> select Get |> receive
  in c |> select Put |> send file |> select Bye |> close

-- Application

-- Five files are put on the server: 27, 93, 66, 14 and 59. The two get
-- clients obtain two of them (which ones depends on scheduling); once all
-- clients are done, the remaining three are fetched. The sum of all the files
-- obtained is always 27 + 93 + 66 + 14 + 59 = 259.
main : ()
main =
  let (ftpc, ftps) = channel @FTP
      (j, a)       = channel @ForkJoin
      (r, w)       = channel @(*?File) in
  -- A server with three threads
  fork (\(_ : ()) -1-> init 3 ftps);
  -- A few clients
  fork (\(_ : ()) -1-> putClient ftpc 27; join j);
  fork (\(_ : ()) -1-> send_ (getClient ftpc) w; join j);
  fork (\(_ : ()) -1-> send_ (getClient ftpc) w; join j);
  fork (\(_ : ()) -1-> putClient' ftpc 93 66; join j);
  fork (\(_ : ()) -1-> putgetClient ftpc 14; join j);
  fork (\(_ : ()) -1-> putClient ftpc 59; join j);
  await 6 a;
  -- The files obtained by the get clients plus those left on the server
  print (receive_ r + receive_ r + getClient ftpc + getClient ftpc + getClient ftpc)
