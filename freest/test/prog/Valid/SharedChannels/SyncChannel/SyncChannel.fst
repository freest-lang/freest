module SyncChannel where

type SyncServer : *C
type SyncServer  = *?SyncService

type SyncService : 1C
type SyncService = ?Int; Wait

syncServerOnce : Int -> Dual SyncServer -> ()
syncServerOnce limit ch = 
    if limit == 0
    then ()
    else 
        -- create endpoints for syncing
        let (c, s) = channel @SyncService in
        -- send client's endpoint; recursive call
        send_ c ch; syncServerOnce (limit - 1) ch;
        -- sync client
        send 0 s |> close

syncServer : Int -> Dual SyncServer -> ()
syncServer limit ch =
    syncServerOnce limit ch;
    syncServer limit ch

-- receive linear sync channel and wait for sync
sync : SyncServer -> ()
sync ch = receive_ ch |> receiveAndWait; ()

client : Int -> SyncServer -> ()
client id ch = print (- id); sync ch; print id

forkNClients : Int -> SyncServer -> ()
forkNClients i ch
  | i == 0    = ()
  | otherwise = fork (\(_ : ()) -1-> client i ch); 
                forkNClients (i - 1) ch

nServers : Int
nServers = 20

main : ()
main = 
    let (c, s) = channel @SyncServer in
    forkNClients nServers c;
    syncServer nServers s
