-- A barrier: clients request a linear sync session on a shared channel; the
-- server releases them only after all of them have arrived, telling each
-- client how many clients reached the barrier.

type SyncServer : *C
type SyncServer  = *!(Dual SyncService)

type SyncService : 1C
type SyncService = ?Int; Wait

-- | Accept k clients, then release all of them, sending each the total n.
syncServer : Int -> Dual SyncServer -> Int -> ()
syncServer _ _  0 = ()
syncServer n ch k =
    -- accept a client; recursive call
    let s = accept ch in
    syncServer n ch (k - 1);
    -- sync client
    s |> send n |> close

-- | Request a linear sync session and wait for sync
sync : SyncServer -> Int
sync ch = request ch |> receiveAndWait

client : SyncServer -> ForkJoin -> ()
client ch j = print (sync ch); join j

nClients : Int
nClients = 10

-- Every client prints the number of clients at the barrier, i.e., `nClients`
main : ()
main =
    let (c, s) = channel @SyncServer
        (j, a) = channel @ForkJoin in
    parallel nClients (\_ -> client c j);
    syncServer nClients s nClients;
    await nClients a
