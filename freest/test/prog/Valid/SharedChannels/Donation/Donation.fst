{-
Based on the Donation.pi from SePi, available in 
    http://rss.di.fc.ul.pt/tryit/SePi#

Note that FreeST does not have refinement types
-}

type CreditCard, Amount, Date : *T
type CreditCard = String
type Amount = Int
type Date = Int

-- type PromotionS = *!(String, CreditCard, Int)
type PromotionS : *C
type PromotionS = *!(Dual Promotion)

type Promotion : 1C
type Promotion = !String ; !CreditCard ; !Amount ; Close 

type Decision : 1C
type Decision = &{ Accepted: ?PromotionS; Close
                 , Denied  : ?String   ; Close
                 }

type DonationS : *C
type DonationS = *?(Dual Donation)
type Donation : 1C
type Donation = +{ SetTitle: !String ; Donation
                 , SetDate : !Date   ; Donation
                 , Commit  : Decision
                 }

-- Rather than printing, clients report denials and the bank reports charges
-- back to main.
type DenialReport : *C
type DenialReport = *!String

type ChargeReport : *C
type ChargeReport = *!(CreditCard, Amount)

-- 1. Two clients

donate : PromotionS -> String -> CreditCard -> Amount -> ()
donate p donor ccard amount =
  request p |> send donor |> send ccard |> send amount |> close

helpSavingTheWolf : DenialReport -> Dual DonationS -> ()
helpSavingTheWolf r d =
  case
    d |> request
      |> select SetDate  |> send 2012                   -- setup the date
      |> select SetTitle |> send "Help Saving the Wolf" -- setup the title
      |> select SetDate  |> send 2013                   -- fix the 2012 date
      |> select Commit
  of
    &Accepted d ->
      let p = receiveAndClose d in 
      fork (\_ -1-> donate p "Benefactor1" "2345" 5);
      donate p "Benefactor3" "1004" 10
    &Denied d ->
      send_ (receiveAndClose d) r ; ()

wrongYear : DenialReport -> Dual DonationS -> ()
wrongYear r d = 
  case
    d |> request
      |> select SetDate  |> send 1999 -- wrong date
      |> select SetTitle |> send "Help Saving the Mink" 
      |> select Commit
  of
    &Accepted d -> -- Not going to happen...
      let p = receiveAndClose d in 
      donate p "No Benefactor" "0000" 0
    &Denied d ->
      send_ (receiveAndClose d) r ; ()


-- 2. The bank that charges credit cards
charge : ChargeReport -> CreditCard -> Amount -> ()
charge r ccard amount =
  send_ (ccard, amount) r ; ()


-- 3. The Online Donation Server
promotion : Int -> ForkJoin -> ChargeReport -> Dual PromotionS -> ()
promotion k f r pc
  | k == 0 = join f
  | otherwise =
    let p = accept pc in
    let (donor, p) = receive p in
    let (ccard, p) = receive p in
    let amount     = receiveAndWait p in
    charge r ccard amount;
    promotion (k - 1) f r pc

setup : String -> Date -> ForkJoin -> PromotionS -> Dual Donation -> ()
setup title _    f p (&SetDate  d) = let (date,  d) = receive d in setup title date f p d
setup _     date f p (&SetTitle d) = let (title, d) = receive d in setup title date f p d
setup title date f p (&Commit   d) =
  (if date < 2013 then 
    select Denied d |> send "Can only accept donations from year 2013"
  else 
    select Accepted d |> send p)
    |> wait ;
  join f

server : Int -> Int -> (ForkJoin, Dual ForkJoin) -> PromotionS -> DonationS -> ()
server k n fj p ds
  | k == 0    = await n (snd fj)
  | otherwise =
    let d = accept ds in
    fork (\_ -1-> setup "<default>" 0000 (fst fj) p d);
    server (k - 1) n fj p ds

donationServer : Int -> Int -> ChargeReport -> DonationS -> ()
donationServer noOfClients noOfDonations r ds =
  let (f, j) = channel @ForkJoin in
  let p = forkWith (promotion noOfDonations f r) in
  server noOfClients noOfClients (channel @ForkJoin) p ds;
  await 1 j

-- 4. Test

-- | Collect the denial (on channel cd) and the four charges (on channel cc),
-- and check that they make sense.
test : *?String -> *?(CreditCard, Amount) -> ()
test cd cc =
  if checkDenial (receive_ cd) && checkCharges (receiveN 4)
  then putStrLn "nondeterministic test passed"
  else putStrLn "nondeterministic test failed"
  where
    -- | String equality (in the Prelude, (==) is on Int only)
    eqString : String -> String -> Bool
    eqString []        []        = True
    eqString (x :: xs) (y :: ys) = ord x == ord y && eqString xs ys
    eqString _         _         = False
    -- | Receive n charges, in order of arrival
    receiveN : Int -> [(CreditCard, Amount)]
    receiveN 0 = []
    receiveN n = receive_ cc :: receiveN (n - 1)
    -- | Only wrongYear is denied, for its date
    checkDenial : String -> Bool
    checkDenial = eqString "Can only accept donations from year 2013"
    -- | Each of the two helpSavingTheWolf clients donates 5 euros on card 2345
    -- and 10 euros on card 1004
    validCharge : (CreditCard, Amount) -> Bool
    validCharge c =
      eqString (fst c) "2345" && snd c == 5 ||
      eqString (fst c) "1004" && snd c == 10
    -- | Four valid charges adding up to 30 euros: two of 5 and two of 10, in
    -- any order
    checkCharges : [(CreditCard, Amount)] -> Bool
    checkCharges cs =
      length cs == 4 && all validCharge cs && sum (map snd cs) == 30

-- 5. Main
main : ()
main = 
  let (serverEnd, clientEnd)              = channel @DonationS
      (collectDenialEnd, reportDenialEnd) = channel @(*?String)
      (collectChargeEnd, reportChargeEnd) = channel @(*?(CreditCard, Amount)) in
  let noOfClients = 3 in
  let noOfDonations = 4 in
  fork (\_ -1-> helpSavingTheWolf reportDenialEnd clientEnd);
  fork (\_ -1-> wrongYear reportDenialEnd clientEnd);
  fork (\_ -1-> helpSavingTheWolf reportDenialEnd clientEnd);
  donationServer noOfClients noOfDonations reportChargeEnd serverEnd;
  test collectDenialEnd collectChargeEnd
