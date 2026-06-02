{-
Based on the Donation.pi from SePi, available in 
    http://rss.di.fc.ul.pt/tryit/SePi#

Note that FreeST does not have refinement types
-}

module Donation where

type CreditCard, Amount, Date : *T
type CreditCard = String
type Amount = Int
type Date = Int

-- type PromotionS = *?(String, CreditCard, Int)
type PromotionS : *C
type PromotionS = *?Promotion

type Promotion : 1C
type Promotion = !String ; !CreditCard ; !Amount ; Close 

type Decision : 1C
type Decision = &{ Accepted: ?PromotionS; Close
                 , Denied  : ?String   ; Close
                 }

type DonationS : *C
type DonationS = *!Donation
type Donation : 1C
type Donation = +{ SetTitle: !String ; Donation
                 , SetDate : !Date   ; Donation
                 , Commit  : Decision
                 }

-- 1. Fork join

type Fork, Join : *C
type Fork = *+{Over}
type Join = Dual Fork

waitFor : Int -> Join -> ()
waitFor n join
  | n == 0    = ()
  | otherwise = case join of &Over _ -> waitFor (n - 1) join


-- 2. Two clients

donate : PromotionS -> String -> CreditCard -> Amount -> ()
donate p donor ccard amount =
  receive_ p |> send donor |> send ccard |> send amount |> close

helpSavingTheWolf : Dual DonationS -> ()
helpSavingTheWolf d =
  case
    d |> receive_ 
      |> select SetDate  |> send 2012                   -- setup the date
      |> select SetTitle |> send "Help Saving the Wolf" -- setup the title
      |> select SetDate  |> send 2013                   -- fix the 2012 date
      |> select Commit
  of
    &Accepted d ->
      let p = receiveAndClose d in 
      fork (\(_ : ()) -1-> donate p "Benefactor1" "2345" 5);
      donate p "Benefactor3" "1004" 10
    &Denied d ->
      putStrLn $ receiveAndClose d

wrongYear : Dual DonationS -> ()
wrongYear d = 
  case
    d |> receive_ 
      |> select SetDate  |> send 1999 -- wrong date
      |> select SetTitle |> send "Help Saving the Mink" 
      |> select Commit
  of
    &Accepted d -> -- Not going to happen...
      let p = receiveAndClose d in 
      donate p "No Benefactor" "0000" 0
    &Denied d ->
      putStrLn $ receiveAndClose d


-- 3. The bank that charges credit cards
charge : CreditCard -> Amount -> ()
charge ccard amount =
  putStrLn $ ("Charging " ++ show amount ++ " euros on card " ++ ccard)


-- 4. The Online Donation Server
promotion : Int -> Fork -> Dual PromotionS -> ()
promotion k f pc
  | k == 0 = select Over f; ()
  | otherwise =
    let p = accept pc in
    let (donor, p) = receive p in
    let (ccard, p) = receive p in
    let amount     = receiveAndWait p in
    charge ccard amount;
    promotion (k - 1) f pc

setup : String -> Date -> Fork -> PromotionS -> Dual Donation -> ()
setup title _    f p (&SetDate  d) = let (date,  d) = receive d in setup title date f p d
setup _     date f p (&SetTitle d) = let (title, d) = receive d in setup title date f p d
setup title date f p (&Commit   d) =
  (if date < 2013 then 
    select Denied d |> send "Can only accept donations from year 2013"
  else 
    select Accepted d |> send p) 
    |> wait ;
  select Over f ; ()

server : Int -> Int -> (Fork, Join) -> PromotionS -> DonationS -> ()
server k n fj p ds
  | k == 0    = waitFor n (snd fj)
  | otherwise =
    let d = accept ds in
    fork (\(_ : ()) -1-> setup "<default>" 0000 (fst fj) p d);
    server (k - 1) n fj p ds

donationServer : Int -> Int -> DonationS -> ()
donationServer noOfClients noOfDonations ds =
  let (f, j) = channel @Fork in
  let p = forkWith (promotion noOfDonations f) in
  server noOfClients noOfClients (channel @Fork) p ds;
  case j of &Over _ -> ()

-- 5. Main
main : ()
main = 
  let (ds, dc) = channel @DonationS in
  let noOfClients = 3 in
  let noOfDonations = 4 in
  fork (\(_ : ()) -1-> helpSavingTheWolf dc);
  fork (\(_ : ()) -1-> wrongYear dc);
  fork (\(_ : ()) -1-> helpSavingTheWolf dc);
  donationServer noOfClients noOfDonations ds
