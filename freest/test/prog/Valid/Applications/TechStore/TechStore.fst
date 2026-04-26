module TechStore where


initQueue : forall (a : *T). () -> (*?a, *!a)
initQueue @a _ = channel @(*?a)


buyWorker : (*?(), *!()) -> *?() -> *?() -> ()
buyWorker buyQueue map bank = ()

setupStore : *?() -> () 
setupStore bank =
  -- buy
  let buyQueue = initQueue @() () in -- CANNOT INFER
  let stockMap = fst (channel @*?()) in
  fork (\(_ : ()) 1-> buyWorker buyQueue stockMap bank)

