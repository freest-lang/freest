module Genetic where
{-

This program is an implementation of a Genetic Algorithm tailored
  especifically for the All Ones problem (number of ones in the
  binary representation).

Additional notes:
  - to enable printing inside the sequential genetic algorithm,
      uncomment lines 238 and 240
  - to enable printing inside the parallel genetic algorithm,
      uncomment line 327

-}

-- ===== CONSTANTS =====

-- Max number
maxNum : Int
maxNum = 100000

-- ===== UTILITY =====

-- == RANDOM ==

-- Generates a pseudorandom number given a seed (using linear congruential
--   generation)
nextRandom : Int -> Int
nextRandom seed =
  let a = 1103515245 in
  let c = 12345 in
  let m = 9223372036854775808 in -- 1 << 63
  abs $ mod (a * seed + c) m

-- Generates a pseudorandom number given a seed, and an upper bound
nextRandomBounded : Int -> Int -> (Int, Int)
nextRandomBounded seed upperBound =
  let random = nextRandom seed in
  (random, mod random upperBound)

-- == MATH ==

-- Counts the amount of ones in the binary representation of a number
countOnes : Int -> Int
countOnes i =
  if i/2 > 0
  then (mod i 2) + countOnes (i/2)
  else mod i 2


-- ===== INDIVIDUAL =====

-- Represents a single individual, in this case, a single Integer
type Individual : *T
type Individual = Int


-- Generate a random individual given a seed
--   This implementation generates an individual
--   with at most 2^3 as its value
generateIndividual : Int -> (Int, Individual)
generateIndividual seed = nextRandomBounded seed (2^3)

-- Fitness function for the AllOnes problem (amount of 1s in binary rep)
fitnessAllOnes : Individual -> Int
fitnessAllOnes = countOnes

-- Compares two individuals and returns the fittest
compareIndividuals : Individual -> Individual -> Individual
compareIndividuals ind0 ind1 =
  if fitnessAllOnes ind0 >= fitnessAllOnes ind1
  then ind0
  else ind1

-- Performs a random crossover between two individuals using a random
--   crossover point (generated using a seed), and returns the individuals
--   and a new seed
crossoverBoth : Int -> Individual -> Individual -> (Int, (Individual, Individual))
crossoverBoth seed ind0 ind1 =
  -- Generate random crossover point (at most to the maxNum)
  let (seed, crossover) = nextRandomBounded seed maxNum in
  -- Return result with an updated seed
  (seed, crossoverBoth_ ind0 ind1 1 (crossover + 1))
  where
    crossoverBoth_ : Individual -> Individual -> Int -> Int -> (Individual, Individual)
    crossoverBoth_ ind0 ind1 counter crossover =
      if crossover == 0
      then
        (ind0 * counter, ind1 * counter)
      else
        let bit0 = mod ind0 2 in
        let bit1 = mod ind1 2 in
        let (ind0, ind1) = crossoverBoth_ (ind0 / 2) (ind1 / 2) (counter * 2) (crossover / 2) in
        ((bit1 * counter) + ind0, (bit0 * counter) + ind1)

-- Crossover an individual with another individual using a seed, and return a
--   new individual alongside a new seed to use
crossoverWith : Int -> Individual -> Individual -> (Int, Individual)
crossoverWith seed ind0 ind1 =
  let (seed, (_, ind1)) = crossoverBoth seed ind0 ind1 in
  (seed, ind1)

-- Mutates an individual given a seed and returns the mutated individual and
--   a new seed.
--   This implementation sums a random power of 2 and does a wraparound
mutateIndividual : Int -> Individual -> (Int, Individual)
mutateIndividual seed ind =
  let (seed, n) = nextRandomBounded seed maxNum in
  (seed, mod (ind + n) (maxNum))


-- ===== POPULATION =====

-- Represents a population a.k.a. a list of Individuals
type Population : *T
data Population = NilPop | ConsPop Individual Population

-- Generate a random population of a given size using a given seed
generatePopulation : Int -> Int -> (Int, Population)
generatePopulation seed size =
  if size == 0
  then (seed, NilPop)
  else
    let (seed, individual) = generateIndividual seed in
    let (seed, pop) = generatePopulation seed (size-1) in
    (seed, ConsPop individual pop)

-- Auxiliary function to filter through a population
--   Uses a function to compare individuals' fitness
getIndividual_ : Individual -> Population -> (Individual -> Individual -> Bool) -> (Individual, Population)
getIndividual_ ind0 pop0 f =
  case pop0 of
    NilPop  -> (ind0, NilPop)
    ConsPop ind1 pop1 ->
      let (fittest, pop) = getIndividual_ ind0 pop1 f in
      if f (fitnessAllOnes fittest) (fitnessAllOnes ind1)
      then (fittest, ConsPop ind1 pop)
      else (ind1, ConsPop fittest pop)

-- Get the fittest individual of a population and isolates them from the rest
getFittestIndividual : Population -> (Individual, Population)
getFittestIndividual population =
  case population of
    NilPop -> (0, NilPop)  -- Should never happen
    ConsPop ind l ->
      getIndividual_ ind l (>=)

-- Get the fittest individual of a population and isolates them from the rest
getUnFittestIndividual : Population -> (Individual, Population)
getUnFittestIndividual population =
  case population of
    NilPop -> (0, NilPop)   -- Should never happen
    ConsPop ind l ->
      getIndividual_ ind l (<)

-- Crossover a population with an individual given a seed
crossoverPopulation : Int -> Individual -> Population -> (Int, Population)
crossoverPopulation seed ind0 pop0 =
  case pop0 of
    NilPop -> (seed, NilPop)
    ConsPop ind1 pop1 ->
      let (seed, ind1) = crossoverWith seed ind0 ind1 in
      let (seed, pop) = crossoverPopulation seed ind0 pop1 in
      (seed, ConsPop ind1 pop)

-- Mutate all individuals in a population
mutatePopulation : Int -> Population -> (Int, Population)
mutatePopulation seed pop0 =
  case pop0 of
    NilPop -> (seed, NilPop)
    ConsPop ind1 pop1 ->
      let (seed, ind1) = mutateIndividual seed ind1 in
      let (seed, pop) = mutatePopulation seed pop1 in
      (seed, ConsPop ind1 pop)

-- ===== SEQUENTIAL GENETIC ALGORITHM =====

geneticAlg_ : Int -> Int ->  Population -> (Int, Population)
geneticAlg_ seed iterations pop =
  if iterations == 0
  then (seed, pop)
  else
    -- Selection - isolate fittest individual from the population
    let (fittest, pop) = getFittestIndividual pop in
    -- Crossover - crossover every individual with the fittest individual
    let (seed, pop) = crossoverPopulation seed fittest pop in
    -- Mutation - randomly mutate the population (not the fittest individual)
    let (seed, pop) = mutatePopulation seed pop in
    -- Compute fitness of the (hopefully) new fittest individual
    --let (fittest, _) = getFittestIndividual pop in
    -- Print information
    --print fittest;
    -- Re-add the fittest individual |> Continue the algorithm (-1 iteration)
    geneticAlg_ seed (iterations - 1) (ConsPop fittest pop)

-- Sequential genetic algorithm
geneticAlg : Int -> Int -> Int -> Individual
geneticAlg seed populationSize iterations =
  -- Generate first population
  let (seed, pop) = generatePopulation seed populationSize in
  -- Get first fittest individual
  --let (fittest, _) = getFittestIndividual pop in
  -- Print out first individual
  --print fittest;
  -- Apply the genetic algorithm
  let (_, pop) = geneticAlg_ seed iterations pop in
  -- Get the resulting population's fittest individual
  let (fittest, _) = getFittestIndividual pop in
  -- Return it
  fittest

-- ===== PARALLEL GENETIC ALGORITHM - MASTER ISLANDS =====

-- Channel to communicate to islands
type IslandChannel : 1C
type IslandChannel = +{
  Fittest:   ?Int; IslandChannel, -- Gets the fittest individual of an Island
  Crossover: !Int; IslandChannel, -- Sends an individual to perform a GA iteration
  Done:       Close }               -- Close the channel


-- Channel for the client to ask master the result
type ResultChannel : 1C
type ResultChannel = ?Int;Wait    -- Compute result and return it


-- Structure that represents a list of IslandChannels
--   Used by the master to hold all channels to the islands
type ListIslandChannel : 1T
data ListIslandChannel = Nil () | Cons IslandChannel ListIslandChannel

-- Fold function over a list of IslandChannels
foldIslands : forall (a : *T) -> (a -> IslandChannel -> (a, IslandChannel)) -> a -> ListIslandChannel -> (a, ListIslandChannel)
foldIslands @a f x chs =
  case chs of
    Nil _ ->
      (x, Nil ())
    Cons ch chss ->
      let (x, ch) = f x ch in
      let (x, chss) = foldIslands f x chss in
      (x, Cons ch chss)

receiveFittestF :  Individual -> IslandChannel -> (Individual, IslandChannel)
receiveFittestF ind0 island =
  let (ind1, island) = receive $ select Fittest island in
  (compareIndividuals ind0 ind1, island)

-- Compute the absolute fittest individual of all islands
receiveFittest : ListIslandChannel -> (Individual, ListIslandChannel)
receiveFittest = foldIslands receiveFittestF 0

sendFittestF :  Int -> IslandChannel -> (Int, IslandChannel)
sendFittestF fittest island = (fittest, send fittest $ select Crossover island)

-- Send an individual to every island to do another round of the GA
sendFittest : Individual -> ListIslandChannel -> ListIslandChannel
sendFittest fittest channels0 = snd $ foldIslands sendFittestF fittest channels0


-- Auxiliary function that performs the getFittest-sendFittest loop
masterLoop : ListIslandChannel -> Int -1-> ListIslandChannel
masterLoop channels nIterG =
  if nIterG == 0
  then
    channels
  else
    -- Get fittest from all
    let (fittest, channels) = receiveFittest channels in
    -- Print information
    --print fittest;
    -- Send fittest to all
    let channels = sendFittest fittest channels in
    -- Continue iterating
    masterLoop channels (nIterG - 1)

-- End all islands and compute the absolute fittest individual
--   Note: This function can not use the foldIslands function because
--         the resulting channels would be Skip and not IslandChannel,
--         therefore raising an error
endIslands : ListIslandChannel -> ()
endIslands cs =
  case cs of
    Nil _ -> ()
    Cons c cs' -> select Done c |> close; endIslands cs'

-- Run the master process that coordinates all the islands
--   and then sends the result to the client
runMasterServer : Dual ResultChannel -> ListIslandChannel -1-> Int -1-> ()
runMasterServer c channels nIterG =
  -- Apply nIterG global iterations
  let channels = masterLoop channels nIterG in
  -- Get fittest individual from all islands...
  let (fittest, channels) = receiveFittest channels in
  -- ... and send it to the client
  send fittest c |> close;
  -- End all islands
  endIslands channels

-- Run an island instance that holds a population an performs
--   the GA on demand (by the master)
runIsland : Dual IslandChannel -> Int -1-> Int -1-> Population -1-> ()
runIsland master seed nIterI pop =
  case master of
    &Fittest master ->
      -- Get our population's fittest
      let (ourFittest, _) = getFittestIndividual pop in
      -- Send it to the master
      let master = send ourFittest master in
      -- Continue serving
      runIsland master seed nIterI pop
    &Crossover master ->
      -- Receive true fittest
      let (fittest, master) = receive master in
      -- Kill unfittest from population...
      let (_, pop) = getUnFittestIndividual pop in
      -- ... and insert the true fittest in the population
      let pop = ConsPop fittest pop in
      -- Apply GA nIterI times inside island
      let (seed, pop) = geneticAlg_ seed nIterI pop in
      -- Continue serving
      runIsland master seed nIterI pop
    &Done master ->
      -- Stop (get some help  -Michael Jordan)
      wait master

initIslands_ : ListIslandChannel -> Int -1-> Int -1-> Int -1-> Int -1-> Int -1-> ResultChannel
initIslands_ channels seed islands popSize nIterI nIterG =
  if islands == 0
  then
    let (client, server) = channel @ResultChannel in
    fork #1 (\(_ : ()) -1-> runMasterServer server channels nIterG);
    client
  else
    let (master, island) = channel @IslandChannel in
    let (seed, pop) = generatePopulation seed popSize in
    fork #1 (\(_ : ()) -1-> runIsland island seed nIterI pop);
    initIslands_ (Cons master channels) seed (islands - 1) popSize nIterI nIterG


-- Initialize all needed processes (islands + master) and return a
--   ResultChannel for the client to request the result
initIslands : Int -1-> Int -1-> Int -1-> Int -1-> Int -1-> ResultChannel
initIslands = initIslands_ $ Nil ()

-- ===== MAIN =====

-- Parameters
argSeed, argPopSize, argIterPop, argIslands, argIterIsl : Int

-- Initial seed for random number generation
argSeed = 12345

-- Amount of individuals per population
argPopSize = 10

-- Iterations per population
argIterPop = 5

-- [PARALLEL] Amount of islands (each island has one population)
argIslands = 4

-- [PARALLEL] Amount of population iteration |> fittest individual sync
argIterIsl = 5

-- Example clients using the sequential vs the parallel genetic algorithms
clientSequential, clientParallel : Int

clientSequential = geneticAlg argSeed argPopSize argIterPop

clientParallel = 
  let (i, c) = receive $ initIslands argSeed argIslands argPopSize argIterPop argIterIsl in
  wait c;
  i

main : ()
main =
  let result = clientParallel in
  -- Print value
  putStr "  Value: "; print result;
  -- Print fitness
  putStr "Fitness: "; print $ fitnessAllOnes result
