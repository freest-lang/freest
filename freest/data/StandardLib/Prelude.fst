-- | The FreeST Prelude.

-- * Undefined. Useful for builtins, but should also be builtin...
undefined : forall (a : *T) -> a
undefined @a = undefined

-- * Error
error : forall (a : 1T) -> String -> a
error @a = undefined

-- * Standard types, classes and related functions

-- ** Basic datatypes

type Bool : *T
data Bool = True | False

(||), (&&) : Bool -> Bool -> Bool
(||) = undefined
(&&) = undefined

not : Bool -> Bool
not True  = False
not False = True

otherwise : Bool
otherwise = True

type Maybe : *T -> *T
data Maybe a = Nothing | Just a

maybe : forall (a : *T) (b : *T) -> b -> (a -> b) -> Maybe a -> b
maybe @a @b n _ Nothing  = n
maybe @a @b _ f (Just x) = f x

type Either : *T -> *T -> *T
data Either a b = Left a | Right b

either : forall (a : *T) (b : *T) (c : 1T) -> (a -> c) -> (b -> c) -> Either a b -> c
either @a @b @c f _ (Left x)  =  f x
either @a @b @c _ g (Right y) =  g y

type Ordering : *T
data Ordering = LT | EQ | GT

ord : Char -> Int
ord = undefined

chr : Int -> Char
chr = undefined

type String : *T
type String = [Char]

show : forall (a : *T) -> a -> String
show @a = undefined

type R : *T -> *T
type R a = R a -> a

fix : forall (a : *T) -> ((a -> a) -> (a -> a)) -> (a -> a)
fix @a f =
  (\(x : R (a -> a)) -> f (\(z : a) -> x x z))
  (\(x : R (a -> a)) -> f (\(z : a) -> x x z))

-- ** Tuples

fst : forall (a : 1T) (b : *T) -> (a, b) -> a
fst @a @b (x,_) = x

snd : forall (a : *T) (b : 1T) -> (a, b) -> b
snd @a @b (_,y) = y

swap : forall (a : 1T) (b : 1T) -> (a, b) -> (b, a)
swap @a @b (x, y) = (y, x)

curry : forall (a : *T) (b : 1T) (c : 1T) -> ((a, b) -> c) -> a -> b -> c
curry @a @b @c f x y =  f (x, y)

uncurry : forall (a : 1T) (b : 1T) (c : 1T) -> (a -> b -> c) -> ((a, b) -> c)
uncurry @a @b @c f (x, y) =  f x y

-- ** Comparison (only Int and Float, for now)
(<), (<=), (==), (>=), (>), (/=) : Int -> Int -> Bool
(< ) = undefined
(<=) = undefined
(==) = undefined
(>=) = undefined
(> ) = undefined
(/=) = undefined

(>.), (<.), (>=.), (<=.) : Float -> Float -> Bool
(>.)  = undefined
(<.)  = undefined
(>=.) = undefined
(<=.) = undefined

-- ** Numeric functions

-- *** Int
(+), (-), (*), (/), (^), subtract
   , quot, rem, div, mod
   , min, max
   , gcd, lcm 
   : Int -> Int -> Int
(+)      = undefined
(-)      = undefined
(*)      = undefined
(/)      = undefined
(^)      = undefined
quot     = undefined
rem      = undefined 
div      = undefined
mod      = undefined
min      = undefined
max      = undefined
subtract = undefined
gcd      = undefined
lcm      = undefined

succ, pred, abs, negate : Int -> Int
succ   = undefined
pred   = undefined
abs    = undefined
negate = undefined

even, odd : Int -> Bool
even = undefined
odd  = undefined

-- *** Float
(+.), (-.), (*.), (/.), (**), maxF, minF, logBase : Float -> Float -> Float
(+.)    = undefined
(-.)    = undefined
(*.)    = undefined
(/.)    = undefined
(**)    = undefined
maxF    = undefined
minF    = undefined
logBase = undefined

absF, negateF, recip
    , exp, log, sqrt 
    , log1p, expm1, log1pexp, log1mexp
    , sin, cos, tan, asin, acos, atan, sinh, cosh, tanh 
    : Float -> Float
absF     = undefined
negateF  = undefined
recip    = undefined
exp      = undefined
log      = undefined
sqrt     = undefined
log1p    = undefined
expm1    = undefined
log1pexp = undefined
log1mexp = undefined
sin      = undefined
cos      = undefined
tan      = undefined
asin     = undefined
acos     = undefined
atan     = undefined
sinh     = undefined
cosh     = undefined
tanh     = undefined

truncate, round ,ceiling, floor : Float -> Int
truncate = undefined
round    = undefined
ceiling  = undefined
floor    = undefined

pi : Float
pi = undefined

fromInteger : Int -> Float
fromInteger = undefined

-- ** Miscellaneous functions

id : forall (a : 1T) -> a -> a
id @a x = x

const : forall (a : *T) (b : *T) -> a -> b -> a
const @a @b x _ = x

(.) : forall #m #n (a : 1T) (b : 1T) (c : 1T) -> (b -m-> c) -> (a -n-> b) -m-> a -m+n-> c
(.) #m #n @a @b @c f g x = f (g x)

flip : forall #m #n #o (a : 1T) (b : m T) (c : 1T) -> (a -n-> b -o-> c) -> b -n-> a -m+n-> c
flip #m #n # o @a @b @c f x y = f y x

($) : forall #m (a : 1T) (b : 1T) -> (a -m-> b) -> a -m-> b
($) #m @a @b f = f

(|>) : forall #m #n (a : m T) (b : 1T) -> a -> (a -n-> b) -m-> b
(|>) #m #n @a @b x f = f x

until : forall (a : *T) -> (a -> Bool) -> (a -> a) -> a -> a
until @a p f = go
  where
    go : a -> a
    go x | p x       = x
         | otherwise = go (f x)

(;) : forall (a : *T) (b : 1T) -> a -> b -> b
(;) @a @b _ x = x

isSpace : Char -> Bool
isSpace c = let n = ord c in (n == 32) || (9 <= n && n <= 13)

-- * Lists

null : forall a -> [a] -> Bool
null @a [] = True
null @a _ = False

(++) : forall (a : *T) -> [a] -> [a] -> [a]
(++) @a []      ys = ys
(++) @a (x::xs) ys = x :: ((++) @a xs ys)

(++') : forall (a : 1T) -> [a]' -> [a]' -1-> [a]'
(++') @a []'        ys = ys
(++') @a (x ::' xs) ys = x ::' ((++') @a xs ys)

head : forall (a : *T) -> [a] -> a
head @a []       = error "head: empty list"
head @a (x :: _) = x

last : forall (a : *T) -> [a] -> a
last @a []        = error "last: empty list"
last @a (x :: []) = x
last @a (_ :: xs) = last xs

tail : forall (a : *T) -> [a] -> [a]
tail @a []        = error "tail: empty list"
tail @a (_ :: []) = [] @a
tail @a (_ :: xs) = xs

init : forall (a : *T) -> [a] -> [a]
init @a []        = error "init: empty list"
init @a (_ :: []) = [] @a
init @a (x::xs)   = x :: init xs

length : forall (a : *T) -> [a] -> Int
length @a []        = 0
length @a (_ :: xs) = succ (length xs)

sum : [Int] -> Int
sum []        = 0
sum (x :: xs) = x + sum xs

foldl : forall #m #n (a : m T) (b : *T) -> (a -> b -n-> a) -> a -> [b] -m-> a
foldl #m #n @a @b f = go
  where
    go : a -> [b] -m-> a
    go accum (x :: xs) = go (f accum x) xs
    go accum _         = accum

foldl' : forall #m #n (a : m T) (b : 1T) -> (a -> b -n-> a) -> a -> [b]' -m-> a
foldl' #m #n @a @b f = go
  where
    go : a -> [b]' -m-> a
    go accum (x ::' xs) = go (f accum x) xs
    go accum []'        = accum

foldr : forall #m #n (a : *T) (b : m T) -> (a -> b -n-> b) -> b -> [a] -m-> b
foldr #m #n @a @b f = go
  where
    go : b -> [a] -m-> b
    go accum (x :: xs) = f x $ go accum xs
    go accum _         = accum

foldr' : forall #m #n (a : 1T) (b : m T) -> (a -> b -n-> b) -> b -> [a]' -m-> b
foldr' #m #n @a @b f = go
  where
    go : b -> [a]' -m-> b
    go accum (x ::' xs) = f x $ go accum xs
    go accum []'        = accum

map : forall (a : *T) (b : *T) -> (a -> b) -> [a] -> [b]
map @a @b _ []        = []
map @a @b f (x :: xs) = f x :: map f xs

map' : forall (a : 1T) (b : 1T) -> (a -> b) -> [a]' -> [b]'
map' @a @b _ []'        = []'
map' @a @b f (x ::' xs) = f x ::' map' f xs

mapUL : forall (a : *T) (b : 1T) -> (a -> b) -> [a] -> [b]'
mapUL @a @b _ []        = []'
mapUL @a @b f (x :: xs) = f x ::' mapUL f xs

mapLU : forall (a : 1T) (b : *T) -> (a -> b) -> [a]' -> [b]
mapLU @a @b _ []'        = []
mapLU @a @b f (x ::' xs) = f x :: mapLU f xs

-- | Reverses a list, using an accumulator so it runs in linear time (as in
-- Haskell's `Data.List.reverse`).
reverse : forall (a : *T) -> [a] -> [a]
reverse @a = go ([] @a)
  where
    go : [a] -> [a] -> [a]
    go acc []        = acc
    go acc (x :: xs) = go (x :: acc) xs

takeWhile : forall (a : *T) -> (a -> Bool) -> [a] -> [a]
takeWhile @a _ []                    = []
takeWhile @a p (x :: xs) | p x       = x :: takeWhile p xs
                         | otherwise = []

dropWhile : forall (a : *T) -> (a -> Bool) -> [a] -> [a]
dropWhile @a _ []                    = []
dropWhile @a p (x :: xs) | p x       = dropWhile p xs
                         | otherwise = x :: xs

span : forall (a : *T) -> (a -> Bool) -> [a] -> ([a], [a])
span p xs = (takeWhile p xs, dropWhile p xs)

words : String -> [String]
words s =
  case dropWhile isSpace s of
    "" -> []
    s' -> w :: words s''
      where (w, s'') = span (not . isSpace) s'

unwords : [String] -> String
unwords []        = ""
unwords (w :: ws) = w ++ go ws
  where
    go : [String] -> String
    go []        = ""
    go (v :: vs) = ' ' :: (v ++ go vs)

-- * Concurrency

fork : forall #m (a : *T) -> (() -m-> a) -> ()
fork #m @a = undefined

send : forall #m (a : m T) -> a -> forall (b : 1S) -> !a;b -m-> b
send @a = undefined

receive : forall (a : 1T) (b : 1S) -> ?a;b -> (a, b)
receive @a @b = undefined

wait : Wait -> ()
wait = undefined

close : Close -> ()
close = undefined

-- | Sends a value on a given channel and then waits for the channel to be
-- | closed. Returns ().
sendAndWait : forall #m (a : m T) -> a -> !a ; Wait -m-> ()
sendAndWait #m @a x c = c |> send x |> wait

-- | Sends a value on a given channel and then closes the channel.
-- | Returns ().
sendAndClose : forall #m (a : m T) -> a -> !a ; Close -m-> ()
sendAndClose #m @a x c = c |> send x |> close

-- | Receives a value from a channel that continues to `Wait`, closes the 
-- | continuation and returns the value.
-- | 
-- | ```
-- | _ =
-- |   -- create channel endpoints
-- |   let (c, s) = channel @(?String ; Wait) () in
-- |   -- fork a thread that prints the received value (and closes the channel)
-- |   fork (\(_ : ()) -1-> c |> receiveAndWait @String |> putStrLn);
-- |   -- send a string through the channel (and close it)
-- |   s |> send "Hello!" |> close
-- | ```
receiveAndWait : forall (a : 1T) -> ?a ; Wait -> a 
receiveAndWait @a c =
  let (x, c) = receive c in 
  wait c;
  x

-- | As in receiveAndWait only that the type is Wait and the function closes the
-- | channel rather the waiting for the channel to be closed.
receiveAndClose : forall (a : 1T) -> ?a ; Close -> a 
receiveAndClose @a c =
  let (x, c) = receive c in 
  close c;
  x

-- | Sends a value on an unrestricted channel. The unrestricted version of `send`.
-- Returns the (unrestricted) channel, so further operations can be chained.
send_ : forall #m (a : m T) -> a -> *!a -m-> *!a
send_ #m @a = undefined

-- | Receives a value from an unrestricted channel. The unrestricted version of `receive`.
receive_ : forall (a : 1T) -> *?a -> a
receive_ @a = undefined

-- | Session initiation. Accepts a request for a linear session on a shared
-- channel. The requester uses a `receive_` operation to obtain the channel
-- end.
accept : forall (a : 1C) -> *!a -> Dual a
accept @a c =
  let (x, y) = channel @a in
  send_ x c;
  y

-- | Creates a new child process and a channel through which it can
-- communicate with its parent process. Returns the channel endpoint.
--  
-- ```
-- _ =
--   -- fork a thread that receives a string and prints
--   let c = forkWith @(!String ; Wait) @() (\s:(?String ; End) -1-> s |> receiveAndWait @String |> putStrLn) in
--   -- send the string to be printed
--   c |> send "Hello!" |> wait
-- ```
forkWith : forall #m (a : 1C) (b : *T) -> (Dual a -m-> b) -> a
forkWith #m @a f =
  let (x, y) = channel @a in
  fork (\_ -1-> f y);
  x

-- | Runs an infinite shared server thread given a function to serve a client (a
-- handle), the initial state, and the server's shared channel endpoint. It can
-- be seen as an infinite sequential application of the handle function over a
-- newly accepted session, while continuously updating the state.
--   
-- Note: this only works with session types that use session initiation.
-- 
-- ```
-- type SharedCounter : *S = *?Counter
-- type Counter : 1S = +{ Inc: Close
--                      , Dec: Close
--                      , Get: ?Int ; Close
--                      }
-- 
-- -- | Handler for a counter
-- counterService : Int -> dualof Counter -1-> Int
-- counterService i (Inc c) = wait c ; i + 1 
-- counterService i (Dec c) = wait c ; i - 1
-- counterService i (Get c) = c |> send i |> wait ; i
--
-- -- | Counter server
-- runCounterServer : dualof SharedCounter -> Void @*T
-- runCounterServer = runServer @Int @Counter counterService 0
-- ```
runServer : forall (a : *T) (b : 1C) -> (a -> Dual b -> a) -> a -> *!b -> Void @*T
runServer handle state c =
  runServer handle (handle state (accept c)) c

-- | Executes a thunk n times, sequentially.
-- ```
-- _ =
--   -- print "Hello!" 5 times sequentially
--   times5 (\_ -> putStrLn "Hello!")
-- ```
times : forall (a : *T) -> Int -> (() -> a) -> ()
times n _     | n <= 0    = ()
times n thunk | otherwise = thunk (); times (n - 1) thunk

-- | Forks n identical threads. Similar to `times` but working in parallel
-- rather than sequentially.
-- ```
-- _ =
--   -- print "Hello!" 5 times in parallel
--   parallel 5 (\_ -> putStrLn "Hello!")
-- ```
parallel : forall (a : *T) -> Int -> (() -> a) -> ()
parallel n thunk = times n (\_ -> fork thunk)

-- * Fork/Join

-- | A simple channel-based fork/join coordination protocol: each child
-- thread signals completion by selecting the `Join` branch, and the parent
-- thread can wait for a fixed number of such completions.
type ForkJoin = *+{Over}

-- | Signal completion of a child thread to the parent waiting on the join channel.
join : ForkJoin -> ()
join c = select_ Over c ; ()

-- | Wait until `n` child threads have signalled completion through the join channel.
await : Int -> Dual ForkJoin -> ()
await n c = times @() n (\_ -> case c of *&Over -> ())

-- * I/O

-- ** I/O Streams

-- *** Input Stream

-- | The `InStream` type describes input streams (such as `stdin` and read
-- files). `GetChar` reads a single character, `GetLine` reads a line, and
-- `IsEOF` checks for the EOF (End-Of-File) token, i.e., if an input stream
-- has reached the end. Operations in this channel terminate with the `Stop`
-- option.
type InStream : 1C
type InStream = +{ GetChar : ?Char   ; InStream
                 , GetLine : ?String ; InStream
                 , IsEOF   : ?Bool   ; InStream
                 , Stop    : Wait
                 }

hGenericGet : forall (a : *T) -> (InStream -> ?a; InStream) -> InStream -> (a, InStream)
hGenericGet sel inStream = inStream |> sel |> receive

-- | Reads a character from an `InStream` channel endpoint.
hGetChar : InStream -> (Char, InStream)
hGetChar = hGenericGet (select GetChar)

-- | Reads a line (as a string) from an `InStream` channel endpoint.
hGetLine : InStream -> (String, InStream)
hGetLine = hGenericGet (select GetLine)

-- | Checks if an `InStream` reached the EOF mark. 
hIsEOF : InStream -> (Bool, InStream)
hIsEOF = hGenericGet (select IsEOF)

-- | Reads an `InStream` channel endpoint up to EOF, separating lines with the
-- newline character `\n`.
hGetContent : InStream -> (String, InStream)
hGetContent c =
  let (eof, c) = hIsEOF c in
  if eof
  then ("", c)
  else
    let (line,    c) = hGetLine c in
    let (content, c) = hGetContent c in
    (line ++ "\n" ++ content, c)

-- | Closes an `InStream` channel endpoint.
hCloseIn : InStream -> ()
hCloseIn c = c |> select Stop |> wait

hGenericGet_ : forall (a : *T) -> (InStream -> (a, InStream)) -> *?InStream -> a
hGenericGet_ get inp = 
  let (x, c) = get $ receive_ inp in
  hCloseIn c; 
  x

-- | `hGetChar` on an `*?InStream`
hGetChar_ : *?InStream -> Char
hGetChar_ = hGenericGet_ hGetChar

-- | `hGetLine` on an `*?InStream`
hGetLine_ : *?InStream -> String
hGetLine_ = hGenericGet_ hGetLine

-- *** Output Stream

-- | The `OutStream` type describes output streams (such as `stdout`, `stderr`
-- and write mode files). `PutChar` outputs a character, `PutStr` outputs a string,
-- and `PutStrLn` outputs a string followed by the newline character (`\n`).
-- Operations in this channel must end with the `Stop` option.
type OutStream : 1C
type OutStream = +{ PutStr   : !String ; OutStream
                  , PutStrLn : !String ; OutStream
                  , Stop     : Wait
                  }

hGenericPut : forall (a : *T) -> (OutStream -> !a; OutStream) -> a -> OutStream -> OutStream
hGenericPut sel x outStream = outStream |> sel |> send x

-- | Writes a String on an `OutStream` channel endpoint.
hPutStr : String -> OutStream -> OutStream
hPutStr = hGenericPut (select PutStr)

-- | Writes a string followed by newline on an `OutStream` channel endpoint.
hPutStrLn : String -> OutStream -> OutStream
hPutStrLn = hGenericPut (select PutStrLn)

-- | Writes a character on an `OutStream` channel endpoint.
hPutChar : Char -> OutStream -> OutStream
hPutChar c = hPutStr [c]

-- | Writes the string representation of a value on an `OutStream` channel
-- endpoint.
hPrint : forall (a : *T) -> a -> OutStream -> OutStream
hPrint @a = hPutStrLn . show

-- | Closes an `OutStream` channel endpoint.
hCloseOut : OutStream -> ()
hCloseOut c = c |> select Stop |> wait

hGenericPut_ : forall (a : *T) -> (a -> OutStream -> OutStream) -> a -> *?OutStream -> ()
hGenericPut_ sendF x outStream = 
  outStream |> receive_  |> sendF x |> hCloseOut

-- | Unrestricted version of `hPutChar`. Behaves the same, except it first
-- receives an `OutStream` channel endpoint (via session initiation), executes
-- an `hPutChar` and then closes the enpoint with `hCloseOut`.
hPutChar_ : Char -> *?OutStream -> ()
hPutChar_ = hGenericPut_ hPutChar

-- | Unrestricted version of `hPutStr`. Behaves similarly, except that it first
-- receives an `OutStream` channel endpoint (via session initiation), executes
-- an `hPutStr` and then closes the enpoint with `hCloseOut`.
hPutStr_ : String -> *?OutStream -> ()
hPutStr_ = hGenericPut_ hPutStr

-- | Unrestricted version of `hPutStrLn`. Behaves similarly, except that it
-- first receives an `OutStream` channel endpoint (via session initiation),
-- executes an `hPutStrLn` and then closes the enpoint with `hCloseOut`.
hPutStrLn_ : String -> *?OutStream -> ()
hPutStrLn_ = hGenericPut_ hPutStrLn

-- | Unrestricted version of `hPrint`. Behaves similarly, except that it first
-- receives an `OutStream` channel endpoint (via session initiation), executes
-- an `hPrint` and then closes the enpoint with `hCloseOut`.
hPrint_ : forall (a : *T) -> a -> *?OutStream -> ()
hPrint_ @a x c = hGenericPut_ (hPrint @a) x c

-- ** Standard I/O

-- *** stdin

-- Internal stdin functions
internalGetChar : () -> Char
internalGetChar = undefined
internalGetLine : () -> String
internalGetLine = undefined
internalIsEOF : () -> Bool
internalIsEOF = undefined

stdin : *?InStream
stdin = forkWith (runServer (\_ -> reader) ())
  where
    reader : Dual InStream -> ()
    reader (&GetChar r) = r |> send (internalGetChar ()) |> reader
    reader (&GetLine r) = r |> send (internalGetLine ()) |> reader
    reader (&IsEOF   r) = r |> send (internalIsEOF   ()) |> reader
    reader (&Stop    r) = r |> close

-- | Reads a single character from `stdin`.
getChar : () -> Char
getChar _ = hGetChar_ stdin

-- | Reads a single line from `stdin`. 
getLine : () -> String
getLine _ = hGetLine_ stdin

-- *** stdout and stderr

-- Internal output functions
internalPutStrOut, internalPutStrErr : String -> ()
internalPutStrOut = undefined
internalPutStrErr = undefined

stdout, stderr : *?OutStream
(stdout, stderr) = (outStream internalPutStrOut, outStream internalPutStrErr)
  where
    readApply : forall (a : *T) (b : 1S) (c : *T) -> (a -> c) -> ?a ; b -1-> b
    readApply f c =
      let (x, c) = receive c in f x; c

    printer : (String -> ()) -> Dual OutStream -> ()
    printer put (&PutStr p) =
      p |> readApply put |> printer put
    printer put (&PutStrLn p) =
      p |> readApply (\s -> put (s ++ "\n")) |> printer put
    printer _ (&Stop p) =
      p |> close

    outStream : (String -> ()) -> *?OutStream
    outStream put = forkWith (runServer (\_ -> printer put) ())

-- | Prints a character to `stdout`.
putChar : Char -> ()
putChar = flip hPutChar_ stdout

-- | Prints a string to `stdout`.
putStr : String -> ()
putStr = flip hPutStr_ stdout

-- | Prints a string to `stdout`, followed by the newline character `\n`.
putStrLn : String -> ()
putStrLn = flip hPutStrLn_ stdout

-- | Prints the string representation of a given value to `stdout`, followed by
-- the newline character `\n`.
print : forall (a : *T) -> a -> ()
print @a = putStrLn . show

-- ** Files

type FilePath : *T
type FilePath = String

-- | Opens a file for reading. The file is closed when the stream is.
openReadFile : FilePath -> InStream
openReadFile = undefined

-- | Opens a file for writing, discarding its current content.
openWriteFile : FilePath -> OutStream
openWriteFile = undefined

-- | Opens a file for writing, after its current content.
openAppendFile : FilePath -> OutStream
openAppendFile = undefined

-- | The entire content of a file, separating lines with `\n`.
readFile : FilePath -> String
readFile path =
  let (content, c) = hGetContent (openReadFile path) in
  hCloseIn c;
  content

-- | Writes a string to a file, discarding its current content.
writeFile : FilePath -> String -> ()
writeFile path content = openWriteFile path |> hPutStr content |> hCloseOut

-- | Writes a string to a file, after its current content.
appendFile : FilePath -> String -> ()
appendFile path content = openAppendFile path |> hPutStr content |> hCloseOut

-- ** Command line

-- | The arguments the program was run with, excluding the program name.
getArgs : () -> [String]
getArgs = undefined

-- | The name the program was run under.
getProgName : () -> String
getProgName = undefined

-- ** Environment

-- | The value of an environment variable, if it is set.
lookupEnv : String -> Maybe String
lookupEnv = undefined

-- | The value of an environment variable, which must be set.
getEnv : String -> String
getEnv name = orElse (lookupEnv name)
  where
    orElse : Maybe String -> String
    orElse (Just value) = value
    orElse Nothing      = error @String ("getEnv: no such environment variable: " ++ name)

-- | The whole environment, as name-value pairs.
getEnvironment : () -> [(String, String)]
getEnvironment = undefined

-- ** Exiting

-- | Terminates the program, reporting success for an exit code of 0 and failure
-- for any other. Called from a forked thread, terminates that thread alone.
exitWith : forall (a : 1T) -> Int -> a
exitWith @a = undefined

exitSuccess, exitFailure : forall (a : 1T) -> () -> a
exitSuccess @a _ = exitWith @a 0
exitFailure @a _ = exitWith @a 1
