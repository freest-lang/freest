-- | The Prelude: a standard module. The Prelude is imported by default
-- into all FreeST modules.
module Prelude where

-- * Undefined. Useful for builtins, but should also be builtin...
undefined : forall (a : *T) -> a
undefined @a = undefined @a

-- * Error
error : forall (a : *T) -> String -> a
error = undefined @(forall (a : *T) -> String -> a)

-- * Standard types, classes and related functions

-- ** Basic datatypes

type Bool : *T
data Bool = True | False

(||), (&&) : Bool -> Bool -> Bool
(||) = undefined @(Bool -> Bool -> Bool)
(&&) = undefined @(Bool -> Bool -> Bool)

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
ord = undefined @(Char -> Int)

chr : Int -> Char
chr = undefined @(Int -> Char)

type String : *T
type String = [Char]

show : forall (a : *T) -> a -> String
show = undefined @(forall (a : *T) -> a -> String)

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
(< ) = undefined @(Int -> Int -> Bool)
(<=) = undefined @(Int -> Int -> Bool)
(==) = undefined @(Int -> Int -> Bool)
(>=) = undefined @(Int -> Int -> Bool)
(> ) = undefined @(Int -> Int -> Bool)
(/=) = undefined @(Int -> Int -> Bool)

(>.), (<.), (>=.), (<=.) : Float -> Float -> Bool
(>.)  = undefined @(Float -> Float -> Bool)
(<.)  = undefined @(Float -> Float -> Bool)
(>=.) = undefined @(Float -> Float -> Bool)
(<=.) = undefined @(Float -> Float -> Bool)

-- ** Numeric functions

-- *** Int
(+), (-), (*), (/), (^), subtract
   , quot, rem, div, mod
   , min, max
   , gcd, lcm 
   : Int -> Int -> Int
(+)      = undefined @(Int -> Int -> Int)
(-)      = undefined @(Int -> Int -> Int)
(*)      = undefined @(Int -> Int -> Int)
(/)      = undefined @(Int -> Int -> Int)
(^)      = undefined @(Int -> Int -> Int)
quot     = undefined @(Int -> Int -> Int)
rem      = undefined @(Int -> Int -> Int) 
div      = undefined @(Int -> Int -> Int)
mod      = undefined @(Int -> Int -> Int)
min      = undefined @(Int -> Int -> Int)
max      = undefined @(Int -> Int -> Int)
subtract = undefined @(Int -> Int -> Int)
gcd      = undefined @(Int -> Int -> Int)
lcm      = undefined @(Int -> Int -> Int)

succ, pred, abs, negate : Int -> Int
succ   = undefined @(Int -> Int)
pred   = undefined @(Int -> Int)
abs    = undefined @(Int -> Int)
negate = undefined @(Int -> Int)

even, odd : Int -> Bool
even = undefined @(Int -> Bool)
odd  = undefined @(Int -> Bool)

-- *** Float
(+.), (-.), (*.), (/.), (**), maxF, minF, logBase : Float -> Float -> Float
(+.)    = undefined @(Float -> Float -> Float)
(-.)    = undefined @(Float -> Float -> Float)
(*.)    = undefined @(Float -> Float -> Float)
(/.)    = undefined @(Float -> Float -> Float)
(**)    = undefined @(Float -> Float -> Float)
maxF    = undefined @(Float -> Float -> Float)
minF    = undefined @(Float -> Float -> Float)
logBase = undefined @(Float -> Float -> Float)

absF, negateF, recip
    , exp, log, sqrt 
    , log1p, expm1, log1pexp, log1mexp
    , sin, cos, tan, asin, acos, atan, sinh, cosh, tanh 
    : Float -> Float
absF     = undefined @(Float -> Float)
negateF  = undefined @(Float -> Float)
recip    = undefined @(Float -> Float)
exp      = undefined @(Float -> Float)
log      = undefined @(Float -> Float)
sqrt     = undefined @(Float -> Float)
log1p    = undefined @(Float -> Float)
expm1    = undefined @(Float -> Float)
log1pexp = undefined @(Float -> Float)
log1mexp = undefined @(Float -> Float)
sin      = undefined @(Float -> Float)
cos      = undefined @(Float -> Float)
tan      = undefined @(Float -> Float)
asin     = undefined @(Float -> Float)
acos     = undefined @(Float -> Float)
atan     = undefined @(Float -> Float)
sinh     = undefined @(Float -> Float)
cosh     = undefined @(Float -> Float)
tanh     = undefined @(Float -> Float)

truncate, round ,ceiling, floor : Float -> Int
truncate = undefined @(Float -> Int)
round    = undefined @(Float -> Int)
ceiling  = undefined @(Float -> Int)
floor    = undefined @(Float -> Int)

pi : Float
pi = undefined @Float

fromInteger : Int -> Float
fromInteger = undefined @(Int -> Float)

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
    go x | p x          = x
         | otherwise    = go (f x)

(;) : forall (a : *T) (b : 1T) -> a -> b -> b
(;) @a @b _ x = x

-- * Lists
(++) : forall #m (a : m T) -> [a] -> [a] -m-> [a]
(++) #m @a []      ys = ys
(++) #m @a (x::xs) ys = x :: ((++) #m xs ys) 

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

-- * Concurrency

fork : forall #m (a : *T) -> (() -m-> a) -> ()
fork = undefined @(forall #m (a : *T) -> (() -m-> a) -> ())

send : forall (a : 1T) -> a -> forall (b : 1S) -> !a;b -1-> b
send = undefined @(forall (a : 1T) -> a -> forall (b : 1S) -> !a;b -1-> b)

receive : forall (a : 1T) (b : 1S) -> ?a;b -> (a, b)
receive = undefined @(forall (a : 1T) (b : 1S) -> ?a;b -> (a, b))

wait : Wait -> ()
wait = undefined @(Wait -> ())

close : Close -> ()
close = undefined @(Close -> ())

-- | Sends a value on a given channel and then waits for the channel to be
-- | closed. Returns ().
sendAndWait : forall (a : 1T) -> a -> !a ; Wait -1-> ()
sendAndWait @a x c = c |> send x |> wait

-- | Sends a value on a given channel and then closes the channel.
-- | Returns ().
sendAndClose : forall (a : 1T) -> a -> !a ; Close -1-> ()
sendAndClose @a x c = c |> send x |> close

-- | Receives a value from a channel that continues to `Wait`, closes the 
-- | continuation and returns the value.
-- | 
-- | ```
-- | main : ()
-- | main =
-- |   -- create channel endpoints
-- |   let (c, s) = new @(?String ; Wait) () in
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

-- | Receives a value from a linear channel and applies a function to it.
-- | Discards the result and returns the continuation channel.
-- | 
-- | ```
-- | main : ()
-- | main =
-- |   -- create channel endpoints
-- |   let (c, s) = new @(?String ; Wait) () in
-- |   -- fork a thread that prints the received value (and closes the channel)
-- |   fork (\_:() -1-> c |> readApply @String @End putStrLn |> wait);
-- |   -- send a string through the channel (and close it)
-- |   s |> send "Hello!" |> close
-- | ```
readApply : forall (a : *T) (b : 1S) -> (a -> ()) {- Consumer a -} -> ?a ; b -1-> b
readApply @a @b f c =
  let (x, c) = receive c in
  f x;
  c

-- | Sends a value on a star channel. Unrestricted version of `send`.
send_ : forall (a : 1T) -> a -> *!a -1-> ()
send_ = undefined @(forall (a : 1T) -> a -> *!a -1-> ()) -- @a x c = c |> send x |> sink @*!a

-- | Receives a value from a star channel. Unrestricted version of `receive`.
receive_ : forall (a : 1T) -> *?a -> a
receive_ = undefined @(forall (a : 1T) -> *?a -> a) -- @a c =  c |> receive @a @*?a |> fst @a @*?a

-- | Session initiation. Accepts a request for a linear session on a shared
-- channel. The requester uses a conventional `receive` to obtain the channel
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
-- main : ()
-- main =
--   -- fork a thread that receives a string and prints
--   let c = forkWith @(!String ; Wait) @() (\s:(?String ; End) -1-> s |> receiveAndWait @String |> putStrLn) in
--   -- send the string to be printed
--   c |> send "Hello!" |> wait
-- ```
forkWith : forall #m (a : 1C) (b : *T) -> (Dual a -m-> b) -> a
forkWith #m @a @b f =
  let (x, y) = channel @a in
  fork (\(_ : ()) -1-> f y);
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
-- runCounterServer : dualof SharedCounter -> Diverge
-- runCounterServer = runServer @Counter @Int counterService 0 
-- ```
runServer : forall (a : 1C) (b : *T) -> (b -> Dual a -1-> b) -> b -> *!a -> Void @*T
runServer @a @b handle state c =
  runServer handle (handle state (accept c)) c 

-- | Discards an unrestricted value
sink : forall (a : *T) -> a -> ()
sink @a _ = ()

-- | Executes a thunk n times, sequentially 
-- ```
-- main : ()
-- main = 
--   -- print "Hello!" 5 times sequentially
--   repeat @() 5 (\_:() -> putStrLn "Hello!")
-- ```
repeat : forall (a : *T) -> Int -> (() -> a) -> ()
repeat @a n thunk =
  if n <= 0
  then ()
  else 
    thunk ();
    repeat (n - 1) thunk

-- | Forks n identical threads. Works the same as a `repeat` call but in parallel
-- instead of sequentially. 
-- ```
-- main : ()
-- main = 
--   -- print "Hello!" 5 times in parallel
--   parallel @() 5 (\_:() -> putStrLn "Hello!")
-- ```
parallel : forall (a : *T) -> Int -> (() -> a) -> ()
parallel @a n thunk = repeat @() n (\(_ : ()) -> fork @a thunk)

-- * I/O

-- ** I/O Streams

-- *** Input Stream

-- | The `InStream` type describes input streams (such as `stdin` and read
-- files). `GetChar` reads a single character, `GetLine` reads a line, and
-- `IsEOF` checks for the EOF (End-Of-File) token, i.e., if an input stream
-- reached the end. Operations in this channel end with the `SWait` option.
type InStream : 1C
type InStream = +{ GetChar: ?Char   ; InStream
                 , GetLine: ?String ; InStream
                 , IsEOF  : ?Bool   ; InStream
                 , SWait  : Wait
                 }

-- | Unrestricted session type for the `OutStream` type.
type InStreamProvider : *C
type InStreamProvider = *?InStream

-- | Closes an `InStream` channel endpoint. Behaves as a `close`.
hCloseIn : InStream -> ()
hCloseIn c = c |> select SWait |> wait

hGenericGet : forall (a : *T) -> (InStream -> ?a; InStream) -> InStream -> (a, InStream)
hGenericGet @a sel c = receive (sel c)

-- | Reads a character from an `InStream` channel endpoint. Behaves as 
-- `|> select GetChar |> receive`.
hGetChar : InStream -> (Char, InStream)
hGetChar = hGenericGet (\(c : InStream) -> select GetChar c)

-- | Reads a line (as a string) from an `InStream` channel endpoint. Behaves as 
-- `|> select GetLine |> receive`.
hGetLine : InStream -> (String, InStream)
hGetLine = hGenericGet (\(c : InStream) -> select GetLine c)

-- | Checks if an `InStream` reached the EOF token that marks where no more input can be read. 
-- Does the same as `|> select IsEOF |> receive`.
hIsEOF : InStream -> (Bool, InStream)
hIsEOF = hGenericGet (\(c : InStream) -> select IsEOF c)

-- | Reads the entire content from an `InStream` (i.e. until EOF is reached). Returns the content
-- as a single string and the continuation channel.
hGetContent : InStream -> (String, InStream)
hGetContent c = 
  let (isEOF, c) = hIsEOF c in
  if isEOF
  then ("", c)
  else 
    let (line, c) = hGetLine c in 
    let (contents, c) = hGetContent c in
    ((++) line ((++) "\n" contents), c)

hGenericGet_ : forall (a : *T) -> (InStream -> (a, InStream)) -> InStreamProvider -> a
hGenericGet_ @a getF inp = 
  let (x, c) = getF $ receive_ inp in
  hCloseIn c; 
  x

-- | Unrestricted version of `hGetChar`. Behaves the same, except it first receives an `InStream` 
-- channel endpoint (via session initiation), executes an `hGetChar` and then closes the 
-- enpoint with `hCloseIn`.
hGetChar_ : InStreamProvider -> Char
hGetChar_ = hGenericGet_ hGetChar

-- | Unrestricted version of `hGetLine`. Behaves the same, except it first receives an `InStream` 
-- channel endpoint (via session initiation), executes an `hGetLine` and then closes the 
-- enpoint with `hCloseIn`.
hGetLine_ : InStreamProvider -> String
hGetLine_ = hGenericGet_ hGetLine

-- | Unrestricted version of `hGetContent`. Behaves the same, except it first receives an `InStream`
-- channel endpoint (via session initiation), executes an `hGetContent` and then closes the
-- endpoint with `hCloseIn`.
hGetContent_ : InStreamProvider -> String
hGetContent_ inp = 
  let (s, c) = receive_ inp |> hGetContent in
  hCloseIn c;
  s

-- *** Output Stream

-- | The `OutStream` type describes output streams (such as `stdout`, `stderr`
-- and write mode files). `PutChar` outputs a character, `PutStr` outputs a string,
-- and `PutStrLn` outputs a string followed by the newline character (`\n`).
-- Operations in this channel must end with the `Close` option.
type OutStream : 1C
type OutStream = +{ PutChar : !Char ; OutStream
                  , PutStr  : !String ; OutStream
                  , PutStrLn: !String ; OutStream
                  , SWait   : Wait
                  }

-- | Unrestricted session type for the `OutStream` type.
type OutStreamProvider : *C
type OutStreamProvider = *?OutStream

-- | Closes an `OutStream` channel endpoint. Behaves as a `close`.
hCloseOut : OutStream -> ()
hCloseOut c = c |> select SWait |> wait

hGenericPut : forall (a : *T) -> (OutStream -> !a; OutStream) -> a -> OutStream -> OutStream
hGenericPut @a sel x outStream = sel outStream |> send x

-- | Sends a character through an `OutStream` channel endpoint. Behaves as 
-- `|> select PutChar |> send`.
hPutChar : Char -> OutStream -> OutStream
hPutChar = hGenericPut (\(ch : OutStream) -> select PutChar ch)

-- | Sends a String through an `OutStream` channel endpoint. Behaves as 
-- `|> select PutString |> send`.
hPutStr : String -> OutStream -> OutStream
hPutStr = hGenericPut (\(c : OutStream) -> select PutStr c)

-- | Sends a string through an `OutStream` channel endpoint, to be output with
-- the newline character. Behaves as `|> select PutStringLn |> send`.
hPutStrLn : String -> OutStream -> OutStream
hPutStrLn = hGenericPut (\(c : OutStream) -> select PutStrLn c)

-- | Sends the string representation of a value through an `OutStream` channel
-- endpoint, to be outputed with the newline character. Behaves as `hPutStrLn
-- (show @t v)`, where `v` is the value to be sent and `t` its type.
hPrint : forall (a : *T) -> a -> OutStream -> OutStream
hPrint @a x = hPutStrLn (show x)

hGenericPut_ : forall (a : *T) -> (a -> OutStream -> OutStream) -> a -> OutStreamProvider -> ()
hGenericPut_ @a putF x outProv = 
  hCloseOut $ putF x $ receive_ outProv 

-- | Unrestricted version of `hPutChar`. Behaves the same, except it first
-- receives an `OutStream` channel endpoint (via session initiation), executes
-- an `hPutChar` and then closes the enpoint with `hCloseOut`.
hPutChar_ : Char -> OutStreamProvider -> ()
hPutChar_ = hGenericPut_ hPutChar

-- | Unrestricted version of `hPutStr`. Behaves similarly, except that it first
-- receives an `OutStream` channel endpoint (via session initiation), executes
-- an `hPutStr` and then closes the enpoint with `hCloseOut`.
hPutStr_ : String -> OutStreamProvider -> ()
hPutStr_ = hGenericPut_ hPutStr

-- | Unrestricted version of `hPutStrLn`. Behaves similarly, except that it
-- first receives an `OutStream` channel endpoint (via session initiation),
-- executes an `hPutStrLn` and then closes the enpoint with `hCloseOut`.
hPutStrLn_ : String -> OutStreamProvider -> ()
hPutStrLn_ = hGenericPut_ hPutStrLn

-- | Unrestricted version of `hPrint`. Behaves similarly, except that it first
-- receives an `OutStream` channel endpoint (via session initiation), executes
-- an `hPrint` and then closes the enpoint with `hCloseOut`.
hPrint_ : forall (a : *T) -> a -> OutStreamProvider -> ()
hPrint_ @a x c = hGenericPut_ (hPrint @a) x c

-- ** Standard I/O

-- *** stdin

-- | Standard input stream. Reads from the console.
stdinChan : (InStreamProvider, Dual InStreamProvider)
stdinChan = channel @InStreamProvider

stdin : InStreamProvider
stdin = let (i, _) = stdinChan in i

dualStdin : Dual InStreamProvider
dualStdin = let (_, o) = stdinChan in o

-- | Reads a single character from `stdin`.
getChar : () -> Char
getChar _ = hGetChar_ stdin

-- | Reads a single line from `stdin`. 
getLine : () -> String
getLine _ = hGetLine_ stdin

-- **** Internal stdin functions

internalGetChar : () -> Char
internalGetChar = undefined @(() -> Char)
internalGetLine : () -> String
internalGetLine = undefined @(() -> String)
internalGetContents : () -> String
internalGetContents = undefined @(() -> String)

runReader : () -> Dual InStream -1-> ()
runReader _ (&GetChar reader) = runReader () $ send (internalGetChar ()) reader
runReader _ (&GetLine reader) = runReader () $ send (internalGetLine ()) reader
runReader _ (&IsEOF   reader) = runReader () $ send False                reader -- stdin is always open
runReader _ (&SWait   reader) = close reader

runStdin : ()
runStdin = fork (\(_ : ()) -1-> runServer runReader () dualStdin)

-- *** stdout

-- | Standard output stream. Prints to the console.
stdoutChan : (OutStreamProvider, Dual OutStreamProvider)
stdoutChan = channel @OutStreamProvider

stdout : OutStreamProvider
stdout = let (o,_) = stdoutChan in o

dualStdout : Dual OutStreamProvider
dualStdout = let (_,i) = stdoutChan in i

-- | Prints a character to `stdout`. Behaves the same as `hPutChar_ c stdout`, where `c`
-- is the character to be printed.
putChar : Char -> ()
putChar = flip #* #* #* hPutChar_ stdout

-- | Prints a string to `stdout`. Behaves the same as `hPutStr_ s stdout`, where `s` is
-- the string to be printed.
putStr : String -> ()
putStr = flip #* #* #* hPutStr_ stdout

-- | Prints a string to `stdout`, followed by the newline character `\n`. Behaves
-- as `hPutStrLn_ s stdout`, where `s` is the string to be printed.
putStrLn : String -> ()
putStrLn = flip #* #* #* hPutStrLn_ stdout

-- | Prints the string representation of a given value to `stdout`, followed by
-- the newline character `\n`. Behaves the same as `hPrint_ @t v stdout`, where `v` is
-- the value to be printed and `t` its type.
print : forall (a : *T) -> a -> ()
print @a x = putStrLn $ show x

-- **** Internal stdout functions

internalPutStrOut : String -> ()
internalPutStrOut = undefined @(String -> ())

runPrinter : () -> Dual OutStream -1-> ()
runPrinter _ (&PutChar printer) = 
  readApply (\(c : Char) -> internalPutStrOut (show c)) printer 
    |> runPrinter ()
runPrinter _ (&PutStr printer) = 
  readApply internalPutStrOut printer 
    |> runPrinter ()
runPrinter _ (&PutStrLn printer) = 
  readApply (\(s : String) -> internalPutStrOut (s ++ "\n")) printer 
    |> runPrinter ()
runPrinter _ (&SWait printer) = 
  close printer

runStdout  : ()
runStdout = fork (\(_ : ()) -1-> runServer runPrinter () dualStdout)
