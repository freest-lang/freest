{- |
Module      :  ArithExprServer
Description :  Server that computes arithmetic expressions
Copyright   :  (c) Bernardo Almeida, Andreia Mordido, Vasco T. Vasconcelos

This example is from Thiemann and Vasconcelos:
"Context-Free Session Types" (listing 3)

The interaction with this server is performed by sending
an arithmetic expression. The server reads the expression,
computes its value and returns the value on the same channel.

This version uses the pipeline operator |>.

-}

module Pipeline where

type TermChannel : 1S
type TermChannel  = +{
   Const: !Int,
   Add: TermChannel;TermChannel,
   Mult: TermChannel;TermChannel
 }

-- Read an arithmetic expression in the front of a channel; compute
-- its value; return the pair composed of this value and the channel
-- residual.
receiveEval : forall (a : 1S). Dual TermChannel;a -> (Int, a)
receiveEval @a c =
  case c of
    &Const c ->
      receive @Int @a c
    &Add c ->
      let (n1, c) = receiveEval @(Dual TermChannel ; a) c in
      let (n2, c) = receiveEval @a c in
      (n1 + n2, c)
    &Mult c ->
      let (n1, c) = receiveEval @(Dual TermChannel ; a) c in
      let (n2, c) = receiveEval @a c in
      (n1 * n2, c)

-- Read an arithmetic expression from a channel; compute its value;
-- return the value on the same channel.
computeService : Dual TermChannel;!Int;Close -> ()
computeService c =
  let (n1, c1) = receiveEval @(!Int ; Close) c in
  close (send @Int n1 @Close c1)

-- Compute 5 + (7 * 9); return the result
client : TermChannel;?Int;Wait -> Int
client c =
  receiveAndWait @Int
    (send @Int 9 @(?Int;Wait)
      (select Const
        (send @Int 7 @(TermChannel;?Int;Wait)
          (select Const 
            (select Mult
              (send @Int 5 @(TermChannel;?Int;Wait)
                (select Const
                  (select Add c))))))))

main : Int
main =
  let (w, r) = channel @(Dual TermChannel;!Int;Close) in
  let _ = fork @() (\(_:()) 1-> computeService w) in
  client r
