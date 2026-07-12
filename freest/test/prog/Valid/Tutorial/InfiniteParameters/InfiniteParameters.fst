type IntSink = Int -> IntSink

-- Partially consumes an IntSink: feeds it five Ints and returns the resulting
-- IntSink. Since IntSink = Int -> IntSink never bottoms out into a non-function,
-- applying it to finitely many Ints always yields another IntSink, so an IntSink
-- can only ever be consumed partially, never to completion.
partialConsume : IntSink -> IntSink
partialConsume f = f 1 2 3 4 5

_ = print True