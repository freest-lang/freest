module LinConsumedInUnMultForall where

multAbs : !Int; Wait -> forall #m -> Int -m-> Wait
multAbs c #a x = send x c  