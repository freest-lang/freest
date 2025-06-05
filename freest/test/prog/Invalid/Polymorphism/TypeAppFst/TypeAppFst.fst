module TypeAppFst where

-- |The elements in the state
type File : *T
type File = Int

-- |A bag of files managed by a shared channel.
-- |The elements in the bag are messages in transit.
type State : *T
type State = (*?File, *!File)

-- |Read a file from the state
readFrom : State -> File
readFrom state =
  fst @File @State $ receive $ fst @*?File @*!File state
  -- Should be  
  -- fst @File @*?File $ receive $ fst @*?File @*!File state
