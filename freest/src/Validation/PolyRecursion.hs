module Validation.PolyRecursion ( polyrec ) where

import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as T
import UI.Error qualified as E

polyrec :: T.KindedType -> M.KindedModule -> Either [E.Error] ()
polyrec _ _ = Right ()
