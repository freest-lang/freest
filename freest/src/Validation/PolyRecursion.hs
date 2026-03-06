module Validation.PolyRecursion ( polyRec ) where

import Syntax.Base
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as T
import Syntax.Kind qualified as K
import UI.Error qualified as E
import Data.Map.Strict qualified as Map

polyRec :: M.KindedModule -> Either [E.Error] ()
polyRec m = Map.foldlWithKey polyRecType (Right ()) (M.typeDecls m)
    where
        polyRecType :: Either [E.Error] () -> Identifier -> T.KindedType -> Either [E.Error] ()
        polyRecType acc id (T.Abs _ aks t) = polyRecAbs acc id aks t
        polyRecType acc _  _ = acc
        polyRecAbs :: Either [E.Error] () -> Identifier -> [(Variable, K.Kind)] -> T.KindedType -> Either [E.Error] ()
        polyRecAbs acc id aks (T.AppTName _ id' us) | id == id' && paramsEqToArgs aks us = acc
        polyRecAbs acc id _ t@(T.AppTName _ id' _)  | id == id' = addTo acc (E.PolymorphicTypeRecursion (getSpan t) t)
        polyRecAbs acc id aks (T.App _ t us) = foldl (`polyRecType` id) acc (t:us)

paramsEqToArgs :: [(Variable, K.Kind)] -> [T.KindedType] -> Bool
paramsEqToArgs [] [] = True
paramsEqToArgs ((a, _):aks) (T.Var _ _ b:us) = a == b && paramsEqToArgs aks us
paramsEqToArgs _ _ = False

addTo :: Either [E.Error] () -> E.Error -> Either [E.Error] ()
addTo (Right _) e = Left [e]
addTo (Left es) e = Left (es ++ [e])
