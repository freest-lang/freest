module MultSubSolverSpec (spec) where

import Syntax.Base
import Syntax.Kind (Multiplicity(..), pattern Un)
import Syntax.Provenance (Origin(..))
import Validation.LocalInference.Multiplicities

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Test.Hspec

spec :: Spec
spec = describe "Multiplicity subkinding solver (Fig. 14 descent)" $ do
  it "lowers a variable to a rigid upper bound, not to *" $
    solve [sub (v 1) (r [1])] (v 1) `shouldBe` r [1]
  it "meets several rigid upper bounds" $
    solve [sub (v 1) (r [1, 2]), sub (v 1) (r [2, 3])] (v 1) `shouldBe` r [2]
  it "propagates a bound through a variable chain" $
    solve [sub (v 1) (v 2), sub (v 2) (r [1])] (v 1) `shouldBe` r [1]
  it "leaves a variable bounded only by the top unsolved" $
    Map.lookup (var 1) (solveMultSubs Set.empty [sub (v 1) lin]) `shouldBe` Nothing
  it "aliases a mutual pair to its *-defaulting side" $
    solveWith (Set.singleton (var 1)) [sub (v 1) (v 2), sub (v 2) (v 1)] (v 2) `shouldBe` v 1
  it "raises a *-defaulting variable to its rigid lower bound" $
    solveWith (Set.singleton (var 1)) [sub (r [1]) (v 1)] (v 1) `shouldBe` r [1]
  it "reports a constraint the solution violates" $
    unsat [sub (r [1, 2]) (v 1), sub (v 1) (r [1])] `shouldBe` True
  where
    o = Origin nullSpan
    var n = Variable nullSpan ("φ" ++ show n) n
    obj n = Variable nullSpan ("m" ++ show n) (100 + n)
    v n   = Sup nullSpan [(UnifLv, var n)]
    r ns  = Sup nullSpan [(ObjLv, obj n) | n <- ns]
    lin   = Lin nullSpan
    sub l u = MultSub l u o

    solve = solveWith Set.empty
    solveWith undefs cs = applyMultSubst (solveMultSubs undefs cs)
    unsat cs =
      let σ = solveMultSubs Set.empty cs
          resolve m = case applyMultSubst σ m of
            Sup s as | any (solvable . fst) as -> Lin s
            m'                                 -> m'
      in maybe False (const True) (unsatisfiedMultSub resolve cs)
