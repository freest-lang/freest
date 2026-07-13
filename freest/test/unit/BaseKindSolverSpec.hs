module BaseKindSolverSpec (spec) where

import Syntax.Base
import Syntax.Kind (BaseKind(..))
import Syntax.Provenance (Origin(..))
import Validation.LocalInference.BaseKinds

import Test.Hspec

spec :: Spec
spec = describe "BaseKind chain solver (C <: S <: T)" $ do
  it "leaves an unconstrained variable at the top (T)" $
    solveFor [sub Top (v 1)] (v 1) `shouldBe` Just Top
  it "lowers a variable to a Session upper bound" $
    solveFor [sub (v 1) Session] (v 1) `shouldBe` Just Session
  it "lowers a variable to a Channel upper bound" $
    solveFor [sub (v 1) Channel] (v 1) `shouldBe` Just Channel
  it "propagates a bound through a variable chain" $
    solveFor [sub (v 1) (v 2), sub (v 2) Channel] (v 1) `shouldBe` Just Channel
  it "assigns the greatest lower bound (meet)" $
    solveFor [MeetBaseKind o (var 1) [Session, Channel]] (v 1) `shouldBe` Just Channel
  it "assigns the least upper bound (join)" $
    solveFor [JoinBaseKind o (var 1) [Session, Channel]] (v 1) `shouldBe` Just Session
  it "fails an unsatisfiable lower/upper pair (S <: ψ <: C)" $
    solveFor [sub Session (v 1), sub (v 1) Channel] (v 1) `shouldBe` Nothing
  it "does not solve object-level (rigid) variables" $
    solveFor [sub (v 1) Session] (rv 9) `shouldBe` Just (rv 9)
  where
    o = Origin nullSpan
    var n = Variable nullSpan ("ψ" ++ show n) n
    v  n  = VarBK UnifLv (var n)  -- a solvable baseKind variable
    rv n  = VarBK ObjLv (var n)   -- a rigid baseKind variable
    sub   = SubBaseKind o
    -- Resolve @target@ under the solution, or 'Nothing' if unsatisfiable.
    solveFor cs target =
      either (const Nothing) (Just . (`applyBaseKindSubst` target))
        (solveBaseKindConstraints cs)
