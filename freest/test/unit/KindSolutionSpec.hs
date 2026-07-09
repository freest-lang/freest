module KindSolutionSpec (spec) where

import Syntax.Base
import Syntax.Kind (Kind(..), Multiplicity(..), pattern Un, pattern VarM, Prekind(..))
import Syntax.Type.Kinded qualified as TK
import Validation.LocalInference.Solution

import Data.Map.Strict qualified as Map
import Test.Hspec

spec :: Spec
spec = describe "Kind solution" $ do
  it "resolves the multiplicity and prekind of a proper kind" $
    resolveKind sol (Proper nullSpan (mvar 1) (pvar 1))
      `shouldBe` Proper nullSpan (Un nullSpan) Session

  it "recurses through arrows" $
    resolveKind sol (Arrow nullSpan (kvar 1) (Proper nullSpan (mvar 1) Top))
      `shouldBe` Arrow nullSpan lt (Proper nullSpan (Un nullSpan) Top)

  it "resolves a whole-kind variable to its binding" $
    resolveKind sol (kvar 1) `shouldBe` lt

  it "chases a chain of whole-kind bindings to a fixpoint" $
    resolveKind solChain (kvar 2) `shouldBe` lt

  it "guards against cyclic whole-kind bindings (no loop)" $
    resolveKind solCycle (kvar 1) `shouldBe` kvar 1

  it "leaves object-level (rigid) variables untouched" $
    resolveKind sol (Var nullSpan ObjLv (v "κ" 1))
      `shouldBe` Var nullSpan ObjLv (v "κ" 1)

  it "resolves kind annotations inside a type" $
    TK.kindOf (resolveType sol (TK.Var nullSpan (Proper nullSpan (mvar 1) (pvar 1)) ObjLv (v "a" 1)))
      `shouldBe` Proper nullSpan (Un nullSpan) Session
  where
    v pre n = Variable nullSpan (pre ++ show n) n
    kvar n  = Var nullSpan UnifLv (v "κ" n)
    mvar n  = VarM nullSpan UnifLv (v "φ" n)
    pvar n  = VarPK UnifLv (v "ψ" n)
    lt      = Proper nullSpan (Lin nullSpan) Top

    sol = KindSolution
      { kindVars = Map.fromList [(v "κ" 1, lt)]
      , prekinds = Map.fromList [(v "ψ" 1, Session)]
      , mults    = Map.fromList [(v "φ" 1, Un nullSpan)]
      }
    solChain = sol { kindVars = Map.fromList [(v "κ" 2, kvar 1), (v "κ" 1, lt)] }
    solCycle = sol { kindVars = Map.fromList [(v "κ" 1, kvar 2), (v "κ" 2, kvar 1)] }