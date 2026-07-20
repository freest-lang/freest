module KindUnifierSpec (spec) where

import Syntax.Base
import Syntax.Kind (Kind(..), Multiplicity(..), BaseKind(..))
import Syntax.Provenance (Origin(..))
import Validation.LocalInference.Kinds
import Validation.LocalInference.BaseKinds (solveBaseKindConstraints, applyBaseKindSubst)

import Data.Either (isLeft)
import Data.Map.Strict qualified as Map
import Test.Hspec

spec :: Spec
spec = describe "Kind unifier (K1 <: K2)" $ do
  it "resolves a whole-kind variable against a proper kind, emitting one leaf each" $
    case unifyKindSub o (kv 1) (proper lin Top) of
      Right u -> do
        fmap isProper (Map.lookup (var 1) (kindSubst u)) `shouldBe` Just True
        length (multConstraints u)    `shouldBe` 1
        length (baseKindConstraints u) `shouldBe` 1
      Left _ -> expectationFailure "expected success"

  it "aliases two whole-kind variables without promoting to proper" $
    case unifyKindSub o (kv 1) (kv 2) of
      Right u -> Map.lookup (var 1) (kindSubst u) `shouldSatisfy` isVar
      Left _  -> expectationFailure "expected success"

  it "recurses through arrows, binding both ends" $
    case unifyKindSub o (arrow (kv 1) (kv 2)) (arrow (proper lin Top) (proper lin Session)) of
      Right u -> Map.size (kindSubst u) `shouldBe` 2
      Left _  -> expectationFailure "expected success"

  it "rejects a proper-vs-arrow mismatch" $
    isLeft (unifyKindSub o (proper lin Top) (arrow (proper lin Top) (proper lin Top)))
      `shouldBe` True

  it "hands baseKind leaves to the baseKind solver (a free leaf resolves to T)" $
    case unifyKindSub o (kv 1) (proper lin Top) of
      Right u -> case (Map.lookup (var 1) (kindSubst u), solveBaseKindConstraints (baseKindConstraints u)) of
        (Just (Proper _ _ p), Right psub) -> applyBaseKindSubst psub p `shouldBe` Top
        _ -> expectationFailure "expected a proper leaf and a baseKind solution"
      Left _ -> expectationFailure "expected success"
  where
    o        = Origin nullSpan
    var n    = Variable nullSpan ("κ" ++ show n) n
    kv n     = Var nullSpan UnifLv (var n)
    lin      = Lin nullSpan
    proper   = Proper nullSpan
    arrow    = Arrow nullSpan
    isProper = \case Proper{} -> True; _ -> False
    isVar    = \case Just Var{} -> True; _ -> False
