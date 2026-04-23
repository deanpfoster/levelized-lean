import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.CombinatoryLogic.Defs
import CslibHeaders.Proofs.Languages.CombinatoryLogic.Defs

/-! # SKI Combinatory Logic — definitions and reduction rules

  Vocabulary:
    SKI           — the type of SKI combinator expressions (S, K, I, app)
    SKI.Red       — single-step reduction relation on SKI terms
    SKI.app (⬝)   — application of SKI terms
    SKI.size      — number of combinators in a term
    SKI.applyList — apply a term to a list of terms

  Multi-step reduction (↠) is the reflexive-transitive closure of Red (⭢).
-/

open Cslib Cslib.SKI

-- Multi-step reduction of primitive combinators
ProvenTheorem MRed.S : ∀ (x y z : SKI), (S ⬝ x ⬝ y ⬝ z) ↠ (x ⬝ z ⬝ (y ⬝ z))
ProvenTheorem MRed.K : ∀ (x y : SKI), (K ⬝ x ⬝ y) ↠ x
ProvenTheorem MRed.I : ∀ (x : SKI), (I ⬝ x) ↠ x

-- Congruence rules for multi-step reduction
ProvenTheorem MRed.head : ∀ {a a' : SKI} (b : SKI), a ↠ a' → (a ⬝ b) ↠ (a' ⬝ b)
ProvenTheorem MRed.tail : ∀ (a : SKI) {b b' : SKI}, b ↠ b' → (a ⬝ b) ↠ (a ⬝ b')

-- Parallel multi-step reduction
ProvenTheorem parallel_mRed : ∀ {a a' b b' : SKI}, a ↠ a' → b ↠ b' → (a ⬝ b) ↠ (a' ⬝ b')

-- Join congruence
ProvenTheorem mJoin_red_head : ∀ {x x' : SKI} (y : SKI),
  Relation.MJoin Red x x' → Relation.MJoin Red (x ⬝ y) (x' ⬝ y)
ProvenTheorem mJoin_red_tail : ∀ (x : SKI) {y y' : SKI},
  Relation.MJoin Red y y' → Relation.MJoin Red (x ⬝ y) (x ⬝ y')
