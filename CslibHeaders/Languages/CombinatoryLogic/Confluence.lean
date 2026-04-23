import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.CombinatoryLogic.Confluence
import CslibHeaders.Proofs.Languages.CombinatoryLogic.Confluence

/-! # SKI Reduction is Confluent — the Church-Rosser Theorem

  Vocabulary:
    ParallelReduction (⭢ₚ) — simultaneous reduction of disjoint redexes

  The proof follows Tait and Martin-Lof's method:
  1. Define parallel reduction ⭢ₚ with ⭢ ⊆ ⭢ₚ ⊆ ↠
  2. Show ⭢ₚ has the diamond property
  3. Lift to the Church-Rosser theorem for ↠

  Read this file for WHAT is true.
  Read Defs/ for WHAT the words mean.
  Never need to open Code or Proofs.
-/

open Cslib Cslib.SKI

-- Inclusions between reduction relations
ProvenTheorem mRed_of_parallelReduction :
  ∀ {a a' : SKI}, a ⭢ₚ a' → a ↠ a'

ProvenTheorem parallelReduction_of_red :
  ∀ {a a' : SKI}, a ⭢ a' → a ⭢ₚ a'

-- Same reflexive-transitive closure
ProvenTheorem reflTransGen_parallelReduction_mRed :
  Relation.ReflTransGen ParallelReduction = Relation.ReflTransGen Red

-- The diamond property for parallel reduction
ProvenTheorem parallelReduction_diamond :
  Relation.Diamond ParallelReduction

-- Equivalence of MJoin for parallel reduction
ProvenTheorem join_parallelReduction_equivalence :
  Equivalence (Relation.MJoin ParallelReduction)

-- The Church-Rosser theorem (general form): MJoin Red is an equivalence
ProvenTheorem mJoin_red_equivalence :
  Equivalence (Relation.MJoin Red)

-- The Church-Rosser theorem (standard form): Red is confluent
ProvenTheorem MRed.diamond :
  Relation.Confluent Red
