/-!
# Best-practice traditional Lean using modules/sections/opaque

This shows how an experienced Lean user would structure Ordering
using ONLY built-in language features — no custom macros. This is
the strongest version of Leo's "modules do everything" argument.

Key techniques:
  - `section`/`variable` to scope assumptions
  - `export` to re-export selected names
  - `opaque` to hide implementation
  - `protected` to require qualified access
  - Separate files for interface vs implementation
  - Careful use of `@[simp]` to mark the API theorems
-/

-- ═══════════════════════════════════════════════════════════════
-- File 1: Ordering/Defs.lean — the "interface" file
-- ═══════════════════════════════════════════════════════════════

namespace ModularOrdering.Defs

inductive Ordering where
  | lt | eq | gt
deriving Repr, BEq, DecidableEq

def Ordering.flip : Ordering → Ordering
  | .lt => .gt | .eq => .eq | .gt => .lt

class StrongOrd (T : Type) where
  strongCmp : T → T → Ordering
  cmp_refl : ∀ (a : T), strongCmp a a = .eq
  cmp_flip : ∀ (a b : T), (strongCmp a b).flip = strongCmp b a
  cmp_lt_trans : ∀ (a b c : T),
    strongCmp a b = .lt → strongCmp b c = .lt → strongCmp a c = .lt
  cmp_eq_trans : ∀ (a b c : T),
    strongCmp a b = .eq → strongCmp b c = .eq → strongCmp a c = .eq

-- This is clean. The reader sees the typeclass and its laws.
-- So far, modules work fine.

end ModularOrdering.Defs

-- ═══════════════════════════════════════════════════════════════
-- File 2: Ordering/Theorems.lean — derived properties
-- ═══════════════════════════════════════════════════════════════

namespace ModularOrdering.Theorems

open ModularOrdering.Defs

variable {T : Type} [StrongOrd T]

-- These are the "interesting" theorems consumers want.
-- In module style, they're just theorems in a namespace.

theorem cmp_gt_trans (a b c : T)
    (hab : StrongOrd.strongCmp a b = .gt)
    (hbc : StrongOrd.strongCmp b c = .gt) :
    StrongOrd.strongCmp a c = .gt := by
  sorry -- actual proof omitted for comparison purposes

theorem cmp_trichotomy (a b : T) :
    StrongOrd.strongCmp a b = .lt ∨
    StrongOrd.strongCmp a b = .eq ∨
    StrongOrd.strongCmp a b = .gt := by
  cases h : StrongOrd.strongCmp a b <;> simp

theorem cmp_lt_iff_gt (a b : T) :
    StrongOrd.strongCmp a b = .lt ↔ StrongOrd.strongCmp b a = .gt := by
  sorry

end ModularOrdering.Theorems

-- ═══════════════════════════════════════════════════════════════
-- File 3: Ordering/Instances.lean — Nat, Int instances
-- ═══════════════════════════════════════════════════════════════

-- (all the private proofs for natCmp go here — same as before)

-- ═══════════════════════════════════════════════════════════════
-- File 4: Ordering.lean — re-export file
-- ═══════════════════════════════════════════════════════════════

namespace ModularOrdering.ReExport

-- The best you can do: a file that imports and re-exports.
-- This is the closest thing to a "header."

-- import Ordering.Defs
-- import Ordering.Theorems
-- import Ordering.Instances

-- export ModularOrdering.Defs (Ordering StrongOrd)
-- export ModularOrdering.Theorems (cmp_gt_trans cmp_trichotomy cmp_lt_iff_gt)

-- This works! A consumer imports Ordering.lean and gets a clean namespace.
-- So what's STILL missing compared to Lean Manifests?

end ModularOrdering.ReExport

-- ═══════════════════════════════════════════════════════════════
-- WHAT MODULES GET YOU (Leo is right about these):
-- ═══════════════════════════════════════════════════════════════
--
-- ✓ Separate files for defs, theorems, instances
-- ✓ Re-export file as an "interface"
-- ✓ Consumers only import the re-export file
-- ✓ `private` hides internal lemmas
-- ✓ `protected` requires qualified names
-- ✓ Namespaces organize the API
--
-- ═══════════════════════════════════════════════════════════════
-- WHAT MODULES STILL CAN'T DO:
-- ═══════════════════════════════════════════════════════════════
--
-- 1. EVIDENCE LEVELS
--    In the re-export file, these look identical:
--
--      theorem cmp_gt_trans : ...   -- fully proven
--      theorem cmp_trichotomy : ... -- fully proven
--      theorem cmp_lt_iff_gt : ...  -- actually sorry!
--
--    There is NO WAY for a reader to see which theorems are proven
--    and which are sorry without opening the theorem file.
--    In Lean Manifests:
--
--      ProvenTheorem cmp_gt_trans : ...        -- proven
--      ProvenTheorem cmp_trichotomy : ...      -- proven
--      TestedConjecture cmp_lt_iff_gt : ...    -- tested only!
--
--    The evidence level is IN THE NAME of the macro.
--
-- 2. COMPILER-ENFORCED WITNESSES
--    `ProvenTheorem foo` FAILS TO COMPILE if `foo_proof` doesn't exist.
--    `TestedConjecture foo` FAILS TO COMPILE if `foo_test` doesn't exist.
--    Modules have no equivalent. You can forget to write the proof
--    and the sorry propagates silently through re-exports.
--
-- 3. PROGRESS TRACKING
--    Module style:
--      $ grep "sorry" Ordering/Theorems.lean
--      -- returns sorry count, but no granularity
--
--    Lean Manifests:
--      $ grep "ProvenTheorem" Ordering.lean | wc -l     → 20 proven
--      $ grep "TestedConjecture" Ordering.lean | wc -l  → 4 tested
--      $ grep "UnprovenConjecture" Ordering.lean | wc -l → 0 unproven
--
-- 4. RECOMPILATION ISOLATION
--    Even with separate files, changing Theorems.lean rebuilds the
--    re-export file and all consumers. FastHeader (axiom) breaks this
--    cascade — modules alone cannot.
--
-- 5. CONVENTION ENFORCEMENT
--    Nothing in the module system prevents someone from putting a proof
--    in the Defs file, or a definition in the Theorems file, or skipping
--    the re-export entirely. Lean Manifests macros ENFORCE the convention:
--    - `Signature` checks the function exists and is total
--    - `ProvenTheorem` checks the proof exists
--    - `TestedConjecture` checks the test witness exists
--    The convention is not just documented — it's compiled.
--
-- ═══════════════════════════════════════════════════════════════
-- VERDICT
-- ═══════════════════════════════════════════════════════════════
--
-- Leo is right that modules give you 80% of the structural benefit.
-- The Defs/Theorems/Instances split is good practice and modules
-- support it fine.
--
-- The 20% that's missing is the METADATA layer: evidence levels,
-- witness enforcement, and progress tracking. These are lightweight
-- (40 lines of macros) but they turn a convention into a contract.
--
-- The analogy: interfaces in Java vs duck typing in Python.
-- Both let you separate API from implementation. But interfaces
-- are compiler-checked — you can't claim to implement Comparable
-- without actually providing compareTo(). Lean Manifests macros
-- are that compiler check for theorem-proving conventions.
-- ═══════════════════════════════════════════════════════════════
