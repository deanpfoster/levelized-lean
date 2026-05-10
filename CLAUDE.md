# C++ Standard Library Formalization in Lean 4

This project formalizes the C++ standard library (N4950) using Lean Manifests conventions.

## Project Structure

- `DeanLean/Basic.lean` — Macros: Signature, ProvenTheorem, TestedConjecture, Wrap, FastHeader
- `DeanLean/Cpp/X.lean` — Headers (the API). Read ONLY these to understand a module.
- `DeanLean/Cpp/Code/X.lean` — Definitions. Import these for types and functions.
- `DeanLean/Cpp/Proofs/X.lean` — Proofs. Never need to read these.
- `DeanLean/Cpp/Tests/X.lean` — Tests and `_test` witnesses for TestedConjectures.

autoImplicit is false. All type variables need explicit `variable` declarations.

## Available Modules — USE THESE, don't reinvent

### Ordering (import DeanLean.Cpp.Code.Ordering)

The canonical comparison typeclass. **Use this for any ordered type.**

```
class StrongOrd (T : Type) where
  strongCmp : T → T → Cpp.Ordering    -- returns .lt, .eq, or .gt
  cmp_refl : ∀ (a : T), strongCmp a a = .eq
  cmp_flip : ∀ (a b : T), (strongCmp a b).flip = strongCmp b a
  cmp_lt_trans : ∀ (a b c : T), strongCmp a b = .lt → strongCmp b c = .lt → strongCmp a c = .lt
  cmp_eq_trans : ∀ (a b c : T), strongCmp a b = .eq → strongCmp b c = .eq → strongCmp a c = .eq
```

Instances: `Nat`, `Int`, `Pair T1 T2` (lexicographic, if T1 and T2 have StrongOrd).

Proven derived properties you can use in proofs:
- `StrongOrd.cmp_gt_trans` — gt is transitive
- `StrongOrd.cmp_lt_iff_gt` — lt a b ↔ gt b a
- `StrongOrd.cmp_trichotomy` — exactly one of lt/eq/gt
- `StrongOrd.cmp_eq_symm` — eq is symmetric
- `StrongOrd.flip_lt_means_gt` / `flip_gt_means_lt` / `flip_eq_means_eq`
- `StrongOrd.cmp_lt_eq_trans` / `cmp_eq_lt_trans` — mixed transitivity
- `StrongOrd.cmp_gt_eq_trans` / `cmp_eq_gt_trans`

Ordering type conversions: `Ordering.flip`, `Ordering.toWeak`, `Ordering.toPartial`

### Pair (import DeanLean.Cpp.Code.Pair)

```
structure Pair (T1 T2 : Type) where
  first : T1
  second : T2
```

Functions: `Pair.make`, `Pair.swap`, `Pair.map_first`, `Pair.map_second`, `Pair.tuple_size`
Key theorem: `Pair.eq_iff_components` — p = q ↔ p.first = q.first ∧ p.second = q.second

### Optional (import DeanLean.Cpp.Code.Optional)

```
inductive Optional (T : Type) where
  | nullopt | some (val : T)
```

Monad instance. Functions: `has_value`, `value`, `value_or`, `emplace`, `reset`,
`and_then`, `transform`, `or_else`, `toOption`, `ofOption`

### Expected (import DeanLean.Cpp.Code.Expected)

```
inductive Expected (E T : Type) where
  | ok (val : T) | unexpected (err : E)
```

Note: type params are (E, T) not (T, E) — error first, like Lean's Except.
Monad instance (bind on T, short-circuit on E).
Functions: `has_value`, `value`, `error`, `value_or`, `and_then`, `transform`,
`transform_error`, `or_else`, `toExcept`, `ofExcept`

### Variant (import DeanLean.Cpp.Code.Variant)

`Variant2 T1 T2` and `Variant3 T1 T2 T3` — tagged unions.
Functions: `index`, `holds_alternative`, `visit`, `get_first`/`get_second`, `variant_size`

### Numeric (import DeanLean.Cpp.Code.Numeric)

`NumericLimits` typeclass with `min`, `max`, `digits`, `is_signed`, etc.
Instances: UInt8, UInt16, UInt32, UInt64, Int8, Int16, Int32, Int64.
Safe comparison: `cmp_equal`, `cmp_less`, `cmp_greater`, `in_range` (via `IntPromotable`).

### Concepts (import DeanLean.Cpp.Code.Concepts)

Typeclasses: `Integral`, `SignedIntegral`, `UnsignedIntegral`, `FloatingPoint`,
`EqualityComparable`, `TotallyOrdered`, `Semiregular`, `Regular`,
`Invocable`, `ConvertibleTo`, `DerivedFrom`, `AssignableFrom`

### Sort (import DeanLean.Cpp.Code.Sort)

```
def insertionSort : List Nat → List Nat
inductive IsSorted : List Nat → Prop
def IsPermutation (l₁ l₂ : List Nat) : Prop := l₁.Perm l₂
def isSorted : List Nat → Bool
```

Crown jewels — all fully proven:
- `insertionSort_sorted : ∀ l, IsSorted (insertionSort l)`
- `insertionSort_perm : ∀ l, IsPermutation l (insertionSort l)`
- `insertionSort_length : ∀ l, (insertionSort l).length = l.length`
- `isSorted_iff_IsSorted : ∀ l, isSorted l = true ↔ IsSorted l`

### Vector (import DeanLean.Cpp.Code.Vector)

`Vector T` wrapping `Array T`. Functions: `empty`, `push_back`, `pop_back`,
`get`, `front`, `back`, `size`, `isEmpty`, `clear`, `ofList`, `toList`

### Map/Set (import DeanLean.Cpp.Code.Map)

`Map K V` and `CppSet K` — sorted associative containers using `StrongOrd`.
Functions: `empty`, `insert`, `find`, `erase`, `contains`, `size`, `keys`, `values`
Key theorems: `find_insert_same`, `find_insert_other`, `erase_find`, `keys_sorted`

### Algorithm (import DeanLean.Cpp.Code.Algorithm)

Uses `StrongOrd` typeclass with `strongCmp` for three-way comparison.
Functions: `cppMin`, `cppMax`, `cppClamp`, `minElement`, `maxElement`, `isSorted`

## Macro Reference

## Evidence Hierarchy (where are the sorry's?)

Each level is strictly stronger than the one below. All are compiler-enforced.

```
○ UnprovenConjecture    — sorry is the whole theorem. Zero evidence.
◐ TestedConjecture      — sorry is the ∀. At least one concrete witness (foo_test).
◑ DecomposedConjecture  — sorry is in the lemmas. Real proof structure exists
                          (foo_derivation), and ALL lemmas are at least tested.
◕ DerivedConjecture     — sorry is in OTHER headers. Your derivation is real;
                          it only depends on theorems promised by other modules.
● ProvenTheorem         — no sorry anywhere. Unconditional proof (foo_proof).
```

Promotion path: each level's requirement is a strict superset of the level below.
DecomposedConjecture FAILS if any lemma lacks a _test witness.
DerivedConjecture auto-reports which other headers' theorems it depends on.
ProvenTheorem accepts both foo_proof and foo_derivation (no rename needed).

## Macro Reference

Evidence macros:
- `UnprovenConjecture foo : T` — bare sorry
- `TestedConjecture foo : T` — requires `foo_test` in scope
- `DecomposedConjecture foo : T` — requires `foo_derivation` + all sorry deps tested
- `DerivedConjecture foo : T` — requires `foo_derivation`, auto-reports sorry deps
- `ProvenTheorem foo : T` — requires `foo_proof` or `foo_derivation` (no sorry)

Other macros:
- `Signature Cpp.Foo.bar : T` — compiler-checks function exists with that type
- `Wrap foo_proof := @Some.External.name` — alias for naming convention bridge
- `FastHeader foo : T` — axiom, for breaking recompilation cascades
- `VerifyAxiom foo : T` — CI-only: confirms fast-mode axiom matches real proof
- `ExternalTheorem foo := @Lib.name : T` — wraps existing library theorem
- `Vocabulary foo := @Lib.name` — define-or-verify for Defs files

Fast mode: `set_option levelized.fast true` makes ProvenTheorem emit axioms.
