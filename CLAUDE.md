# C++ Standard Library Formalization in Lean 4

This project formalizes the C++ standard library (N4950) using Lean Manifests conventions.

> **Starting a new project that depends on lean-manifests?** This file
> is the workflow for working ON lean-manifests itself. For downstream
> projects, copy `templates/CLAUDE.md` (or `templates/AGENTS.md`) to
> your project root. See `templates/README.md` for details.

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
- `Restate foo` — forward a manifest claim into current namespace, auto-detects evidence level
- `RestateTheorem foo` — forward specifically as ProvenTheorem
- `PureExcept Ns.fn` — static call-graph analysis proving IO surface is complete
- `AxiomsAllowed Ns.fn` — verify axiom surface (no unexpected axioms in reachable constants)
- `ManifestAxiom foo : T` — permanent environmental assumption (never provable)
- `FullyAttested foo` — compile-time check that all sorry deps are ManifestAxioms
- `Test foo` — inline test macro, tries elaboration, records pass/fail
- `FailingConjecture foo : T` — like TestedConjecture but expects some tests to fail

Fast mode: `set_option levelized.fast true` makes ProvenTheorem emit axioms.

## Downstream Dependents

- **l3m** (~/l3m.kiro) — verified coding agent. Depends on this repo via `require dean_lean from git`.

## Writing good manifests

Read **`templates/MANIFEST_GUIDE.md`** before writing or reviewing any
manifest. Key principles:

- 4–6 headline claims written for the consumer, not proof obligations
- Explicit "What we do NOT claim" section
- `registerTestResults` on every conjecture with test coverage
- No vacuous totality (`∀ x, ∃ y, f x = y` is a tautology)
- No trivially decidable claims left as UnprovenConjecture
- Strip workplan metadata on promotion

## The Workflow Gap and @[theorems]

### The problem

Manifests catch violations at build time. They don't help during the *writing* phase. When you're modifying a function, you grep for code — you don't grep for manifest entries. The theorems are organized by concept (all path theorems together), not by function (all theorems about `confineIO` together). So consulting them requires knowing where to look.

Concrete example: migrating 24 tool functions to caps in l3m. The manifests weren't consulted first. The code was written, `lake build` caught every bypass. Manifests worked as tripwires, not as design specs.

### The @[theorems] attribute

`DeanLean/Attr.lean` provides a parametric attribute:

```lean
@[theorems confine_within_root, confine_rejects_dotdot, confineIO_rejects_symlink_escape]
def confineIO (root path : System.FilePath) : IO (Option WorkspacePath) := ...
```

Query at elaboration time:
```lean
import DeanLean.Attr
-- getTheorems? env `confineIO returns some #[`confine_within_root, ...]
```

### The function-keyed index

A metaprogram (`Scripts/GenerateTheoremIndex.lean` in l3m) walks all tagged constants and produces a markdown index with two sections:
- **Function → Theorems**: given a function, what theorems constrain it?
- **Theorem → Functions**: given a theorem, what functions does it apply to?

### How to use when modifying code

1. Before modifying a function, check if it's tagged: `grep "@\[theorems" L3m/path/to/file.lean`
2. Or look it up in the generated index (`docs/theorem-index.md`)
3. Read the listed theorems to understand what invariants must be preserved
4. Make the change, run `lake build` — the kernel still catches violations either way

### Honest assessment

The attribute enables consultation. It doesn't enforce it. Whether developers actually check before modifying is a workflow/habit question. The build catches you regardless. The attribute just makes it cheaper to check first.

## DeanLean.IndexGen — Reusable Theorem Index Generator

A generic utility for any project using lean-manifests to generate a function↔theorem cross-reference.

### How to invoke from any project

```lean
-- Scripts/GenerateTheoremIndex.lean
import DeanLean.IndexGen
import MyProject  -- your root import

def main : IO Unit := do
  DeanLean.IndexGen.run "MyProject" "docs/theorem-index.md" #[{ module := `MyProject }]
```

Run: `lake env lean --run Scripts/GenerateTheoremIndex.lean`

### What it does

Two-tier discovery:
1. **@[theorems]** annotations — explicit links from functions to their theorems
2. **Auto-detection** — walks every ProvenTheorem/DerivedConjecture/TestedConjecture/ManifestAxiom statement, finds which project functions are mentioned

The output flags each link by source: annotated, auto-detected, or both.

### Single-function lookup

```lean
import DeanLean.IndexGen
import MyProject

def main (args : List String) : IO Unit := do
  let env ← Lean.importModules #[{ module := `MyProject }] {} 0
  let result := DeanLean.IndexGen.lookupFunction env "MyProject" args.head!.toName
  IO.print result
```

### Recommended workflow for projects

1. Add a `Scripts/GenerateTheoremIndex.lean` that calls `DeanLean.IndexGen.run`
2. Run it as part of your verification script (or CI)
3. Use `@[theorems]` for load-bearing explicit links
4. Let auto-detection cover the rest — sparse annotations are better than dense


## DeanLean.Workplan — Reusable Workplan for Parallel Agents

A generic workplan generator that surfaces UnprovenConjecture work-in-progress as structured tasks. Useful when multiple LLM agents work on the same project in parallel — each picks an entry point, claims it, works.

### Three optional attributes on UnprovenConjectures

```lean
@[depends_on  foo, bar]              -- what must be done first
@[estimated_minutes 60]              -- rough effort estimate
@[entry_point]                       -- flag: independently approachable
UnprovenConjecture my_claim : ...
```

These attributes are stripped on promotion to ProvenTheorem or TestedConjecture (work is done; the metadata becomes noise).

### How to invoke from any project

```lean
-- Scripts/Workplan.lean
import DeanLean.Workplan
import MyProject

def main : IO Unit := DeanLean.Workplan.run "MyProject"
```

Run: `lake env lean --run Scripts/Workplan.lean`

### What it does

Walks every `@[manifest_entry]`-tagged constant in `MyProject.*` that:
1. Still uses `sorry` transitively (work in progress)
2. Is NOT marked `@[manifest_axiom]` (permanent assumption, not work)

Prints three sections:

```
WORKPLAN (12 manifest entries)

== Entry points (no deps, ready to start) — 3 ==
  parse_atx_headings  est=30m
  parse_paragraphs    est=45m
  parse_thematic_breaks est=30m

== Blocked by other entries — 6 ==
  parse_lists  est=120m  blocked-by: parse_paragraphs
  parse_emphasis  est=80m  blocked-by: parse_atx_headings, parse_paragraphs
  ...

== Other (no deps, no entry-point flag) — 3 ==
  parse_html_blocks  est=?
  ...
```

### Recommended workflow for parallel LLM work

1. Pre-load the manifest with `UnprovenConjecture` entries decorated with `@[entry_point]` and `@[estimated_minutes N]` for the work you want done.
2. Add `Scripts/Workplan.lean` that calls `DeanLean.Workplan.run`.
3. When you dispatch parallel agents, have each agent's prompt start with: "Run `lake env lean --run Scripts/Workplan.lean`. Pick an entry point matching your time budget. Claim it via a one-line commit. Work."
4. Once an entry promotes (becomes `ProvenTheorem` or `TestedConjecture`), strip its workplan metadata.
5. Re-run workplan to see what remains.

This is a workflow tool, not a safety tool — the kernel still verifies anything that tries to claim ProvenTheorem status. The workplan just makes parallel coordination cheaper than memo-by-memo.

### Single-project lookup

`DeanLean.Workplan.collect env "MyProject"` returns the list of `Entry` records if you want to programmatically inspect the workplan instead of printing.
