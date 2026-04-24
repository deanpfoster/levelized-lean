# Formalizing the C++ Standard Library in Lean 4

A case study in applying Levelized Lean to a large-scale formalization project.

## Goal

Convert the C++ standard library specification (N4950, ~1,000 pages of
library content) into machine-checked Lean 4 theorems. The theorems
replace English prose with compiler-verified claims. The proofs and code
are second-class — what matters is the header: what's true, and how
confident we are.

## What We Found

### The spec is mostly about value categories, not behavior

The C++ spec for `std::pair` is 5 pages. Our formalization covers it in
34 lines of header. The gap isn't laziness — roughly 80% of those 5
pages describe constructor overloads (12+), SFINAE constraints, reference
qualification (lvalue/rvalue/const variants of every method), and
exception safety tables. None of these have analogues in a pure
functional language.

The 20% that does translate — structural properties, comparison
semantics, accessor correctness — translates cleanly and can be proven
with real inductive proofs.

### Trivial theorems vs. interesting theorems

Our first 93 theorems were almost all trivially true by `rfl` (unfold the
definition, done). Things like "if you construct a pair and take `.first`,
you get back what you put in." These are the equivalent of unit tests that
happen to be proven.

The interesting theorems came later:

- **Sort correctness**: `insertionSort` produces a sorted permutation of
  its input. Real inductive proofs, not `rfl`.
- **Map invariants**: `find (insert k v m) k = some v` and
  `(erase k m).find k = none`. Requires reasoning about sorted list
  insertion.
- **Ordering laws**: `StrongOrd` typeclass with reflexivity, flip,
  lt-transitivity, eq-transitivity — and the discovery that
  eq-transitivity is an independent axiom.
- **Algorithm properties**: `min` commutativity, `clamp` stays in range,
  `minElement` is actually minimal.

### eq-transitivity is an independent axiom

The Ordering module discovered something the C++ spec states but doesn't
emphasize: for `strong_ordering`, the property that "equal elements are
substitutable" (eq-transitivity: `cmp a b = eq → cmp b c = eq → cmp a c = eq`)
cannot be derived from reflexivity + flip + lt-transitivity alone. A
3-element counterexample exists. The C++ spec (§17.11.2.1 para 4) says
strong_ordering "implies substitutability" — but doesn't spell out that
this is an independent axiom you must separately verify.

This is exactly the kind of insight you get from formalization that you
don't get from reading prose.

### Cross-module dependencies validate the architecture

The Map module imports `StrongOrd` from the Ordering module and uses its
proven comparison laws (transitivity, reflexivity, flip) to prove that
the sorted-key invariant is maintained across insert and erase operations.
This is the dependency chain working as intended: proven properties in one
module become available lemmas in another, without anyone opening a proof
file.

### Parallel development works without worktrees

Because each module writes to its own set of files (Code/X.lean,
Proofs/X.lean, Tests/X.lean, X.lean), multiple agents can work on
different modules simultaneously in the same repository with no
conflicts. The only shared file is the root import file (DeanLean.lean),
and edits to it are additive (each agent appends one import line).

We ran 3 agents in parallel across 3 rounds (9 total) with zero merge
conflicts. This is a direct consequence of the levelized file structure.

### The evidence hierarchy: where are the sorry's?

Every theorem claim has a sorry somewhere — the question is where.
The hierarchy tracks this precisely, each level strictly stronger:

```
○ UnprovenConjecture    — sorry IS the theorem. Zero evidence.
◐ TestedConjecture      — sorry is the ∀. One concrete witness exists.
◑ DecomposedConjecture  — sorry is in the LEMMAS. Real proof structure
                          (derivation), all lemmas at least tested.
◕ DerivedConjecture     — sorry is in OTHER HEADERS. Your proof is real;
                          it only depends on promises from other modules.
● ProvenTheorem         — no sorry ANYWHERE. Done.
```

Each level is compiler-enforced:
- `TestedConjecture foo` fails without `foo_test`
- `DecomposedConjecture foo` fails if any lemma in `foo_derivation` lacks a `_test`
- `DerivedConjecture foo` auto-reports which external theorems still have sorry
- `ProvenTheorem foo` fails if `foo_proof` or `foo_derivation` has any sorry

Inspired by Theorem.dev's "fractional proof decomposition":
decompose a theorem into pieces, prove some, test others, track the fraction.
`DecomposedConjecture` is the Lean formalization of this idea.

## Current State

11 modules, 46 files, ~6,200 lines of Lean, 226 theorem statements:
- 174 `ProvenTheorem` (fully proven, zero sorry)
- 52 `TestedConjecture` (at least one witness, universal claim is sorry)

| Module | C++ Section | Proven | Tested | Highlight |
|--------|------------|--------|--------|-----------|
| Pair | §22.3 | 9 | 0 | swap involution, eq iff components |
| Optional | §22.5 | 17 | 6 | monad laws, roundtrip to Option |
| Concepts | §18 | 12 | 0 | typeclass hierarchy |
| Numeric | §17.4 | 27 | 9 | safe cross-signedness comparison |
| Variant | §22.6 | 28 | 6 | exactly-one-alternative, visit composition |
| Ordering | §17.11 | 30 | 11 | eq-trans independence, lexicographic Pair |
| Algorithm | §27.7-9 | 20 | 3 | min/max comm, clamp-in-range |
| Expected | §22.8 | 18 | 6 | Result/Either with monad laws |
| Sort | §27 | 4 | 0 | **insertionSort sorted + permutation** |
| Vector | §24.3 | 7 | 0 | push_back/pop_back roundtrip |
| Map/Set | §24.4 | 10 | 0 | **find_insert_same, uses StrongOrd** |

## What's hard, what's easy

**Easy to formalize** (translates directly):
- Algebraic data types: pair, optional, variant, expected
- Type traits / concepts → typeclasses
- Numeric constants → typeclass instances
- Pure algorithms on lists → standard Lean

**Medium** (requires real proof work):
- Ordering laws and their derived properties
- Algorithm correctness (min comm, clamp range, sort)
- Container invariants (sorted keys in map, size tracking in vector)

**Hard / not yet attempted**:
- Iterator invalidation rules (need a memory model)
- Concurrency (need a happens-before model)
- Exception safety guarantees (irrelevant in pure Lean)
- Template metaprogramming (no direct analogue)

## Module maturity stages

A module can start simple and grow into full enforcement. The macros
(`ProvenTheorem`, `TestedConjecture`) work at every stage — they give
you evidence tracking from day one. The file split is about visibility
and enforcement, not about the macros.

### Stage 1: Prototype (one file)

```
Sort.lean    ← definitions, proofs, tests, theorems — all in one file
```

Everything lives together. `ProvenTheorem` still checks that `_proof`
exists; `TestedConjecture` still requires `_test`. The evidence
hierarchy is enforced even in a single file. Good for exploration
and rapid iteration. Start here.

### Stage 2: Separated (conventional levelized lean)

```
Sort.lean           ← header: Signature + ProvenTheorem + TestedConjecture
Code/Sort.lean      ← definitions + implementation
Proofs/Sort.lean    ← proofs (named foo_proof)
Tests/Sort.lean     ← tests (named foo_test)
```

Header imports Code, Proofs, and Tests. Consumers read only the header.
Proofs can change without affecting the header's meaning. But the header
can see everything in Code — no enforcement that theorems only reference
"vocabulary" types. A sneaky definition in Code could leak into a theorem.

### Stage 2.5: Organized (definitions first, proofs second)

Within each file, move all definitions (structure, inductive, class, def,
abbrev) to the top, and all proofs (theorem, lemma) to the bottom.
Same file, same imports, same behavior — just reordered.

This is the safe checkpoint for an intrusive migration: pure reorder,
easy diff to review. It also reveals which definitions are vocabulary
(they're the ones at the top) and which are internal helpers.

For a PR to an existing codebase, Stage 2.5 is PR #1 (reorganize),
and Stage 3 is PR #2 (split). Each is independently reviewable.

### Stage 3: Enforced (full vocabulary control)

```
Sort.lean                  ← header: imports Defs + ProofExports only
Defs/Sort.lean             ← vocabulary: types and functions used in theorems
Code/Sort.lean             ← imports Defs, adds implementation helpers
Proofs/Sort.lean           ← proofs
Proofs/SortExports.lean    ← auto-generated: re-exports only _proof names
Tests/Sort.lean            ← tests
Tests/SortExports.lean     ← auto-generated: re-exports only _test names
```

The header imports `Defs/` (not `Code/`) and `Proofs/SortExports` (not
`Proofs/Sort`). This means:
- Theorems can only reference names from Defs — compiler-enforced
- Proof files can't smuggle definitions into the header
- The exports files are auto-generated from the header by `generate_exports.sh`
- `Code/` is invisible to the header entirely

The enforcement is structural (Lean's import system), not a custom macro.

### When to promote

- **1 → 2**: When the file gets long, or when you want proof changes to
  stop triggering recompilation of consumers.
- **2 → 2.5**: When preparing for a PR or wanting better readability.
  Pure reorder — safe, reviewable, no behavioral change.
- **2.5 → 3**: Cut the top section (definitions) into Defs/, add one import.
  Mechanical after 2.5 — the hard thinking was already done.
  Run `generate_exports.sh` after adding theorems to the header.

## What goes in a header

A header has three sections:

### 1. Vocabulary (the domain language)

Short definitions and comments explaining the concepts used in theorem
types. A reader who understands the vocabulary can read every theorem
without opening any other file.

Example from a sorting header:
```
⟪tm⟫       — extract the return value from a TimeM computation
tm.time    — extract the cost (comparison count)
IsSorted l — List.Pairwise (· ≤ ·) l
l₁ ~ l₂   — l₁ is a permutation of l₂
```

This vocabulary is the **shared language** of the domain. Once defined,
it works across every sorting algorithm — mergeSort, quickSort, heapSort
all use the same four concepts. The more modules you add, the cheaper
each header becomes: the vocabulary is paid once.

### 2. Public theorems (the contract)

Only the theorems a consumer would use. Internal lemmas (stepping stones
to the public results) stay in Proofs/. The header contains the *what*,
not the *how*.

A 207-line mergeSort module with 14 theorems reduces to 7 public theorems
in the header. The other 7 are helpers (`min_all_merge`, `merge_perm`,
`timeMergeSortRec_le`) that a consumer never invokes directly.

### 3. Signatures (when needed)

`Signature` is useful when theorems don't fully cover a function — it
tells the reader "this exists and has this type" even when behavior isn't
fully specified. Once theorems cover every case, the Signature is
redundant.

### What NOT to put in a header

- Proof bodies (they go in Proofs/)
- Implementation helpers (they go in Code/)
- Internal lemmas used only by other proofs
- Test code (it goes in Tests/)

### Sizing rule of thumb

A good header is roughly **2 lines per public theorem** (the signature
+ a one-line comment) plus **1-2 lines per vocabulary concept**. A module
with 7 theorems and 5 vocabulary concepts → ~20 lines. The original
source might be 200+ lines.

## Vocabulary as shared infrastructure

The Defs/ directory isn't just "definitions used by theorems" — it's
the **shared vocabulary** that makes headers across modules mutually
intelligible.

Examples from this project:
- `StrongOrd` (Ordering) → used by Algorithm, Map, Set
- `IsSorted`, `IsPermutation` (Sort) → would be shared by any sorting module
- `mem`, `subset` (Interval) → used by Core, Arith, Lattice
- `HappensBefore` (Concurrency) → used by every concurrency pattern

The progression: English comments → Lean definitions → shared Defs/
vocabulary → reusable domain language. Each step makes future headers
cheaper and more precise. Investing in good vocabulary definitions is
the highest-leverage work in a formalization project.

## Lessons for other formalization projects

1. **Start with the easy modules** to establish patterns. Pair and Optional
   are trivial but they defined the file layout, macro usage, and naming
   conventions everything else follows.

2. **Promote test properties to the header**. Interesting claims were
   hiding in test files where nobody could see them. Making them
   `TestedConjecture` in the header surfaces them as proof targets.

3. **The header IS the spec**. If a reader (human or LLM) can't understand
   what a module provides by reading only the header, the header is
   incomplete. Proofs and code are implementation details.

4. **Separate public from internal theorems**. Not every theorem belongs
   in the header. Internal lemmas (stepping stones to the public results)
   stay in Proofs/. A 14-theorem module might have only 7 public theorems.

5. **Parallel agents work when the architecture is right**. Levelized file
   structure enables embarrassingly parallel development. Each module is
   independent until you choose to wire up cross-module dependencies.

6. **Formalization finds real issues**. The eq-transitivity discovery
   wasn't something we were looking for — it fell out of trying to prove
   the Ordering laws. English specs hide these gaps.

7. **Vocabulary is the highest-leverage investment**. Defining `IsSorted`,
   `HappensBefore`, `StrongOrd` well means every future header is
   cheaper. The domain language amortizes across the entire library.
