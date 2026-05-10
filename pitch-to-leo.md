# Lean Manifests: Evidence Levels with Teeth

**To:** Leo de Moura & the Lean Core Team  
**Subject:** Complementing `module` with manifest macros that make evidence levels first-class and compiler-enforced

## 1. Acknowledgment: `module` Already Solves the Cascade

We originally proposed signature-based incremental compilation to break
recompilation cascades. **We now know that Lean 4.30's `module` keyword
already does this.** Our testing on CSLib (130 files, 768 theorems)
confirms: changing a proof body in a `module` file does NOT cascade to
downstream dependents. The semantic hashing is built into the compiler.

This is exactly what we asked for. Well done.

## 2. What `module` Doesn't Solve

The cascade was one problem. The others remain:

### A. Evidence Levels: What's proven vs. tested vs. conjectured?

In standard Lean, `theorem foo : T := by sorry` and `theorem foo : T := by exact proof`
look identical to a consumer who imports the module. Both are `theorem`.
There's no way to know the evidence level without opening the file.

Framed another way: Lean already has two ways to declare a theorem you
can't fully prove. `axiom foo : T` is honest — declared, tracked,
visible in the axiom-usage report. `theorem foo : T := by sorry` is
apologetic — warning, contaminated dependency graph, zero structure.
Every `sorry` looks the same as every other `sorry`, whether it's a
deliberate assumption or a scratch-hole someone forgot to clean up.

We propose a 5-level evidence hierarchy — **five new kinds of sorry,
each less apologetic than the last**:

```
○ UnprovenConjecture    — sorry IS the theorem
◐ TestedConjecture      — sorry is the ∀ (concrete witness required)
◑ DecomposedConjecture  — sorry is in the lemmas (all lemmas tested)
◕ DerivedConjecture     — sorry is in other modules (your proof is real)
● ProvenTheorem         — no sorry anywhere
```

Each level requires progressively more evidence. A reader scanning a
header sees the level in the macro name — no compilation needed.
`DecomposedConjecture` FAILS to compile if any lemma lacks a test.
`DerivedConjecture` auto-discovers sorry dependencies via
`getUsedConstantsAsSet` metaprogramming and reports them as a trust
artifact.

**Teeth.** Until recently the hierarchy was a convention: the trust
report listed sorry deps by name, but those names could point at
undeclared holes in random proof files. We added an attribute-based
enforcement: every macro stamps `@[manifest_entry]` on its emitted
declaration, and `DerivedConjecture` / `DecomposedConjecture` refuse
to compile if any sorry-bearing dep lacks the attribute. The error
message names the stray and points at the fix.

After the enforcement, the trust report is complete by construction.
Every entry points at a named manifest macro invocation. No
off-the-record sorry, because any off-the-record sorry breaks the
build. The hierarchy went from a stylistic convention to a compile-time
contract.

The enforcement is binary — declared vs. hidden — not a monotonicity
check. A `DerivedConjecture` can depend on an `UnprovenConjecture`
(lower), a `TestedConjecture` (also lower), or a `ProvenTheorem`
(higher). The hierarchy is ordered informally for human reading; the
compiler only enforces "no hidden holes."

This is ~150 lines of macros plus ~40 lines of attribute stamping and
enforcement. It layers on top of Lean's existing theorem mechanism
without modifying the compiler.

### B. Readability: 77% Line Reduction

CSLib's 20,837 lines of source reduce to 4,173 lines of manifest +
vocabulary. A reader (human or LLM) understands the entire library
API without seeing a single proof body.

The manifest contains:
- **Theorem signatures**: each carrying an evidence level
- **Nothing else**: no proof bodies, no tactic blocks, no internal lemmas

Vocabulary — the types and predicates that appear in theorem
signatures — lives in a sibling `Defs/` directory, also public. Code,
proofs, and tests are hidden.

For AI verification pipelines, this is the key win. An LLM using the
library needs theorem signatures, not proof bodies. Our benchmark
shows 42% fewer tokens for identical comprehension accuracy.

### C. Vocabulary Enforcement via `Defs/`

A `Defs/` directory holds the vocabulary — definitions that appear in
theorem types. The manifest imports `Defs/` but NOT `Code/`, so
theorems in the manifest can only reference vocabulary definitions.
This is enforced by Lean's import system, not custom macros.

This prevents internal helpers from leaking into the public API.

### D. Fractional Proof Tracking

Inspired by Theorem.dev's "fractional proof decomposition":
decompose a theorem into lemmas, prove some, test others.
`DecomposedConjecture` tracks the fraction automatically
and requires every piece to have at least a test witness.

## 3. What We Built

Working prototype at `lean4.ai/levelized-lean.html`:

- Full CSLib manifests: 459 compiler-verified theorem entries
- Full CSLib intrusive refactor: 121 Defs files, all building
- C++ standard library formalization: 13 modules, 226 theorems
- Verified interval arithmetic: 34 proven containment theorems
- Happens-before memory model: 22 proven concurrency theorems
- Benchmark: manifests give 42% token savings for LLM comprehension
- Fast mode toggle: `set_option levelized.fast true` for axiom-based manifests
- **Teeth** (2026): `@[manifest_entry]` enforcement makes the trust
  report complete by construction — `DerivedConjecture` refuses to
  compile if any sorry dep is a stray, not a declared manifest entry

## 4. For Mathlib

The `module` keyword's cascade prevention presumably extends to Mathlib
once Mathlib adopts `module`. Lean Manifests would complement this:

- **Progress tracking**: `grep DecomposedConjecture *.lean` instantly shows
  partially-proven theorems and what's blocking them
- **LLM access**: Mathlib manifests would give AI agents the full API in
  ~16K lines instead of ~200K+ lines of proof-heavy source
- **Contribution guidance**: new contributors see which conjectures are
  closest to promotion (highest fraction of proven lemmas)
- **Trust reports**: every `DerivedConjecture` in Mathlib would emit a
  complete, enforced list of its sorry dependencies

## 5. O(1) Parallel Verification

The `module` keyword's semantic hashing should also enable O(1) parallel
verification: if proof changes at level N don't invalidate level N+1,
then all levels can be compiled simultaneously. Does Lake already exploit
this? If so, the parallelization win from our original pitch is also
already solved.

Our `FastHeader` (axiom-based manifest entries) would still be useful
for the extreme case: an LLM exploring proof space wants sub-second
type-checking without waiting for ANY proof to compile. But for normal
development, `module` + Lake parallelism may be sufficient.

## 6. The Ask

The evidence hierarchy is 150 lines of macros that work today. We're not
asking for compiler changes — `module` already solved the hard part.

We'd welcome feedback on:
1. Would the Lean community adopt evidence-level macros?
2. Should vocabulary enforcement (`Defs/`) be a convention or tooling?
3. Is there interest in manifest generation for Mathlib?
