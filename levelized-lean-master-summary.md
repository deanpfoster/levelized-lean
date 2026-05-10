# Lean Manifests: Architectural Master Summary

## 1. The Core Idea: Separate the Contract from the Evidence

A Lean library communicates two different things: the **claims** it
makes (types of functions, statements of theorems, and the evidence
backing each one), and the **evidence itself** (definitions,
implementations, proof bodies, test witnesses). These belong on
opposite sides of an interface.

**Lean Manifests** formalize that separation through a three-way
split:

| Category | Contents | Visibility |
| --- | --- | --- |
| **Manifests** | Claims — theorem statements with explicit evidence level | Public; read to use the module |
| **Vocabulary (`Defs/`)** | Types and predicates that appear in the claims | Public; read to understand the claims |
| **Everything else** (`Code/`, `Proofs/`, `Tests/`) | How each claim is established | Hidden; don't read unless you're working on it |

A reader — human or LLM — can understand what a module offers and how
confident they should be in each claim by reading the manifest plus
vocabulary. No proof bodies needed.

## 2. The Evidence Hierarchy

Lean already has two ways to declare a theorem you can't fully prove:
`axiom` (declared, honest) and `theorem ... := by sorry` (apologetic,
unstructured). Every `sorry` looks identical to every other — a
deliberate assumption is indistinguishable from a forgotten
scratch-hole.

Lean Manifests introduce **five kinds of sorry, each less apologetic
than the last**, each visible at a glance through its macro name:

```
○ UnprovenConjecture    — sorry IS the theorem. Zero evidence.
◐ TestedConjecture      — sorry is the ∀ (at least one concrete witness).
◑ DecomposedConjecture  — sorry is in the LEMMAS (all lemmas tested).
◕ DerivedConjecture     — sorry is in OTHER manifests (derivation is real).
● ProvenTheorem         — no sorry anywhere.
```

Each level's obligations are compiler-enforced at elaboration time.
`TestedConjecture foo` requires `foo_test` to exist;
`DecomposedConjecture foo` hard-fails if any lemma lacks its own
`_test`; `DerivedConjecture foo` walks the dependency graph via
`getUsedConstantsAsSet` and reports exactly which sorry deps its
derivation assumes.

## 3. Teeth: the Trust Report Is Complete by Construction

Until recently the evidence hierarchy was a convention. The info
message from `DerivedConjecture` listed sorry dependencies by name —
but those names could point at undeclared stray sorries sitting in
random proof files. A reader auditing "what does this module assume?"
couldn't distinguish a named, intentional assumption from a forgotten
scratch-hole.

The enforcement fixes this. Every evidence macro stamps its emitted
declaration with `@[manifest_entry]`. The attribute is invisible in
the source — `UnprovenConjecture foo : P` is still one clean line —
but it makes manifest entries distinguishable to the elaborator.
`DerivedConjecture` and `DecomposedConjecture` refuse to compile if
any sorry-bearing dep lacks the attribute:

```
error: DerivedConjecture bad_claim: sorry deps must be declared via
       manifest macros. These deps are stray sorries, not manifest
       entries:
         #[stray_sorry]
       Fix by either wrapping each in the appropriate manifest macro,
       or replacing with a real proof.
```

After the enforcement: every sorry dep of a `DerivedConjecture` is a
named manifest entry with a known evidence level. The trust report is
complete by construction. There is no off-the-record sorry, because
any off-the-record sorry breaks the build.

## 4. Why This Matters for AI

LLMs working on Lean code today face a comprehension crisis: the
library is too big to fit in context, proof bodies are unnecessary for
*using* a theorem, but standard Lean gives no machine-extractable
distinction between proven and sorry-bearing claims at the interface.
Every consumer has to open every proof file to know what's real.

Lean Manifests solve this directly. An LLM scans the manifest files,
sees the evidence level of each claim, and proceeds accordingly. A
claim marked `DerivedConjecture` names its stated dependencies. If
the AI needs higher confidence than the derivation offers, it knows
exactly which assumptions to strengthen.

Measurement on CSLib (130 files, 768 theorems): 20,837 lines of source
reduce to 4,173 lines of manifest + vocabulary. A benchmark on the
same library shows **42% fewer tokens for identical comprehension
accuracy** when LLMs read manifests versus the full source.

## 5. The Macro Toolkit

All macros live in `DeanLean/Basic.lean` (~300 lines including the
enforcement). They layer on top of stock Lean 4 — no compiler
patches, no plugins:

- `Signature foo : T` — totality-aware type check; creates an axiom
  if `foo` doesn't exist yet (spec-first mode).
- `UnprovenConjecture foo : T`, `TestedConjecture foo : T`,
  `DecomposedConjecture foo : T`, `DerivedConjecture foo : T`,
  `ProvenTheorem foo : T` — the five evidence levels.
- `FastHeader foo : T` — an axiom tagged as a manifest entry, for the
  fast-mode workflow (see Appendix A).
- `VerifyAxiom foo : T` — CI-only pairing of a fast-mode axiom with
  its `_proof` or `_derivation`.
- `ExternalTheorem foo := @Lib.name : T` — wraps a theorem from
  another library, type-checked at the facade so upstream API drift
  is caught immediately.
- `Wrap foo_proof := @Lib.name` — name-convention bridge for external
  theorems.

Every evidence macro supports **redundant manifests**: if `foo`
already exists from an upstream manifest, the macro just
type-checks the claim against the existing definition. Safe to
repeat across a facade and an aggregator.

Promotion between levels is a one-keyword edit. `ProvenTheorem`
accepts both `_proof` and `_derivation`, so
`DerivedConjecture foo` → `ProvenTheorem foo` requires no file
renaming. An optional `promote.sh` script rewrites headers
automatically when a proof file appears.

## 6. Applied to Other Languages

The ideas generalize. Separating *what you're claiming* from *how
you established it* isn't specific to theorem provers — it's the same
move as C++ header files, Rust traits, or Haskell type signatures,
with the addition of an explicit evidence level.

The C++ standard library formalization (`dean_lean`) applies this
pattern to a language-boundary-crossing project: Lean manifests model
the N4950 C++ specification, bottoming out in axioms about C++'s
execution model where the spec is prose. Similar work is plausible
for any API whose specification has internal structure (POSIX, the
Lean environment itself, HTTP verbs, etc.).

---

## Appendix A: Cascade Prevention and Fast Mode

When the original "Levelized Lean" work began, Lean's build system
(Lake) tracked dependencies at the `.olean` level. Changing a proof
in a low-level file triggered recompilation up the entire import
chain, even when the exported signatures were identical. For large
libraries or long proof chains, this serial bottleneck dominated
development time.

The project proposed two mitigations:

- **Signature isolation.** Keep the interface (types and theorem
  statements) in one file; put the proof in another. Consumers import
  only the interface file. Lake then sees the interface `.olean` as
  unchanged even when the proof `.olean` regenerates.
- **Fast mode.** The `FastHeader` macro declares a theorem as an
  `axiom` with no proof import at all. Consumers using fast mode skip
  the proof elaboration entirely; a CI-only `VerifyAxiom` closes the
  soundness gap by separately confirming each axiom has a matching
  proof.

### What changed

Lean 4.30's `module` keyword implemented semantic hashing in the
compiler: changing a proof body no longer cascades to downstream
dependents if the module's public interface is bit-for-bit identical.
The cascade problem that motivated signature isolation is now solved
upstream. Testing on CSLib confirms: changing a proof in a `module`
file does not trigger downstream recompilation.

This means **the original physical-design motivation for Lean
Manifests has largely moved into the compiler**. What remains — and
what this document leads with — is the evidence hierarchy, the
vocabulary separation, and the enforcement of complete trust reports.
Those are the load-bearing contributions now. The cascade prevention
is a nice-to-have for projects that haven't yet adopted `module`, and
fast mode remains useful for LLM agents that want sub-second
type-checking without waiting for any proof to compile.

### Resolving mutual recursion across levels

One case where explicit levelization is still useful: when logical
mutual recursion exists (e.g., $f$ calls $g$, and $g$ calls $f$) but
the physical import graph must be acyclic. The workaround is three
levels:

- **Level N (Signatures):** Abstract interface defining $f$ and $g$.
- **Level N+1 (Parameterized Implementations):** $f$ and $g$ in
  separate files as higher-order functions taking their recursive
  counterparts as arguments.
- **Level N+2 (The Knot):** A file importing both implementations and
  closing the recursion with a `mutual` block or fixed-point
  combinator.

This is still a live technique, but it's a technique for handling a
specific structural need, not the central design principle it once
seemed to be.

## Appendix B: Massive Parallel Verification

A corollary of signature isolation: if the interface of module $N$ is
frozen, module $N+1$'s proofs can be verified independently against
that interface. Proof elaboration becomes embarrassingly parallel —
limited only by the single longest proof rather than the depth of the
dependency chain.

Lean 4.30's `module` semantic hashing should make Lake exploit this
parallelism automatically. For projects that haven't adopted
`module`, the fast-mode / signature-isolation workflow reaches the
same asymptote by hand.

## Appendix C: Naming History

"Levelized Lean" was the original name, borrowed from John Lakos's
"Large-Scale C++ Software Design" where levelization refers to
organizing software into strict acyclic layers. The name was accurate
when the main contribution was physical-design-driven cascade
prevention.

As the work shifted toward the evidence hierarchy and manifest
contracts, "Levelized Lean" became misleading — it advertised the
wrong thing. The project is now called **Lean Manifests**. The old
name persists in URLs, module names, and filenames for compatibility;
those will migrate when the web-serving infrastructure is updated.
The `levelized.fast` option identifier is similarly preserved for
backward compatibility, though its spelling is a historical artifact
rather than a semantic claim.
