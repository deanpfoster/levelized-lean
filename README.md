# lean-manifests

Macros and tooling for **evidence-tagged claims** in Lean 4.

The thesis: every theorem in a Lean module should carry a named
evidence level, the compiler should track where every `sorry` lives,
and the trust report should be a build artifact.

## What's here

- **Macros** for evidence-tagged declarations:
  - `ProvenTheorem` (kernel-checked proof)
  - `DerivedConjecture` (proven modulo named axioms)
  - `ManifestAxiom` (permanent environmental assumption)
  - `TestedConjecture` (verified for concrete inputs)
  - `UnprovenConjecture` (TODO)
- **`@[theorems]`** attribute for linking functions to their theorems
- **`DeanLean.IndexGen`** — generic theorem-index generator that any
  project using this library can call to produce a function-keyed
  index of theorem coverage
- **`DeanLean.Workplan`** — generic workplan generator for parallel
  LLM agents. Reads `@[depends_on]`, `@[estimated_minutes]`, and
  `@[entry_point]` attributes on UnprovenConjectures and surfaces
  ready-to-start work in three buckets (entry points, blocked,
  other).
- **`FullyAttested`** — a compile-time check that all sorry-deps of
  a derivation are explicit `ManifestAxioms`, never stray TODOs

## How to use

```lean
-- In your lakefile.lean:
require dean_lean from git "https://github.com/deanpfoster/lean-manifests" @ "mainline"
```

Then in your code:

```lean
import DeanLean.Basic

ProvenTheorem foo : ∀ x, P x := by ...
ManifestAxiom os_assumption : ∀ x, Q x
DerivedConjecture combined : ∀ x, P x ∧ Q x := ⟨foo x, os_assumption x⟩
```

The compiler tracks the evidence chain. The trust report shows what
your top-level claims rest on.

## Starting a new project

We ship templates for AI coding agents at **`templates/`**. Copy
`templates/CLAUDE.md` (or `templates/AGENTS.md` for tools that read
that convention) to your project root and customize. The templates
prescribe a workflow that makes manifests usable as design specs,
not just build-time tripwires:

1. Before modifying a function, run `bash Scripts/show-theorems.sh
   PROJECT.functionName` to see what theorems constrain it
2. After modifying, run `bash Scripts/verify-all.sh`
3. Annotate new theorems with `@[theorems]` on the function they
   describe

See `templates/README.md` for details.

## Documentation

- **`CLAUDE.md`** — workflow and conventions for working ON
  lean-manifests itself (not for downstream users — see
  `templates/` for that)
- **`templates/`** — starter agent configs for downstream projects
- **`templates/MANIFEST_GUIDE.md`** — how to write a good manifest
  (patterns, anti-patterns, promotion discipline)
- **`CONVERSION_GUIDE.md`** — guide for converting existing Lean code
  to use the manifest discipline
- **`CPP_PROJECT.md`** — an example: formalizing the C++ standard
  library with manifests
- **`pitch-to-leo.md`** — the design rationale, in essay form

## Status

Active development. Used in production by:
- `cslib` (computability and language theory)
- `dean_lean/Cpp/*` (C++ standard library formalization)
- `l3m` (Lean LLM agent — kernel-verified safety theorems)

## License

See LICENSE.
