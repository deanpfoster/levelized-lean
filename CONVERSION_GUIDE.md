# Guide: Adding a Manifest to a Lean Library

This guide tells you how to create a non-intrusive manifest for an
existing Lean library — following the Lean Manifests discipline.
The original code is never modified.

## Prerequisites

Read https://lean4.ai/levelized-lean.html for the full architecture
(the URL still uses the old path; the project is now called Lean
Manifests). Key concepts: manifests separate claims from evidence,
five evidence levels (ProvenTheorem / DerivedConjecture /
DecomposedConjecture / TestedConjecture / UnprovenConjecture), and
the `Defs/` + `Proofs/` + manifest file structure.

## The Three Files You Create Per Module

For an original file `Lib/Foo/Bar.lean` with theorems and definitions:

### 1. Defs/Foo/Bar.lean — Vocabulary (what the words mean)

```lean
import LibHeaders.Basic
import Lib.Foo.Bar

open Lib.Foo.Bar  -- make names available

-- Re-export definitions that appear in theorem types
Vocabulary SomeType := @SomeType
Vocabulary someFunction := @someFunction
Vocabulary somePredicate := @somePredicate
```

The `Vocabulary` macro verifies the name exists. If the library is
later replaced, change these to standalone definitions — nothing
else needs to change.

### 2. Proofs/Foo/Bar.lean — Bridge (plumbing)

```lean
import Lib.Foo.Bar

open Lib.Foo.Bar

-- Bridge: original names → _proof naming convention
noncomputable def theorem1_proof := @theorem1
noncomputable def theorem2_proof := @theorem2
noncomputable def theorem3_proof := @theorem3
```

One line per theorem. Each creates a `_proof` alias that
`ProvenTheorem` in the manifest will find.

### 3. Foo/Bar.lean — Manifest (the claims)

```lean
import LibHeaders.Basic
import LibHeaders.Defs.Foo.Bar
import LibHeaders.Proofs.Foo.Bar

/-! # Module Title
  Vocabulary:
    SomeType — brief description
    someFunction — brief description
-/

open Lib.Foo.Bar

-- Public theorems only (skip internal lemmas)
ProvenTheorem theorem1 : <exact type signature>
ProvenTheorem theorem2 : <exact type signature>
ProvenTheorem theorem3 : <exact type signature>
```

## Gotchas

### Type signatures must match EXACTLY
The `ProvenTheorem` macro expands to `theorem foo : T := foo_proof`.
If `T` doesn't match `foo_proof`'s type, it fails. Common issues:

- **Implicit arguments**: Use `∀ {α} [inst]` not `∀ (α) [inst]`
- **Universe polymorphism**: Check with `#check @theorem_name`
- **Notation**: `~` for Perm may not be available — use `.Perm` instead
- **Namespaces**: After `open Lib.Foo`, `Bar` resolves — but in type
  signatures you may need the full path

### Use `@` for the proof bridge
In `Proofs/`, always use `@` to reference theorems:
```lean
noncomputable def foo_proof := @Lib.Foo.Bar.foo
```
This avoids implicit argument resolution issues.

### Use `open` liberally in manifests
Manifests should be readable. Open the relevant namespaces so types
are concise:
```lean
open Lib.Foo.Bar  -- now IsSorted not Lib.Foo.Bar.IsSorted
```

### Skip private theorems
If the source has `private theorem helper_lemma`, don't include it.
Only expose theorems a consumer would use.

### Skip instances
Typeclass instances (`instance : Foo Bar`) are not theorems.
Don't create ProvenTheorem entries for them.

### Public vs Internal
A theorem is PUBLIC if a consumer would invoke it directly.
A theorem is INTERNAL if it's only used as a stepping stone
in other proofs. Only PUBLIC theorems go in the manifest.

Rule of thumb: if the theorem appears in the module's docstring
or "Main results" section, it's public.

### Lean version differences
- Lean 4.30: `noncomputable theorem` is an error (use `theorem`)
- Lean 4.30: `open ... in` must immediately precede the declaration
  (no intervening doc comments)
- Lean 4.16: `noncomputable theorem` works fine

### Testing your manifest
After creating all three files:
```bash
lake build LibHeaders.Foo.Bar
```
If it compiles, the types match. If it fails, the error message
tells you which theorem's type doesn't match.

## Sizing Guide

- **Defs file**: ~1 line per vocabulary definition + imports
- **Proofs bridge**: ~1 line per theorem + imports
- **Manifest**: ~2 lines per public theorem + ~5 lines vocabulary comments
- **Total overhead**: ~30-50 lines per module

A 200-line original file with 14 theorems → ~7 public theorems
→ manifest of ~20 lines + Defs ~10 lines + Proofs ~10 lines = ~40 lines total.

## Workflow

1. Read the original .lean file
2. Identify PUBLIC theorems (grep for `theorem` and `lemma`)
3. Identify vocabulary (types/defs that appear in theorem signatures)
4. Create Defs/ with Vocabulary entries
5. Create Proofs/ with _proof bridges
6. Create manifest with ProvenTheorem entries
7. `lake build` and fix type mismatches
8. Repeat for next module
