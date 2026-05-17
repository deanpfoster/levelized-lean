# Writing a Good Manifest

A manifest is a **living dashboard** for your Lean 4 project. It answers
three questions for three audiences:

- **Consumers** ("Should I depend on this?"): What does this library
  actually promise? What evidence backs those promises?
- **Maintainers** ("What's still TODO?"): Where are the gaps? What's
  proven, what's tested, what's aspirational?
- **Contributors** ("Where can I help?"): Which conjectures are
  approachable entry points? What's blocked on what?

A manifest is NOT a proof obligation list. It's a contract written for
humans, decorated with machine-checkable evidence levels.

---

## 1. The shape of a good top-level `Manifest.lean`

Your project's root `Manifest.lean` should contain **4–6 headline
claims** — the load-bearing promises your library makes. Write them
for the consumer, not for yourself.

Structure:

```lean
import DeanLean.Basic
import YourProject.Manifests.Axis1
import YourProject.Manifests.Axis2

/-! # YourProject — Manifest

What this library promises:
1. <plain English description of claim 1>
2. <plain English description of claim 2>
...

## What we do NOT claim

- <explicit boundary 1>
- <explicit boundary 2>
-/

-- Claim 1: one-line English summary
-- Evidence: TestedConjecture (N/M examples passing)
Restate YourProject.Manifests.Axis1.headline_claim_1

-- Claim 2: one-line English summary
Restate YourProject.Manifests.Axis2.headline_claim_2
...
```

Key principles:

- **"What we do NOT claim" is mandatory.** Consumers need to know
  boundaries. If you don't claim full CommonMark compliance, say so.
  If you don't claim thread safety, say so.
- **4–6 claims, not 40.** The top-level manifest is an executive
  summary. Detail lives in per-axis files.
- **Plain English headers above each claim.** The Lean type is the
  formal statement; the comment is for humans who don't read Lean.

The canonical example is markdown-cm's `MarkdownCM/Manifest.lean`:
a handful of headline claims (conformance, termination, roundtrip
stability), an explicit "What we do NOT claim" section (no HTML
sanitization, no extensions), and `Restate` pulling from per-axis
manifests.

---

## 2. Per-axis decomposition

When your project is large enough to have multiple independent
concerns, split into `Manifests/<Axis>.lean` files. Each axis is a
single concern with its own claims and evidence.

Example axes (from markdown-cm):

| File | Concern |
|------|---------|
| `Manifests/Conformance.lean` | Spec compliance per section |
| `Manifests/Termination.lean` | Parser always terminates |
| `Manifests/Roundtrip.lean` | Parse→render→parse stability |
| `Manifests/Renderer.lean` | Output well-formedness |

Benefits:

- Each axis can progress independently (conformance at 60% while
  termination is fully proven).
- Contributors can focus on one axis without understanding the others.
- The top-level manifest stays readable by restating only headlines.

When to decompose: if you have more than ~8 claims, or if claims
naturally cluster into independent concerns. A 3-claim project
doesn't need decomposition — a single `Manifest.lean` is fine.

The top-level manifest imports each axis and uses `Restate` to pull
in the headline claim from each. This keeps the top-level file short
and navigable while the detail lives where it belongs.

---

## 3. Showing live progress with `registerTestResults`

This is the killer pattern. Decorate conjectures with live test
counts so anyone reading the manifest sees progress without building:

```lean
-- CommonMark §4.1: ATX headings
-- 19 of 22 spec examples passing
registerTestResults atx_headings_conformance (passed := 19) (total := 22)
@[entry_point, estimated_minutes 30]
UnprovenConjecture atx_headings_conformance :
  ∀ (input expected : String),
    input ∈ atxHeadingExamples →
    render (parse input) = expected
```

What this gives each audience:

- **Consumer**: "ATX headings are 86% conformant — good enough for
  my use case" (or not).
- **Maintainer**: "3 examples still failing — that's the next task."
- **Contributor**: "This is an entry point, estimated 30 minutes,
  and I can see exactly what's left."

The gap between `passed` and `total` IS the work-in-progress. No
separate tracking system needed.

Update `registerTestResults` whenever you fix a test. The numbers
in the manifest are the source of truth for progress. When all tests
pass, promote to `TestedConjecture` and the numbers become a
permanent record of coverage breadth.

---

## 4. Workplan attributes

For parallel agent work, decorate `UnprovenConjecture` entries with
scheduling metadata from `DeanLean.Workplan`:

```lean
@[entry_point]                    -- independently approachable
@[estimated_minutes 45]           -- rough effort budget
@[depends_on parse_paragraphs]    -- blocked until this is done
UnprovenConjecture parse_lists_conformance : ...
```

- `@[entry_point]`: no unmet dependencies; an agent can start here.
- `@[estimated_minutes N]`: rough time budget for the task.
- `@[depends_on x, y]`: blocked until `x` and `y` are promoted.

**Strip all workplan metadata on promotion.** Once a conjecture
becomes `TestedConjecture` or `ProvenTheorem`, the scheduling info
is noise. Remove it.

Run `lake env lean --run Scripts/Workplan.lean` to see the current
state: entry points ready to claim, blocked items, and untagged work.

---

## 5. Anti-patterns to avoid

### 5a. Vacuous totality

**Bad:**
```lean
UnprovenConjecture parse_total :
  ∀ (s : String), ∃ (d : Document), parse s = d
```

This is trivially true for ANY function — even a diverging one.
The existential `∃ d, f x = d` says nothing about termination,
correctness, or behavior. It's a tautology disguised as a claim.

**What to do instead:**

- Rely on Lean's structural-recursion checker. If your `def` compiles
  without `partial`, Lean has already proven termination. Don't
  restate what the kernel gives you for free.
- If you must use `partial def`, document WHY (e.g., "input is
  streaming; termination depends on external EOF") and test with
  adversarial inputs.
- If you want to claim totality, prove something with real shape:
  `parse s` returns a `Document` satisfying specific structural
  properties, not just that it returns *something*.

### 5b. Trivially decidable claims left as UnprovenConjecture

**Bad:**
```lean
UnprovenConjecture canonicalize_empty : canonicalize "" = ""
```

If `canonicalize` is a non-`partial` function that reduces on `""`,
this is provable by `decide` or `native_decide`. Leaving it as
`UnprovenConjecture` is noise — it signals "we haven't verified this"
when in fact the kernel can verify it in milliseconds.

**Rule:** If `decide` works, use `ProvenTheorem`. If it doesn't work
(timeout, universe issues), explain why in a comment and leave as
`TestedConjecture` with a concrete witness.

### 5c. True-typed conjectures

The extreme case of 5b: a conjecture whose type is `True` or is
trivially inhabited. This was caught by our earlier cleanup discipline
(the `True`-typed audit). Mention it here for completeness: if your
claim's type is trivially provable by `trivial`, it's not a claim.

### 5d. Sorry'd ProvenTheorems

**Bad:**
```lean
ProvenTheorem foo : P := by sorry
```

A `ProvenTheorem` with `sorry` is a lie. The macro should reject this
at elaboration time (and does, if you're using the current version of
lean-manifests). But if you're tempted to "temporarily" sorry a
ProvenTheorem — don't. Use `UnprovenConjecture` for unproven claims.
Promote when proven. The evidence level IS the status.

---

## 6. Promotion discipline

Claims move through evidence levels as work progresses:

```
UnprovenConjecture     — writing the implementation
       ↓
FailingConjecture      — tests registered, some failing
       ↓
TestedConjecture       — 100% of registered tests pass
       ↓
ProvenTheorem          — kernel-checked proof (no sorry)
```

Guidelines:

- **Start at `UnprovenConjecture`** while the feature is being
  implemented. Add `@[entry_point]` and `@[estimated_minutes]` if
  you want agents to pick it up.
- **Add `registerTestResults` early.** Even `passed := 0` is useful —
  it shows the claim is being actively worked.
- **Use `FailingConjecture`** when some tests pass but not all. This
  is honest: "we're making progress but aren't there yet."
- **Promote to `TestedConjecture`** when all registered tests pass.
  This requires a `_test` witness in scope.
- **Promote to `ProvenTheorem`** when you have a kernel-checked proof.
  This is rare for IO-bound properties (you can't prove the OS
  behaves correctly) but common for pure functions.
- **On promotion, strip workplan metadata.** Remove `@[entry_point]`,
  `@[estimated_minutes]`, `@[depends_on]`. The work is done.

Never skip levels to look good. A `TestedConjecture` with 5 concrete
witnesses is more honest than a `ProvenTheorem` you're not sure about.

---

## 7. Documentation hygiene

### Comments are for humans

```lean
-- Claim: parsing any valid ATX heading produces exactly one
-- Heading node with the correct level (1-6).
-- Why: this is the most basic structural guarantee consumers need.
TestedConjecture atx_heading_structure : ...
```

- The `--` comment above a claim explains WHAT it says in plain
  English and WHY it matters.
- Use `--` line comments, not `/-- -/` docstrings. The
  `UnprovenConjecture` macro doesn't accept attached docstrings
  (known limitation).

### Headers organize the manifest

Use `/-! ... -/` module docstrings for section headers:

```lean
/-! ## Conformance: Block-level elements -/

-- ATX headings (§4.1)
registerTestResults ...
TestedConjecture atx_conformance : ...

/-! ## Conformance: Inline elements -/
...
```

### Explain design evolution

When a claim's formulation changes, leave a comment explaining why:

```lean
-- Earlier formulation was `∀ s, parse s ≠ none` which is vacuous
-- (parse always returns Something). Replaced with structural claim.
TestedConjecture parse_produces_valid_ast : ...
```

This prevents future contributors from reverting to the bad
formulation.

---

## Quick checklist

Before committing a manifest change:

- [ ] Top-level has 4–6 headline claims, not a dump of everything
- [ ] "What we do NOT claim" section is present and honest
- [ ] Every `UnprovenConjecture` either has workplan metadata or a
      comment explaining why it's deferred
- [ ] No vacuous totality claims (`∀ x, ∃ y, f x = y`)
- [ ] No trivially-decidable claims left as UnprovenConjecture
- [ ] `registerTestResults` numbers are current
- [ ] Promoted claims have workplan metadata stripped
- [ ] Plain English comments above each claim
