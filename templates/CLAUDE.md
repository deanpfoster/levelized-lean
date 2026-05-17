# CLAUDE.md

<!--
  This is a starter template for projects using lean-manifests.
  Copy to your project root, customize the project-specific sections,
  and delete these instructions.
-->

You are working on a Lean 4 project that uses **lean-manifests** for
evidence-tagged claims and the trust report. Read these conventions
before making changes.

<!-- BEGIN: lean-manifests-specific (keep as-is unless you know what you're doing) -->

## Required reading

Before writing or reviewing manifests, read
**`templates/MANIFEST_GUIDE.md`** in the lean-manifests repo. It covers
the shape of a good manifest, the `registerTestResults` pattern,
anti-patterns to avoid, and promotion discipline.

## The evidence hierarchy

Every claim in the codebase has a named evidence level:

- `ProvenTheorem` (●) — kernel-checked proof. The build verifies it.
- `DerivedConjecture` (◕) — proven modulo named axioms.
- `ManifestAxiom` (◆) — permanent environmental assumption (OS,
  network, hardware). Type-checked, content trusted.
- `TestedConjecture` (◐) — verified for concrete inputs at build time.
- `UnprovenConjecture` (○) — TODO: a hole expected to close.

When you read a manifest entry, the symbol tells you the strength of
the evidence. A `ProvenTheorem` is binding; an `UnprovenConjecture`
is documentation.

## Manifest workflow

Before modifying any function in the codebase, consult what theorems
constrain it:

```bash
bash Scripts/show-theorems.sh PROJECT.functionName
```

This surfaces:
- `@[theorems ...]` annotations on the function (explicit links)
- Theorems whose statements mention the function (auto-detected)

Look at each theorem before changing the function. The theorem is the
contract. If your change would break the theorem, either the theorem
must change with it (and you document why), or the change is wrong.

After modifying:

```bash
bash Scripts/verify-all.sh   # full pre-commit check
```

If a theorem broke, the build will tell you. Don't suppress with
`sorry` — fix the code, or update the theorem statement and document.

## Annotating new theorems

When you add a new theorem about a function, tag the function with
`@[theorems ...]` if the theorem is load-bearing:

```lean
@[theorems my_new_theorem]
def myFunction (x : Nat) : Nat := ...
```

Sparse annotations are better than dense; the auto-detection covers
the rest. Annotate only the most important relationships.

## Parallel work via the workplan

If multiple agents are working on this project in parallel (e.g., via
spawn or just via separate terminals), use the workplan to coordinate:

```bash
lake env lean --run Scripts/Workplan.lean
```

This prints UnprovenConjectures organized as:
- **Entry points** — independently approachable, no unmet deps
- **Blocked** — waiting on other entries
- **Other** — no deps but not flagged as entry point

Each agent picks an entry point matching its time budget, claims it via
a one-line commit ("wip: claiming X"), and works. When the entry promotes
to ProvenTheorem or TestedConjecture, strip its workplan metadata
(`@[depends_on]`, `@[estimated_minutes]`, `@[entry_point]`).

The workplan is a coordination tool, not a safety tool. The kernel still
verifies anything that claims ProvenTheorem status.

## Never

These are kernel-blocked or audit-checked. Don't try:

- Replace a `ProvenTheorem` with `sorry` (build fails)
- Add raw `axiom` keyword in your project namespace (kernel-blocked
  if you have a `no_<NS>_raw_axioms` theorem)
- Add `unsafe def` in your namespace (kernel-blocked similarly)
- Add `initialize` blocks (kernel-blocked if checked)
- Bypass the evidence hierarchy (caught at build time)

## Honest limitation

The manifest discipline catches you at *build time*, not before you
start writing. The workflow above asks you to consult manifests
*before* writing, which is more discipline than the kernel enforces.
Treat it as a habit to develop, not as a rule the system imposes.

<!-- END: lean-manifests-specific -->


<!-- BEGIN: project-specific (customize for your project) -->

## Project overview

<!-- TODO: 1-2 sentences on what this project does. -->

## Build & verify

<!-- TODO: your project's build commands. Example below. -->

```bash
source ~/.elan/env
lake build           # or `lake build <target>` for specific target
bash Scripts/verify-all.sh   # if you have a verify script
```

## Architecture

<!-- TODO: a few key directories and their purpose. Example below. -->

```
YourProject/
  Defs/        # vocabulary types and predicates
  Code/        # pure functions (no IO)
  Tools/       # IO-doing wrappers
  Manifests/   # claims with evidence levels
  Proofs/      # proofs that establish the claims
```

## Key files

<!-- TODO: list the 3-5 most important files for someone navigating
     the codebase for the first time. -->

- `<file>` — <one-line description>

## Commit conventions

<!-- TODO: how this project does commits, branches, PRs. -->

<!-- END: project-specific -->
