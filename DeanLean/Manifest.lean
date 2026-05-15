import DeanLean.Manifests.MacroContracts

/-! # Manifest for the Lean Manifests System

  Two manifests, one going up, one going down:

  **LeanEnvironment.lean** — manifest TO Leo (15 claims about Lean's 200K+ lines)
    15 UnprovenConjectures + 1 ProvenTheorem (error_bind_is_error, proven by rfl)
    Vocabulary: UsesSorry, SorryFree, DirectlySorry, IsTheoremElaboration
    All claims have real Prop types — zero placeholder True.

  **MacroContracts.lean** — manifest FROM us (3 DerivedConjectures)
    ProvenTheoremSpec: n_proof exists → sorry-free thmInfo with matching type
    TestedConjectureSpec: n_test exists → sorry thmInfo
    EvidenceOrderingInvariant: _proof names are SorryFree, _test names UsesSorry
    Dependencies auto-discovered: elab_theorem_creates_thmInfo, real_proof_no_sorry,
      find_name_consistent, sorry_proof_detected

  **Tests** — verify contracts on concrete names at elaboration time
    EnvironmentTests.lean: #check_is_theorem, #check_has_sorry, etc.
    ManifestTests.lean: macro behavior tests

  ## Evidence Hierarchy

  ○ UnprovenConjecture    — sorry IS the theorem (TODO: close eventually)
  ◆ ManifestAxiom         — sorry IS the theorem (permanent env assumption, OK)
  ✗ FailingConjecture     — tests exist, some fail (known broken)
  ◐ TestedConjecture      — sorry is the ∀ (all tests pass)
  ◑ DecomposedConjecture  — sorry is in the lemmas (all tested)
  ◕ DerivedConjecture     — sorry is in other modules
  ● ProvenTheorem         — no sorry anywhere

  ## Test macro

  `Test foo := show <expr> = <val> from rfl` — tries elaboration at compile time.
  If rfl succeeds, records pass. If it fails, records fail (compilation continues).
  Multiple Tests per name accumulate into pass/total counts.
  TestedConjecture requires all pass; FailingConjecture requires at least one fail.
  DerivedConjecture/DecomposedConjecture do blame analysis when tests fail.

  ## Dependency chain

  Leo's Lean (200K+ lines)
    ↑ 15 UnprovenConjectures + 1 ProvenTheorem (LeanEnvironment.lean)
  Our macros (350 lines)
    ↑ 3 DerivedConjectures depending on 5 of Leo's claims (MacroContracts.lean)
  Library manifests (CSLib, C++, Interval, etc.)
    ↑ ProvenTheorem / TestedConjecture / FailingConjecture / etc.
  Consumers
-/
