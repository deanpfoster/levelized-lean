# Benchmark Answers (Source Files Only)

## Module 1: MergeSort

**Q1:** Does this module prove that mergeSort has O(n log n) time complexity? If yes, what is the theorem called?

Yes. The theorem is `mergeSort_time` (line 200). It proves `(mergeSort xs).time <= n * clog 2 n` where `n := xs.length`. There is also `timeMergeSortRec_le` (line 162) which solves the recurrence, and `mergeSort_time_le` (line 187) which bounds actual time by the recurrence.

**Q2:** What is the exact type signature of `mergeSort_correct`?

```lean
theorem mergeSort_correct (xs : List α) : IsSorted ⟪mergeSort xs⟫ ∧ ⟪mergeSort xs⟫ ~ xs
```
(line 110)

**Q3:** I want to prove that a sorted list merged with another sorted list is still sorted. Which theorem should I use?

Use `sorted_merge` (line 85):
```lean
theorem sorted_merge {l1 l2 : List α} (hxs : IsSorted l1) (hys : IsSorted l2) :
    IsSorted ⟪merge l1 l2⟫
```

---

## Module 2: LTS.Bisimulation

**Q1:** Does this module prove that bisimilarity is an equivalence relation? If yes, what is the theorem called?

Yes. The theorem is `HomBisimilarity.eqv` (line 120):
```lean
theorem HomBisimilarity.eqv : Equivalence (HomBisimilarity lts)
```
There is also `HomWeakBisimilarity.eqv` (line 928) for weak bisimilarity.

**Q2:** What is the exact type signature of the theorem that says bisimilarity implies trace equivalence?

The most direct theorem is `Bisimilarity.le_traceEq` (line 372):
```lean
theorem Bisimilarity.le_traceEq : Bisimilarity lts₁ lts₂ ≤ TraceEq lts₁ lts₂
```
There is also the more foundational `IsBisimulation.traceEq` (line 351):
```lean
theorem IsBisimulation.traceEq
    (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) :
    s₁ ~tr[lts₁,lts₂] s₂
```

**Q3:** I have two LTSs and want to show they are bisimilar using an up-to technique. Which theorem should I use?

Use `IsBisimulationUpTo.is_bisimulation` (line 266):
```lean
theorem IsBisimulationUpTo.is_bisimulation (h : IsBisimulationUpTo lts₁ lts₂ r) :
  IsBisimulation lts₁ lts₂ (UpToHomBisimilarity lts₁ lts₂ r)
```
This shows that any bisimulation up to bisimilarity is a bisimulation, so you can define a relation `r` that is a bisimulation up to bisimilarity, and then use this theorem to obtain an actual bisimulation.

---

## Module 3: Data.Relation

**Q1:** Does this module prove Newman's Lemma (local confluence + termination -> confluence)? If yes, what is it called?

Yes. It is `LocallyConfluent.Terminating_toConfluent` (line 284):
```lean
theorem LocallyConfluent.Terminating_toConfluent (hlc : LocallyConfluent r) (ht : Terminating r) :
    Confluent r
```

**Q2:** What is the exact type signature of the Church-Rosser / confluence theorem?

The Church-Rosser property is defined as an abbreviation (line 84):
```lean
abbrev ChurchRosser (r : α → α → Prop) := ∀ {x y}, EqvGen r x y → Join (ReflTransGen r) x y
```
Confluence is also defined (line 76):
```lean
abbrev Confluent (r : α → α → Prop) := Diamond (ReflTransGen r)
```
The theorem connecting them is `Confluent.toChurchRosser` (line 107):
```lean
theorem Confluent.toChurchRosser (h : Confluent r) : ChurchRosser r
```
And the equivalence is `Confluent_iff_ChurchRosser` (line 138):
```lean
theorem Confluent_iff_ChurchRosser : Confluent r ↔ ChurchRosser r
```

**Q3:** I have a terminating, locally confluent relation and want to show it's confluent. Which theorems do I need?

You need `LocallyConfluent.Terminating_toConfluent` (line 284). This is Newman's Lemma. You supply a proof of `LocallyConfluent r` and `Terminating r`, and it gives you `Confluent r`.

---

## Module 4: CCS.BehaviouralTheory

**Q1:** Does this module prove that parallel composition is commutative up to bisimilarity? If yes, what is the theorem called?

Yes. The theorem is `bisimilarity_par_comm` (line 64):
```lean
theorem bisimilarity_par_comm : (par p q) ~[lts (defs := defs)] (par q p)
```

**Q2:** What is the exact type signature of `bisimilarity_is_congruence`?

```lean
theorem bisimilarity_is_congruence
    (p q : Process Name Constant) (c : Context Name Constant) (h : p ~[lts (defs := defs)] q) :
    (c.fill p) ~[lts (defs := defs)] (c.fill q)
```
(line 427)

**Q3:** I want to simplify a CCS term `P | 0` (parallel with nil). Which theorem should I use?

Use `bisimilarity_par_nil` (line 47):
```lean
theorem bisimilarity_par_nil : (par p nil) ~[lts (defs := defs)] p
```

---

## Module 5: CombinatoryLogic.Confluence

**Q1:** Does this module prove the Church-Rosser theorem for SKI combinatory logic? If yes, what is it called?

Yes. The theorem in its most standard form is `MRed.diamond` (line 217):
```lean
theorem MRed.diamond : Confluent Red
```
There is also `mJoin_red_equivalence` (line 212):
```lean
theorem mJoin_red_equivalence : Equivalence (MJoin Red)
```
which states the Church-Rosser theorem in its general form (that having a common reduct is an equivalence relation).

**Q2:** What is the exact type signature of the diamond property for parallel reduction?

```lean
theorem parallelReduction_diamond : Diamond ParallelReduction
```
(line 142). Where `Diamond` is defined as `∀ {a b c : α}, r a b → r a c → Join r b c`.

**Q3:** I have two reduction sequences from the same term and want to show they converge. Which theorem should I use?

Use `MRed.diamond` (line 217):
```lean
theorem MRed.diamond : Confluent Red
```
This states `Confluent Red`, which unfolds to `Diamond (ReflTransGen Red)`, meaning: given `a ↠ b` and `a ↠ c`, there exists `d` such that `b ↠ d` and `c ↠ d`.

---

## Module 6: PerfectSecrecy.Basic

**Q1:** Does this module prove Shannon's theorem (|K| >= |M| for perfect secrecy)? If yes, what is it called?

Yes. The theorem is `perfectlySecret_keySpace_ge` (line 46):
```lean
theorem perfectlySecret_keySpace_ge [Finite K]
    (scheme : EncScheme M K C) (h : scheme.PerfectlySecret) :
    Nat.card K ≥ Nat.card M
```

**Q2:** What is the exact type signature of the ciphertext indistinguishability characterization?

```lean
theorem perfectlySecret_iff_ciphertextIndist (scheme : EncScheme M K C) :
    scheme.PerfectlySecret ↔ scheme.CiphertextIndist
```
(line 39)

**Q3:** I want to show an encryption scheme is perfectly secret by showing ciphertext distributions are equal. Which theorem do I use?

Use `perfectlySecret_iff_ciphertextIndist` (line 39). Specifically, use the backward direction (`.mpr` or `.2`): if you prove `scheme.CiphertextIndist`, then `perfectlySecret_iff_ciphertextIndist` gives you `scheme.PerfectlySecret`.

---

## Module 7: OmegaLanguage

**Q1:** Does this module prove that omega-power distributes over union? If yes, what is it called?

NOT FOUND. The module does not contain a theorem about omega-power distributing over union. It does prove properties like `kstar_omegaPow_eq_omegaPow`, `hmul_omegaPow_eq_omegaPow`, `hmul_sup`, and `add_hmul`, but not `(l1 + l2)^omega = l1^omega ⊔ l2^omega` or similar.

**Q2:** What is the type signature of the coinduction principle for omega-languages (if it exists)?

Yes, it exists. `omegaPow_coind` (line 393):
```lean
theorem omegaPow_coind [Inhabited α] (h_le : p ≤ (l - 1) * p) : p ≤ l^ω
```
There is also the variant `omegaPow_coind'` (line 378):
```lean
theorem omegaPow_coind' [Inhabited α] (h_nn : [] ∉ l) (h_le : p ≤ l * p) : p ≤ l^ω
```

**Q3:** I want to show that L^omega <= (L*)^omega for some language L. Which theorem should I use?

Use `omegaPow_le_kstar_omegaPow` (line 426):
```lean
theorem omegaPow_le_kstar_omegaPow [Inhabited α] (l : Language α) : l^ω ≤ (l∗)^ω
```
Or even more strongly, `kstar_omegaPow_eq_omegaPow` (line 438) which shows equality:
```lean
theorem kstar_omegaPow_eq_omegaPow [Inhabited α] (l : Language α) : (l∗)^ω = l^ω
```

---

## Module 8: Stlc.Safety

**Q1:** Does this module prove the progress theorem for STLC? If yes, what is it called?

Yes. The theorem is `FullBeta.progress` (line 78):
```lean
theorem progress {t : Term Var} {τ : Ty Base} (ht : [] ⊢ t ∶ τ) : t.Value ∨ ∃ t', t ⭢βᶠ t'
```

**Q2:** What is the exact type signature of the preservation theorem?

```lean
theorem preservation (der : Γ ⊢ t ∶ τ) (step : t ⭢βᶠ t') : Γ ⊢ t' ∶ τ
```
(line 67, under namespace `FullBeta`)

**Q3:** I want to show that a well-typed closed STLC term either is a value or can take a step. Which theorem do I use?

Use `FullBeta.progress` (line 78):
```lean
theorem progress {t : Term Var} {τ : Ty Base} (ht : [] ⊢ t ∶ τ) : t.Value ∨ ∃ t', t ⭢βᶠ t'
```

---

## Module 9: HML.Basic

**Q1:** Does this module prove that HML theory equivalence equals bisimilarity? If yes, what is it called?

Yes. The theorem is `theoryEq_eq_bisimilarity` (line 255):
```lean
theorem theoryEq_eq_bisimilarity (lts : LTS State Label)
    [image_finite : ∀ s μ, Finite (lts.image s μ)] :
    TheoryEq lts = HomBisimilarity lts
```

**Q2:** What is the exact type signature of the modal characterization theorem?

The modal characterization theorem is `theoryEq_eq_bisimilarity` (line 255):
```lean
theorem theoryEq_eq_bisimilarity (lts : LTS State Label)
    [image_finite : ∀ s μ, Finite (lts.image s μ)] :
    TheoryEq lts = HomBisimilarity lts
```

**Q3:** I want to show two states satisfy the same HML formulas. What do I need to show first?

You need to show that the two states are bisimilar (i.e., `s1 ~[lts] s2`). The theorem `bisimulation_TheoryEq` (line 247) shows that if two states are related by a bisimulation then they are theory-equivalent. Additionally, `theoryEq_eq_bisimilarity` (line 255) proves the full equivalence (for image-finite LTSs): `TheoryEq lts = HomBisimilarity lts`, so bisimilarity is both necessary and sufficient.

---

## Module 10: RegularLanguage

**Q1:** Does this module prove that regular languages are closed under complement? If yes, what is it called?

Yes. The theorem is `IsRegular.compl` (line 60):
```lean
theorem IsRegular.compl {l : Language Symbol} (h : l.IsRegular) : (lᶜ).IsRegular
```

**Q2:** What is the type signature of the theorem relating DFA acceptance to regular languages?

```lean
theorem IsRegular.iff_dfa {l : Language Symbol} :
    l.IsRegular ↔ ∃ State : Type, ∃ _ : Finite State,
      ∃ dfa : DA.FinAcc State Symbol, language dfa = l
```
(line 35)

**Q3:** I want to show the intersection of two regular languages is regular. Which theorem should I use?

Use `IsRegular.inf` (line 104):
```lean
theorem IsRegular.inf {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 ⊓ l2).IsRegular
```
