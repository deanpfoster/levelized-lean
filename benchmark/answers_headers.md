# Answers (Header Files Only)

## Module 1: MergeSort

**Q1:** Does this module prove that mergeSort has O(n log n) time complexity? If yes, what is the theorem called?

Yes. The theorem is called `mergeSort_time`. It states:
`(mergeSort xs).time ≤ xs.length * Nat.clog 2 xs.length`
(at most n * ceil(log2 n) comparisons, which is O(n log n)).
Based on: ExternalTheorem `mergeSort_time` (lines 57-60).

**Q2:** What is the exact type signature of mergeSort_correct?

```
∀ {α : Type} [LinearOrder α] (xs : List α),
  IsSorted ⟪mergeSort xs⟫ ∧ ⟪mergeSort xs⟫.Perm xs
```
Based on: ExternalTheorem `mergeSort_correct` (lines 38-41).

**Q3:** I want to prove that a sorted list merged with another sorted list is still sorted. Which theorem should I use?

Use `sorted_merge`. Its type signature is:
`∀ {α : Type} [LinearOrder α] {l1 l2 : List α}, IsSorted l1 → IsSorted l2 → IsSorted ⟪merge l1 l2⟫`
Based on: ExternalTheorem `sorted_merge` (lines 25-28).

---

## Module 2: LTS.Bisimulation

**Q1:** Does this module prove that bisimilarity is an equivalence relation? If yes, what is the theorem called?

Yes. The theorem is called `homBisimilarity_eqv`. It states:
`Equivalence lts.HomBisimilarity`
Based on: ExternalTheorem `homBisimilarity_eqv` (lines 90-93).

**Q2:** What is the exact type signature of the theorem that says bisimilarity implies trace equivalence?

```
∀ {State : Type u_1} {Label : Type u_2} {lts₁ : LTS State Label}
  {State_1 : Type u_3} {lts₂ : LTS State_1 Label},
  lts₁.Bisimilarity lts₂ ≤ lts₁.TraceEq lts₂
```
Based on: ExternalTheorem `bisimilarity_le_traceEq` (lines 161-165).

**Q3:** I have two LTSs and want to show they are bisimilar using an up-to technique. Which theorem should I use?

Use `isBisimulationUpTo_is_bisimulation`. It states that any bisimulation up to bisimilarity is a bisimulation:
`lts₁.IsBisimulationUpTo lts₂ r → lts₁.IsBisimulation lts₂ (lts₁.UpToHomBisimilarity lts₂ r)`
You define a relation `r` that is a bisimulation up to bisimilarity, then this theorem gives you an actual bisimulation, from which you can conclude bisimilarity.
Based on: ExternalTheorem `isBisimulationUpTo_is_bisimulation` (lines 135-139).

---

## Module 3: Data.Relation

**Q1:** Does this module prove Newman's Lemma (local confluence + termination -> confluence)? If yes, what is it called?

Yes. The theorem is called `locallyConfluent_terminating_toConfluent`. It states:
`Relation.LocallyConfluent r → Relation.Terminating r → Relation.Confluent r`
Based on: ExternalTheorem `locallyConfluent_terminating_toConfluent` (lines 256-259).

**Q2:** What is the exact type signature of the Church-Rosser / confluence theorem?

There are several relevant theorems. The direct confluence/Church-Rosser equivalence is:
```
∀ {α : Type u_1} {r : α → α → Prop},
  Relation.Confluent r ↔ Relation.ChurchRosser r
```
Based on: ExternalTheorem `confluent_iff_churchRosser` (lines 130-133).

The theorem that derives Church-Rosser from confluence is:
```
∀ {α : Type u_1} {r : α → α → Prop},
  Relation.Confluent r → Relation.ChurchRosser r
```
Based on: ExternalTheorem `confluent_toChurchRosser` (lines 111-114).

**Q3:** I have a terminating, locally confluent relation and want to show it's confluent. Which theorems do I need?

You need `locallyConfluent_terminating_toConfluent` (Newman's Lemma):
`Relation.LocallyConfluent r → Relation.Terminating r → Relation.Confluent r`
Provide proofs of `Relation.LocallyConfluent r` and `Relation.Terminating r` to obtain `Relation.Confluent r`.
Based on: ExternalTheorem `locallyConfluent_terminating_toConfluent` (lines 256-259).

---

## Module 4: CCS.BehaviouralTheory

**Q1:** Does this module prove that parallel composition is commutative up to bisimilarity? If yes, what is the theorem called?

Yes. The theorem is called `bisimilarity_par_comm`. It states:
`(lts (defs := defs)).HomBisimilarity (p.par q) (q.par p)`
Based on: ProvenTheorem `bisimilarity_par_comm` (lines 45-49).

**Q2:** What is the exact type signature of bisimilarity_is_congruence?

```
∀ {Name : Type u_1} {Constant : Type u_2}
  {defs : Constant → Process Name Constant → Prop}
  (p q : Process Name Constant) (c : Context Name Constant),
  (lts (defs := defs)).HomBisimilarity p q →
    (lts (defs := defs)).HomBisimilarity (c.fill p) (c.fill q)
```
Based on: ProvenTheorem `bisimilarity_is_congruence` (lines 126-131).

**Q3:** I want to simplify a CCS term `P | 0` (parallel with nil). Which theorem should I use?

Use `bisimilarity_par_nil`. It states:
`(lts (defs := defs)).HomBisimilarity (p.par Process.nil) p`
This shows `P | nil ~ P`.
Based on: ProvenTheorem `bisimilarity_par_nil` (lines 38-42).

---

## Module 5: CombinatoryLogic.Confluence

**Q1:** Does this module prove the Church-Rosser theorem for SKI combinatory logic? If yes, what is it called?

Yes. The theorem is called `MRed.diamond` (confluence of Red). It states:
`Relation.Confluent Red`
There is also `mJoin_red_equivalence` which states `Equivalence (Relation.MJoin Red)`.
Based on: ProvenTheorem `MRed.diamond` (lines 46-47) and `mJoin_red_equivalence` (lines 42-43).

**Q2:** What is the exact type signature of the diamond property for parallel reduction?

```
Relation.Diamond ParallelReduction
```
Based on: ProvenTheorem `parallelReduction_diamond` (lines 34-35).

**Q3:** I have two reduction sequences from the same term and want to show they converge. Which theorem should I use?

Use `MRed.diamond` (confluence of `Red`):
`Relation.Confluent Red`
This says that `Red` is confluent, meaning `Relation.ReflTransGen Red` has the diamond property -- any two multi-step reduction sequences from the same term can be joined.
Based on: ProvenTheorem `MRed.diamond` (lines 46-47).

---

## Module 6: PerfectSecrecy.Basic

**Q1:** Does this module prove Shannon's theorem (|K| >= |M| for perfect secrecy)? If yes, what is it called?

Yes. The theorem is called `perfectlySecret_keySpace_ge`. It states:
`scheme.PerfectlySecret → Nat.card K ≥ Nat.card M`
Based on: ProvenTheorem `perfectlySecret_keySpace_ge` (lines 29-31).

**Q2:** What is the exact type signature of the ciphertext indistinguishability characterization?

```
∀ {M K C : Type u_1} (scheme : EncScheme M K C),
  scheme.PerfectlySecret ↔ scheme.CiphertextIndist
```
Based on: ProvenTheorem `perfectlySecret_iff_ciphertextIndist` (lines 23-25).

**Q3:** I want to show an encryption scheme is perfectly secret by showing ciphertext distributions are equal. Which theorem do I use?

Use `perfectlySecret_iff_ciphertextIndist`. The backward direction gives you:
`scheme.CiphertextIndist → scheme.PerfectlySecret`
So you prove ciphertext indistinguishability (that the ciphertext distribution is independent of the message), and then apply this iff to conclude perfect secrecy.
Based on: ProvenTheorem `perfectlySecret_iff_ciphertextIndist` (lines 23-25).

---

## Module 7: OmegaLanguage

**Q1:** Does this module prove that omega-power distributes over union? If yes, what is it called?

NOT FOUND. The module does not contain a theorem stating that `(l1 + l2)^omega = l1^omega ⊔ l2^omega` or similar distribution of omega-power over union.

**Q2:** What is the type signature of the coinduction principle for omega-languages (if it exists)?

The coinduction principle is `ω_omegaPow_coind`:
```
∀ {α : Type u_1} {l : Language α} {p : Cslib.ωLanguage α}
  [_inst : Inhabited α],
  p ≤ (l - 1) * p → p ≤ l^ω
```
Based on: ProvenTheorem `ω_omegaPow_coind` (lines 111-114).

**Q3:** I want to show that L^omega is a subset of (L*)^omega for some language L. Which theorem should I use?

Use `ω_kstar_omegaPow_eq_omegaPow`, which states:
`(KStar.kstar l)^ω = l^ω`
This shows `(L*)^omega = L^omega`, so in particular `L^omega ⊆ (L*)^omega` (they are equal).
Based on: ProvenTheorem `ω_kstar_omegaPow_eq_omegaPow` (lines 120-122).

---

## Module 8: Stlc.Safety

**Q1:** Does this module prove the progress theorem for STLC? If yes, what is it called?

Yes. The theorem is called `Stlc.FullBeta.progress`. It states:
`Stlc.Typing [] t τ → t.Value ∨ ∃ t', t.FullBeta t'`
Based on: ProvenTheorem `Stlc.FullBeta.progress` (lines 25-28).

**Q2:** What is the exact type signature of the preservation theorem?

```
∀ {Var : Type u_1} {Base : Type u_2} [HasFresh Var] [DecidableEq Var]
  {Γ : Context Var (Stlc.Ty Base)}
  {t : Untyped.Term Var} {τ : Stlc.Ty Base}
  {t' : Untyped.Term Var},
  Stlc.Typing Γ t τ → t.FullBeta t' → Stlc.Typing Γ t' τ
```
Based on: ProvenTheorem `Stlc.FullBeta.preservation` (lines 17-22).

**Q3:** I want to show that a well-typed closed STLC term either is a value or can take a step. Which theorem do I use?

Use `Stlc.FullBeta.progress`:
`Stlc.Typing [] t τ → t.Value ∨ ∃ t', t.FullBeta t'`
Provide a proof that the term is well-typed under the empty context (`[]`), and the theorem gives you that it is either a value or can step.
Based on: ProvenTheorem `Stlc.FullBeta.progress` (lines 25-28).

---

## Module 9: HML.Basic

**Q1:** Does this module prove that HML theory equivalence equals bisimilarity? If yes, what is it called?

Yes. The theorem is called `theoryEq_eq_bisimilarity`. It states:
`TheoryEq lts = lts.HomBisimilarity`
(for image-finite LTSs).
Based on: ProvenTheorem `theoryEq_eq_bisimilarity` (lines 100-103).

**Q2:** What is the exact type signature of the modal characterization theorem?

```
∀ {State : Type u_1} {Label : Type u_2} (lts : Cslib.LTS State Label)
  [image_finite : ∀ (s : State) (μ : Label), Finite ↑(lts.image s μ)],
  TheoryEq lts = lts.HomBisimilarity
```
Based on: ProvenTheorem `theoryEq_eq_bisimilarity` (lines 100-103).

**Q3:** I want to show two states satisfy the same HML formulas. What do I need to show first?

You need to show that the two states are bisimilar (related by a bisimulation). Then use `bisimulation_TheoryEq`:
`lts.IsHomBisimulation r → r s1 s2 → TheoryEq lts s1 s2`
This shows that bisimulation-related states are theory-equivalent, meaning they satisfy exactly the same HML formulas.
Based on: ProvenTheorem `bisimulation_TheoryEq` (lines 92-96).

---

## Module 10: RegularLanguage

**Q1:** Does this module prove that regular languages are closed under complement? If yes, what is it called?

Yes. The theorem is called `reg_compl`. It states:
`l.IsRegular → lᶜ.IsRegular`
Based on: ProvenTheorem `reg_compl` (lines 40-42).

**Q2:** What is the type signature of the theorem relating DFA acceptance to regular languages?

```
∀ {Symbol : Type u_1} {l : Language Symbol},
  l.IsRegular ↔ ∃ State : Type, ∃ (_ : Finite State),
    ∃ dfa : Cslib.Automata.DA.FinAcc State Symbol,
      Cslib.Automata.Acceptor.language dfa = l
```
Based on: ProvenTheorem `reg_iff_dfa` (lines 28-32).

**Q3:** I want to show the intersection of two regular languages is regular. Which theorem should I use?

Use `reg_inf`. It states:
`l1.IsRegular → l2.IsRegular → (l1 ⊓ l2).IsRegular`
(where `⊓` is intersection/infimum in the lattice of languages).
Based on: ProvenTheorem `reg_inf` (lines 53-55).
