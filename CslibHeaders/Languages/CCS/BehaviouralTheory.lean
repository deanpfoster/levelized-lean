import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.CCS.Basic
import CslibHeaders.Defs.Languages.CCS.Semantics
import CslibHeaders.Defs.Languages.CCS.BehaviouralTheory
import CslibHeaders.Proofs.Languages.CCS.BehaviouralTheory

/-! # CCS Behavioural Theory -- Bisimilarity Laws and Congruence

  Vocabulary:
    lts           -- the LTS of CCS
    Congruence    -- bisimilarity is a congruence

  Laws of bisimilarity (~):
    P | nil ~ P               (bisimilarity_par_nil)
    nil | P ~ P               (bisimilarity_nil_par)
    P | Q ~ Q | P             (bisimilarity_par_comm)
    P | (Q | R) ~ (P|Q) | R  (bisimilarity_par_assoc)
    P + nil ~ P               (bisimilarity_choice_nil)
    P + P ~ P                 (bisimilarity_choice_idem)
    P + Q ~ Q + P             (bisimilarity_choice_comm)
    P + (Q + R) ~ (P+Q) + R  (bisimilarity_choice_assoc)

  Congruence laws:
    P ~ Q -> mu.P ~ mu.Q     (bisimilarity_congr_pre)
    P ~ Q -> (v a)P ~ (v a)Q (bisimilarity_congr_res)
    P ~ Q -> P + R ~ Q + R   (bisimilarity_congr_choice)
    P ~ Q -> P | R ~ Q | R   (bisimilarity_congr_par)
    P ~ Q -> C[P] ~ C[Q]     (bisimilarity_is_congruence)

  Read this file for WHAT is true.
  Read Defs/ for WHAT the words mean.
  Never need to open Code or Proofs.
-/

open Cslib Cslib.CCS Cslib.LTS

-- P | nil ~ P
ProvenTheorem bisimilarity_par_nil :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    {defs : Constant → Process Name Constant → Prop}
    {p : Process Name Constant},
    (lts (defs := defs)).HomBisimilarity (p.par Process.nil) p

-- P | Q ~ Q | P
ProvenTheorem bisimilarity_par_comm :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    {defs : Constant → Process Name Constant → Prop}
    {p q : Process Name Constant},
    (lts (defs := defs)).HomBisimilarity (p.par q) (q.par p)

-- nil | P ~ P
ProvenTheorem bisimilarity_nil_par :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    {defs : Constant → Process Name Constant → Prop}
    {p : Process Name Constant},
    (lts (defs := defs)).HomBisimilarity (Process.nil.par p) p

-- P | (Q | R) ~ (P | Q) | R
ProvenTheorem bisimilarity_par_assoc :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    {defs : Constant → Process Name Constant → Prop}
    {p q r : Process Name Constant},
    (lts (defs := defs)).HomBisimilarity (p.par (q.par r)) ((p.par q).par r)

-- P + nil ~ P
ProvenTheorem bisimilarity_choice_nil :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    {defs : Constant → Process Name Constant → Prop}
    {p : Process Name Constant},
    (lts (defs := defs)).HomBisimilarity (p.choice Process.nil) p

-- P + P ~ P
ProvenTheorem bisimilarity_choice_idem :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    {defs : Constant → Process Name Constant → Prop}
    {p : Process Name Constant},
    (lts (defs := defs)).HomBisimilarity (p.choice p) p

-- P + Q ~ Q + P
ProvenTheorem bisimilarity_choice_comm :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    {defs : Constant → Process Name Constant → Prop}
    {p q : Process Name Constant},
    (lts (defs := defs)).HomBisimilarity (p.choice q) (q.choice p)

-- P + (Q + R) ~ (P + Q) + R
ProvenTheorem bisimilarity_choice_assoc :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    {defs : Constant → Process Name Constant → Prop}
    {p q r : Process Name Constant},
    (lts (defs := defs)).HomBisimilarity (p.choice (q.choice r)) ((p.choice q).choice r)

-- P ~ Q -> mu.P ~ mu.Q
ProvenTheorem bisimilarity_congr_pre :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    {defs : Constant → Process Name Constant → Prop}
    {p q : Process Name Constant} {μ : Act Name},
    (lts (defs := defs)).HomBisimilarity p q →
      (lts (defs := defs)).HomBisimilarity (Process.pre μ p) (Process.pre μ q)

-- P ~ Q -> (v a)P ~ (v a)Q
ProvenTheorem bisimilarity_congr_res :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    {defs : Constant → Process Name Constant → Prop}
    {p q : Process Name Constant} {a : Name},
    (lts (defs := defs)).HomBisimilarity p q →
      (lts (defs := defs)).HomBisimilarity (Process.res a p) (Process.res a q)

-- P ~ Q -> P + R ~ Q + R
ProvenTheorem bisimilarity_congr_choice :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    {defs : Constant → Process Name Constant → Prop}
    {p q r : Process Name Constant},
    (lts (defs := defs)).HomBisimilarity p q →
      (lts (defs := defs)).HomBisimilarity (p.choice r) (q.choice r)

-- P ~ Q -> P | R ~ Q | R
ProvenTheorem bisimilarity_congr_par :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    {defs : Constant → Process Name Constant → Prop}
    {p q r : Process Name Constant},
    (lts (defs := defs)).HomBisimilarity p q →
      (lts (defs := defs)).HomBisimilarity (p.par r) (q.par r)

-- P ~ Q -> C[P] ~ C[Q]
ProvenTheorem bisimilarity_is_congruence :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    {defs : Constant → Process Name Constant → Prop}
    (p q : Process Name Constant) (c : Context Name Constant),
    (lts (defs := defs)).HomBisimilarity p q →
      (lts (defs := defs)).HomBisimilarity (c.fill p) (c.fill q)
