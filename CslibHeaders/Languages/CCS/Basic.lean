import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.CCS.Basic
import CslibHeaders.Proofs.Languages.CCS.Basic

/-! # CCS Basic -- Syntax of the Calculus of Communicating Systems

  Vocabulary:
    Act Name          -- actions: name, coname, or tau
    Process Name Constant -- CCS processes
    Context Name Constant -- syntactic contexts with a hole
    Context.fill      -- fill a context's hole with a process
    Act.IsVisible     -- an action is a name or coname (not tau)
    Act.Co            -- two actions are coactions
    Act.isCo          -- Boolean coaction check

  Read this file for WHAT is true.
  Read Defs/ for WHAT the words mean.
  Never need to open Code or Proofs.
-/

open Cslib.CCS

-- If an action is visible, it is not tau.
ProvenTheorem isVisible_neq_τ :
  ∀ {Name : Type u_1} {μ : Act Name}, μ.IsVisible → μ ≠ Act.τ

-- Act.Co is symmetric.
ProvenTheorem Co.symm :
  ∀ {Name : Type u_1} {μ μ' : Act Name}, μ.Co μ' → μ'.Co μ

-- If two actions are coactions, both are visible.
ProvenTheorem co_isVisible :
  ∀ {Name : Type u_1} {μ μ' : Act Name}, μ.Co μ' → μ.IsVisible ∧ μ'.IsVisible

-- Boolean isCo agrees with propositional Co.
ProvenTheorem isCo_iff :
  ∀ {Name : Type u_1} [DecidableEq Name] {μ μ' : Act Name},
    μ.isCo μ' = true ↔ μ.Co μ'

-- Definition of context filling.
ProvenTheorem context_fill_def :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    (c : Context Name Constant) (p : Process Name Constant),
    (c<[p] : Process Name Constant) = c.fill p

-- Any process equals some context filled with an atom (nil or constant).
ProvenTheorem Context.complete :
  ∀ {Name : Type u_1} {Constant : Type u_2}
    (p : Process Name Constant),
    ∃ c : Context Name Constant,
      p = c.fill Process.nil ∨ ∃ k, p = c.fill (Process.const k)
