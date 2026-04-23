import CslibHeaders.Basic
import CslibHeaders.Defs.Languages.LambdaCalculus.LocallyNameless.Context
import CslibHeaders.Proofs.Languages.LambdaCalculus.LocallyNameless.Context

/-! # Typing Contexts for the Locally Nameless Lambda Calculus

  Vocabulary:
    Context    -- list of (variable, type) pairs
    dom        -- domain (finite set of variables)
    map_val    -- map a function over the types in a context

  Contexts support lookup via List.dlookup.
-/

open Cslib Cslib.LambdaCalculus.LocallyNameless

ProvenTheorem Context.map_val_keys :
  ∀ {α : Type u_1} {β : Type u_2} {Γ : Context α β} (f : β → β),
    Γ.keys = (Γ.map_val f).keys

ProvenTheorem Context.map_val_mem :
  ∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] {σ : β}
    {Γ : Context α β} {x : α} (mem : σ ∈ Γ.dlookup x) (f : β → β),
    f σ ∈ (Γ.map_val f).dlookup x
