import CslibHeaders.Basic
import CslibHeaders.Computability.Defs.Automata.NA.Loop
import CslibHeaders.Computability.Proofs.Automata.NA.Loop

/-! # Loop Construction on Nondeterministic Automata

  Vocabulary:
    FinAcc.loop    -- the loop construction (Buchi ω-power)
    FinAcc.finLoop -- the loop construction for finite words (Kleene star)

  Theorems:
    loop_run_one_iter          -- a run with a non-initial () decomposes into one iteration + tail
    buchi_loop_language_eq     -- Buchi language of na.loop = (language na)^ω
    finAcc_loop_language_eq    -- FinAcc language of na.finLoop = (language na)*
-/

open Cslib.Automata.NA Cslib.Automata

ProvenTheorem loop_run_one_iter :
  ∀ {Symbol : Type u_1} {State : Type u_2}
    {na : Cslib.Automata.NA.FinAcc State Symbol}
    {xs : Cslib.ωSequence Symbol}
    {ss : Cslib.ωSequence (Unit ⊕ State)} {k : ℕ},
    na.loop.Run xs ss →
      0 < k →
        (ss k).isLeft = true →
          ∃ n, n ≤ k ∧
            Cslib.ωSequence.take n xs ∈ Acceptor.language na - 1 ∧
              na.loop.Run (Cslib.ωSequence.drop n xs) (Cslib.ωSequence.drop n ss)

ProvenTheorem buchi_loop_language_eq :
  ∀ {Symbol : Type u_1} {State : Type u_2}
    {na : Cslib.Automata.NA.FinAcc State Symbol}
    [_inst : Inhabited Symbol],
    ωAcceptor.language (NA.Buchi.mk na.loop {Sum.inl ()}) =
      (Acceptor.language na)^ω

ProvenTheorem finAcc_loop_language_eq :
  ∀ {Symbol : Type u_1} {State : Type u_2}
    {na : Cslib.Automata.NA.FinAcc State Symbol}
    [_inst : Inhabited Symbol],
    ¬Acceptor.language na = 0 →
      Acceptor.language (NA.FinAcc.mk na.finLoop {Sum.inl ()}) =
        KStar.kstar (Acceptor.language na)
