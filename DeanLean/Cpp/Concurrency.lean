import DeanLean.Cpp.Defs.Concurrency
import DeanLean.Cpp.Proofs.Concurrency
import DeanLean.Cpp.Tests.Concurrency

/-! # C++ happens-before memory model (N4950 §33)

  Formalizes the reasoning principles for concurrent programs using
  partial orders over memory events. Rather than modeling thread
  interleavings (exponential), we model *constraints on event visibility*.

  The happens-before relation is a partial order over memory events.
  Acquire/release semantics add synchronization edges.

  ## Layer 1: Events and relations

  structure Event — threadId : Nat, seqNo : Nat
  structure Execution — events, sequencedBefore, synchronizesWith + axioms
  inductive HappensBefore — transitive closure of (sb ∪ sw)

  ## Layer 2: Properties (proven)

  - HappensBefore is transitive (by construction)
  - HappensBefore is irreflexive in well-formed executions
  - HappensBefore is asymmetric in well-formed executions
  - SequencedBefore ⊆ HappensBefore
  - SynchronizesWith ⊆ HappensBefore
  - Composites: sb;sb, sb;sw, sw;sb all yield hb

  ## Layer 3: Data race detection (proven)

  - conflict: same location, at least one write, distinct events
  - DataRace: conflict ∧ ¬hb in either direction
  - RaceFree: no data races in a list of accesses
  - THEOREM: single-threaded execution with total sb is race-free
  - Two reads never race

  ## Layer 4: Memory orders (definitions)

  - MemoryOrder: relaxed, acquire, release, acq_rel, seq_cst
  - AtomicOp: access + memory order
  - releaseAcquireSync: release store → acquire load specification

  ## Layer 5: Concurrency patterns (proven)

  - acquire_release_guarantee: sb;sw;sb chain yields hb
  - MessagePassingPattern: data write, release store, acquire load, data read
  - message_passing_is_race_free: message passing has no data race
  - MutexExecution: two critical sections on the same mutex
  - mutex_critical_sections_ordered: CS₁ happens-before CS₂
-/

namespace Cpp.Concurrency

/-! ## Type signatures -/

-- Events
-- (Event is a structure, not a function — no Signature needed)

/-! ## Proven theorems: HappensBefore properties -/

ProvenTheorem hb_transitivity :
    ∀ {exec : Execution} {e1 e2 e3 : Event},
    HappensBefore exec e1 e2 → HappensBefore exec e2 e3 →
    HappensBefore exec e1 e3

ProvenTheorem sb_in_hb :
    ∀ {exec : Execution} {e1 e2 : Event},
    exec.sequencedBefore e1 e2 → HappensBefore exec e1 e2

ProvenTheorem sw_in_hb :
    ∀ {exec : Execution} {e1 e2 : Event},
    exec.synchronizesWith e1 e2 → HappensBefore exec e1 e2

ProvenTheorem hb_is_irreflexive :
    ∀ {exec : Execution},
    exec.wellFormed → ∀ (e : Event), ¬ HappensBefore exec e e

ProvenTheorem hb_is_asymmetric :
    ∀ {exec : Execution},
    exec.wellFormed → ∀ {e1 e2 : Event},
    HappensBefore exec e1 e2 → ¬ HappensBefore exec e2 e1

ProvenTheorem sb_sb_yields_hb :
    ∀ {exec : Execution} {e1 e2 e3 : Event},
    exec.sequencedBefore e1 e2 → exec.sequencedBefore e2 e3 →
    HappensBefore exec e1 e3

ProvenTheorem sb_sw_yields_hb :
    ∀ {exec : Execution} {e1 e2 e3 : Event},
    exec.sequencedBefore e1 e2 → exec.synchronizesWith e2 e3 →
    HappensBefore exec e1 e3

ProvenTheorem sw_sb_yields_hb :
    ∀ {exec : Execution} {e1 e2 e3 : Event},
    exec.synchronizesWith e1 e2 → exec.sequencedBefore e2 e3 →
    HappensBefore exec e1 e3

/-! ## Proven theorems: Data race properties -/

ProvenTheorem conflict_is_symmetric :
    ∀ {a1 a2 : MemoryAccess},
    conflict a1 a2 → conflict a2 a1

ProvenTheorem dataRace_is_symmetric :
    ∀ {exec : Execution} {a1 a2 : MemoryAccess},
    DataRace exec a1 a2 → DataRace exec a2 a1

ProvenTheorem two_reads_no_conflict :
    ∀ {a1 a2 : MemoryAccess},
    a1.kind = .read → a2.kind = .read → ¬ conflict a1 a2

ProvenTheorem two_reads_no_race :
    ∀ {exec : Execution} {a1 a2 : MemoryAccess},
    a1.kind = .read → a2.kind = .read → ¬ DataRace exec a1 a2

ProvenTheorem hb_prevents_dataRace :
    ∀ {exec : Execution} {a1 a2 : MemoryAccess},
    HappensBefore exec a1.event a2.event → ¬ DataRace exec a1 a2

ProvenTheorem singleThread_is_raceFree :
    ∀ {exec : Execution} {accesses : List MemoryAccess},
    SingleThreaded accesses → exec.sbTotal →
    (∀ (a : MemoryAccess), a ∈ accesses → a.event ∈ exec.events) →
    RaceFree exec accesses

/-! ## Proven theorems: Execution axiom consequences -/

ProvenTheorem sb_is_irreflexive :
    ∀ {exec : Execution} (e : Event), ¬ exec.sequencedBefore e e

ProvenTheorem sb_preserves_thread :
    ∀ {exec : Execution} {e1 e2 : Event},
    exec.sequencedBefore e1 e2 → e1.threadId = e2.threadId

ProvenTheorem sw_crosses_threads :
    ∀ {exec : Execution} {e1 e2 : Event},
    exec.synchronizesWith e1 e2 → e1.threadId ≠ e2.threadId

/-! ## Proven theorems: Concurrency patterns -/

ProvenTheorem acquire_release_guarantee :
    ∀ {exec : Execution} {before_store store_event load_event after_load : Event},
    exec.sequencedBefore before_store store_event →
    exec.synchronizesWith store_event load_event →
    exec.sequencedBefore load_event after_load →
    HappensBefore exec before_store after_load

ProvenTheorem message_passing_data_ordered :
    ∀ {exec : Execution} (mp : MessagePassingPattern exec),
    HappensBefore exec mp.dataWrite mp.dataRead

ProvenTheorem message_passing_is_race_free :
    ∀ {exec : Execution} (mp : MessagePassingPattern exec),
    ¬ DataRace exec mp.dataWriteAccess mp.dataReadAccess

ProvenTheorem mutex_critical_sections_ordered :
    ∀ {exec : Execution} (mx : MutexExecution exec),
    HappensBefore exec mx.work₁ mx.work₂

ProvenTheorem mutex_lock_order :
    ∀ {exec : Execution} (mx : MutexExecution exec),
    HappensBefore exec mx.lock₁ mx.lock₂

/-! ## Tested conjectures -/

TestedConjecture event_equality :
    Event.mk 0 0 = Event.mk 0 0

TestedConjecture event_seqno_matters :
    (Event.mk 0 0 == Event.mk 0 1) = false

TestedConjecture event_thread_matters :
    (Event.mk 0 0 == Event.mk 1 0) = false

TestedConjecture accessKind_read_neq_write :
    (AccessKind.read == AccessKind.write) = false

TestedConjecture memoryOrder_values_distinct :
    (MemoryOrder.relaxed == MemoryOrder.acquire) = false

TestedConjecture read_access_has_read_kind :
    (MemoryAccess.mk (Event.mk 0 0) 42 .read).kind = .read

TestedConjecture write_access_has_write_kind :
    (MemoryAccess.mk (Event.mk 0 0) 42 .write).kind = .write

end Cpp.Concurrency
