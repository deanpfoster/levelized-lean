import DeanLean.Basic

/-! # C++ happens-before memory model (N4950 §33)

  Formalizes the reasoning principles for concurrent programs:
  - Events with thread IDs and sequence numbers
  - SequencedBefore: intra-thread total order
  - SynchronizesWith: cross-thread synchronization edges
  - HappensBefore: transitive closure of the union
  - Data race detection: conflicting unordered events

  This is ABSTRACT — we model *relations between events* and prove
  properties of those relations. No actual memory or values.
-/

namespace Cpp.Concurrency

/-! ## Layer 1: Events and basic relations -/

/-- A memory event in a concurrent execution.
    Identified by its thread and position within that thread.
    C++ §6.9.2.2: "An expression evaluation ... in a thread of execution." -/
structure Event where
  threadId : Nat
  seqNo    : Nat
deriving Repr, BEq, DecidableEq, Inhabited

/-- An execution provides the relations between events.
    This is a record of axioms that a particular execution satisfies.
    - sequencedBefore: intra-thread total order (§6.9.1/10)
    - synchronizesWith: cross-thread synchronization (§33.4.4)
    We parameterize proofs over an arbitrary execution. -/
structure Execution where
  /-- The events in this execution -/
  events : List Event
  /-- Sequenced-before: total order within each thread (§6.9.1) -/
  sequencedBefore : Event → Event → Prop
  /-- Synchronizes-with: cross-thread synchronization (§33.4.4) -/
  synchronizesWith : Event → Event → Prop
  /-- sequencedBefore only relates events on the same thread -/
  sb_same_thread : ∀ (e1 e2 : Event),
    sequencedBefore e1 e2 → e1.threadId = e2.threadId
  /-- sequencedBefore is irreflexive -/
  sb_irrefl : ∀ (e : Event), ¬ sequencedBefore e e
  /-- sequencedBefore is transitive -/
  sb_trans : ∀ (e1 e2 e3 : Event),
    sequencedBefore e1 e2 → sequencedBefore e2 e3 → sequencedBefore e1 e3
  /-- synchronizesWith only relates events on different threads -/
  sw_diff_thread : ∀ (e1 e2 : Event),
    synchronizesWith e1 e2 → e1.threadId ≠ e2.threadId
  /-- synchronizesWith is irreflexive (follows from sw_diff_thread) -/
  sw_irrefl : ∀ (e : Event), ¬ synchronizesWith e e

/-- Happens-before: transitive closure of (sequencedBefore ∪ synchronizesWith).
    C++ §6.9.2.2: "An evaluation A happens before an evaluation B if
    A is sequenced before B, or A inter-thread happens before B." -/
inductive HappensBefore (exec : Execution) : Event → Event → Prop where
  /-- sequencedBefore ⊆ happensBefore -/
  | sb {e1 e2 : Event} : exec.sequencedBefore e1 e2 → HappensBefore exec e1 e2
  /-- synchronizesWith ⊆ happensBefore -/
  | sw {e1 e2 : Event} : exec.synchronizesWith e1 e2 → HappensBefore exec e1 e2
  /-- transitivity -/
  | trans {e1 e2 e3 : Event} : HappensBefore exec e1 e2 → HappensBefore exec e2 e3 →
            HappensBefore exec e1 e3

/-! ## Layer 2: Properties of HappensBefore

  Key insight: we CANNOT prove irreflexivity of HappensBefore in general —
  an execution with a synchronizesWith cycle would violate it. Instead,
  we define well-formed executions (acyclic) and prove properties for those. -/

/-- An execution is well-formed if its happens-before relation is acyclic.
    C++ §6.9.2.2 footnote: implementations must ensure no happens-before cycles. -/
def Execution.wellFormed (exec : Execution) : Prop :=
  ∀ (e : Event), ¬ HappensBefore exec e e

/-- HappensBefore is transitive by construction. Extract it as a standalone theorem. -/
theorem hb_trans {exec : Execution} {e1 e2 e3 : Event}
    (h12 : HappensBefore exec e1 e2) (h23 : HappensBefore exec e2 e3) :
    HappensBefore exec e1 e3 :=
  HappensBefore.trans h12 h23

/-- SequencedBefore implies HappensBefore. -/
theorem sb_implies_hb {exec : Execution} {e1 e2 : Event}
    (h : exec.sequencedBefore e1 e2) : HappensBefore exec e1 e2 :=
  HappensBefore.sb h

/-- SynchronizesWith implies HappensBefore. -/
theorem sw_implies_hb {exec : Execution} {e1 e2 : Event}
    (h : exec.synchronizesWith e1 e2) : HappensBefore exec e1 e2 :=
  HappensBefore.sw h

/-- In a well-formed execution, HappensBefore is irreflexive. -/
theorem hb_irrefl {exec : Execution} (wf : exec.wellFormed) (e : Event) :
    ¬ HappensBefore exec e e :=
  wf e

/-- In a well-formed execution, HappensBefore is asymmetric. -/
theorem hb_asymm {exec : Execution} (wf : exec.wellFormed) {e1 e2 : Event}
    (h : HappensBefore exec e1 e2) : ¬ HappensBefore exec e2 e1 := by
  intro h'
  exact wf e1 (hb_trans h h')

/-! ## Layer 3: Data race detection -/

/-- The kind of memory access. -/
inductive AccessKind where
  | read
  | write
deriving Repr, BEq, DecidableEq, Inhabited

/-- A memory access: an event accessing a particular location with a particular kind. -/
structure MemoryAccess where
  event    : Event
  location : Nat
  kind     : AccessKind
deriving Repr, BEq, DecidableEq

/-- Two accesses conflict if they access the same location and at least one is a write.
    C++ §6.9.2.2: "Two expression evaluations conflict if one of them modifies
    a memory location and the other ... accesses or modifies the same memory location." -/
def conflict (a1 a2 : MemoryAccess) : Prop :=
  a1.location = a2.location ∧
  (a1.kind = .write ∨ a2.kind = .write) ∧
  a1.event ≠ a2.event

/-- A data race exists between two accesses if they conflict and neither
    happens-before the other.
    C++ §6.9.2.2: "... two potentially concurrent actions ... conflict,
    at least one of which is not atomic, ... the program has a data race." -/
def DataRace (exec : Execution) (a1 a2 : MemoryAccess) : Prop :=
  conflict a1 a2 ∧
  ¬ HappensBefore exec a1.event a2.event ∧
  ¬ HappensBefore exec a2.event a1.event

/-- An execution is race-free if no pair of accesses has a data race.
    C++ §6.9.2.2: "A program ... shall not have data races." -/
def RaceFree (exec : Execution) (accesses : List MemoryAccess) : Prop :=
  ∀ (a1 a2 : MemoryAccess), a1 ∈ accesses → a2 ∈ accesses →
    ¬ DataRace exec a1 a2

/-- All accesses are on a single thread. -/
def SingleThreaded (accesses : List MemoryAccess) : Prop :=
  ∀ (a1 a2 : MemoryAccess), a1 ∈ accesses → a2 ∈ accesses →
    a1.event.threadId = a2.event.threadId

/-- Within a thread, sequencedBefore provides a total order:
    for any two distinct events on the same thread, one is sequenced before the other. -/
def Execution.sbTotal (exec : Execution) : Prop :=
  ∀ (e1 e2 : Event), e1.threadId = e2.threadId → e1 ≠ e2 →
    exec.sequencedBefore e1 e2 ∨ exec.sequencedBefore e2 e1

/-! ## Layer 4: Memory orders (stretch) -/

/-- C++ memory orderings (§33.4.1) -/
inductive MemoryOrder where
  | relaxed
  | acquire
  | release
  | acq_rel
  | seq_cst
deriving Repr, BEq, DecidableEq, Inhabited

/-- A memory operation with its ordering. -/
structure AtomicOp where
  access : MemoryAccess
  order  : MemoryOrder
deriving Repr, BEq

/-- A release store synchronizes-with an acquire load that reads the stored value.
    C++ §33.4.4: "An atomic operation A that is a release operation on an atomic object M
    synchronizes with an atomic operation B that is an acquire operation on M
    and takes its value from any side effect in the release sequence headed by A." -/
def releaseAcquireSync (store load : AtomicOp) : Prop :=
  store.access.location = load.access.location ∧
  store.access.kind = .write ∧
  load.access.kind = .read ∧
  (store.order = .release ∨ store.order = .acq_rel ∨ store.order = .seq_cst) ∧
  (load.order = .acquire ∨ load.order = .acq_rel ∨ load.order = .seq_cst) ∧
  store.access.event.threadId ≠ load.access.event.threadId

/-! ## Layer 5: Concurrency patterns -/

/-- The message-passing pattern:
    Thread 1 writes data (w), then release-stores a flag (s).
    Thread 2 acquire-loads the flag (l), then reads data (r).
    The store synchronizes-with the load.

    This captures the classic idiom:
      Thread 1: data = 42; flag.store(1, release);
      Thread 2: while (!flag.load(acquire)); use(data);
-/
structure MessagePassingPattern (exec : Execution) where
  /-- The data write event (thread 1) -/
  dataWrite : Event
  /-- The release store of the flag (thread 1) -/
  flagStore : Event
  /-- The acquire load of the flag (thread 2) -/
  flagLoad  : Event
  /-- The data read event (thread 2) -/
  dataRead  : Event
  /-- The data write is sequenced-before the flag store -/
  sb_write_store : exec.sequencedBefore dataWrite flagStore
  /-- The flag store synchronizes-with the flag load -/
  sw_store_load  : exec.synchronizesWith flagStore flagLoad
  /-- The flag load is sequenced-before the data read -/
  sb_load_read   : exec.sequencedBefore flagLoad dataRead
  /-- The data write and read access the same location -/
  same_location  : Nat

/-- The data write as a MemoryAccess. -/
def MessagePassingPattern.dataWriteAccess {exec : Execution}
    (mp : MessagePassingPattern exec) : MemoryAccess :=
  ⟨mp.dataWrite, mp.same_location, .write⟩

/-- The data read as a MemoryAccess. -/
def MessagePassingPattern.dataReadAccess {exec : Execution}
    (mp : MessagePassingPattern exec) : MemoryAccess :=
  ⟨mp.dataRead, mp.same_location, .read⟩

/-- A mutex execution with two critical sections:
    Thread 1: lock₁ (acquire), work₁, unlock₁ (release)
    Thread 2: lock₂ (acquire from unlock₁), work₂, unlock₂ (release)

    The unlock₁ synchronizes-with lock₂, ordering the two critical sections.
-/
structure MutexExecution (exec : Execution) where
  /-- Thread 1's lock (acquire) -/
  lock₁   : Event
  /-- Thread 1's work event -/
  work₁   : Event
  /-- Thread 1's unlock (release) -/
  unlock₁ : Event
  /-- Thread 2's lock (acquire from unlock₁) -/
  lock₂   : Event
  /-- Thread 2's work event -/
  work₂   : Event
  /-- Thread 2's unlock (release) -/
  unlock₂ : Event
  /-- lock₁ is sequenced-before work₁ -/
  sb_lock₁_work₁     : exec.sequencedBefore lock₁ work₁
  /-- work₁ is sequenced-before unlock₁ -/
  sb_work₁_unlock₁   : exec.sequencedBefore work₁ unlock₁
  /-- unlock₁ synchronizes-with lock₂ -/
  sw_unlock₁_lock₂   : exec.synchronizesWith unlock₁ lock₂
  /-- lock₂ is sequenced-before work₂ -/
  sb_lock₂_work₂     : exec.sequencedBefore lock₂ work₂
  /-- work₂ is sequenced-before unlock₂ -/
  sb_work₂_unlock₂   : exec.sequencedBefore work₂ unlock₂

end Cpp.Concurrency
