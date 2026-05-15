import DeanLean.Basic
import DeanLean.Cpp.Code.Concurrency

/-! # Tests for C++ happens-before memory model (N4950 §33) -/

namespace Cpp.Concurrency.Tests

/-! ## Event construction tests -/

#eval do
  let e1 := Event.mk 0 0
  let e2 := Event.mk 0 1
  let e3 := Event.mk 1 0
  assert! e1.threadId == 0
  assert! e1.seqNo == 0
  assert! e2.threadId == 0
  assert! e2.seqNo == 1
  assert! e3.threadId == 1
  assert! e1 != e2  -- same thread, different seq
  assert! e1 != e3  -- different thread

#eval do
  -- Events on the same thread with different seqNo are distinct
  let e1 := Event.mk 42 0
  let e2 := Event.mk 42 1
  assert! e1 != e2
  assert! e1.threadId == e2.threadId

/-! ## AccessKind tests -/

#eval do
  assert! AccessKind.read != AccessKind.write
  assert! AccessKind.read == AccessKind.read
  assert! AccessKind.write == AccessKind.write

/-! ## MemoryAccess construction tests -/

#eval do
  let e := Event.mk 0 0
  let a1 := MemoryAccess.mk e 100 .read
  let a2 := MemoryAccess.mk e 100 .write
  assert! a1.location == a2.location
  assert! a1.kind == AccessKind.read
  assert! a2.kind == AccessKind.write

/-! ## MemoryOrder tests -/

#eval do
  assert! MemoryOrder.relaxed != MemoryOrder.acquire
  assert! MemoryOrder.acquire != MemoryOrder.release
  assert! MemoryOrder.release != MemoryOrder.acq_rel
  assert! MemoryOrder.acq_rel != MemoryOrder.seq_cst
  assert! MemoryOrder.seq_cst == MemoryOrder.seq_cst

/-! ## AtomicOp construction tests -/

#eval do
  let e := Event.mk 0 0
  let acc := MemoryAccess.mk e 42 .write
  let op := AtomicOp.mk acc .release
  assert! op.order == MemoryOrder.release
  assert! op.access.kind == AccessKind.write

/-! ## Scenario: two-thread message passing

  Thread 0: write x (e0_0), release store flag (e0_1)
  Thread 1: acquire load flag (e1_0), read x (e1_1)

  Expected happens-before chain:
    e0_0 ->sb e0_1 ->sw e1_0 ->sb e1_1
  So e0_0 happens-before e1_1, protecting the read of x. -/

#eval do
  let e0_0 := Event.mk 0 0  -- write x
  let e0_1 := Event.mk 0 1  -- release store flag
  let e1_0 := Event.mk 1 0  -- acquire load flag
  let e1_1 := Event.mk 1 1  -- read x

  -- Verify events are on correct threads
  assert! e0_0.threadId == 0
  assert! e0_1.threadId == 0
  assert! e1_0.threadId == 1
  assert! e1_1.threadId == 1

  -- Verify sequencing within threads
  assert! e0_0.seqNo < e0_1.seqNo
  assert! e1_0.seqNo < e1_1.seqNo

  -- Cross-thread sync is between different threads
  assert! e0_1.threadId != e1_0.threadId

/-! ## Scenario: Message passing pattern structure -/

#eval do
  -- Verify the events used in a message-passing pattern
  let w := Event.mk 0 0   -- data write
  let s := Event.mk 0 1   -- release store flag
  let l := Event.mk 1 0   -- acquire load flag
  let r := Event.mk 1 1   -- data read

  -- Thread assignments are correct
  assert! w.threadId == 0
  assert! s.threadId == 0
  assert! l.threadId == 1
  assert! r.threadId == 1

  -- Sequencing within threads
  assert! w.seqNo < s.seqNo
  assert! l.seqNo < r.seqNo

  -- Cross-thread sync
  assert! s.threadId != l.threadId

/-! ## Scenario: Mutex with two critical sections -/

#eval do
  -- Thread 0: lock, work, unlock
  let lock1   := Event.mk 0 0
  let work1   := Event.mk 0 1
  let unlock1 := Event.mk 0 2
  -- Thread 1: lock, work, unlock
  let lock2   := Event.mk 1 0
  let work2   := Event.mk 1 1
  let unlock2 := Event.mk 1 2

  -- Thread assignments
  assert! lock1.threadId == 0
  assert! work1.threadId == 0
  assert! unlock1.threadId == 0
  assert! lock2.threadId == 1
  assert! work2.threadId == 1
  assert! unlock2.threadId == 1

  -- Sequencing
  assert! lock1.seqNo < work1.seqNo
  assert! work1.seqNo < unlock1.seqNo
  assert! lock2.seqNo < work2.seqNo
  assert! work2.seqNo < unlock2.seqNo

  -- Cross-thread sync between unlock1 and lock2
  assert! unlock1.threadId != lock2.threadId

end Cpp.Concurrency.Tests

/-! ## Named test defs for TestedConjectures -/

namespace Cpp.Concurrency

Test event_equality :=
  show Event.mk 0 0 = Event.mk 0 0 from rfl

Test event_seqno_matters :=
  show (Event.mk 0 0 == Event.mk 0 1) = false from rfl

Test event_thread_matters :=
  show (Event.mk 0 0 == Event.mk 1 0) = false from rfl

Test accessKind_read_neq_write :=
  show (AccessKind.read == AccessKind.write) = false from rfl

Test memoryOrder_values_distinct :=
  show (MemoryOrder.relaxed == MemoryOrder.acquire) = false from rfl

Test read_access_has_read_kind :=
  show (MemoryAccess.mk (Event.mk 0 0) 42 .read).kind = .read from rfl

Test write_access_has_write_kind :=
  show (MemoryAccess.mk (Event.mk 0 0) 42 .write).kind = .write from rfl

end Cpp.Concurrency
