# Physical Design for Lean 4: Breaking the Elaboration Bottleneck

**To:** Leo de Moura & the Lean Core Team  
**Subject:** Resolving Serial Build Cascades via Signature-Based Incremental Compilation

## 1. The Core Problem: Physical Coupling in the Module System

Lean 4’s new module scopes provide excellent control over logical visibility and namespaces. However, the build infrastructure (Lake/Elan) currently suffers from a critical limitation in its physical design: **the coupling of logical truth to physical compilation artifacts.**

Currently, a Lean module (`.olean`) is the atomic unit of dependency. If module `A` contains both a public definition and a heavy, private proof, and module `B` imports `A`, any modification to the proof in `A` alters the `A.olean` export hash. 

Even if the public interface of `A` remains bit-for-bit identical, Lake’s hash-based dependency tracking detects a change and triggers a full re-elaboration of `B`. In massive codebases like Mathlib, or in deep $N$-level dependency chains, this results in a monolithic, serial recompilation cascade. Cloud caching (`lake exe cache`) treats the symptom but does not solve the underlying architectural bottleneck.

## 2. The Solution: Signature-Based Incremental Compilation

To unlock true scalability for Lean 4, we must decouple the *Interface* (the "what") from the *Implementation* (the "how"). We propose integrating **Signature-Based Incremental Compilation** (or Semantic Hashing) natively into the Elaboration and Build pipeline.

By allowing the compiler to distinguish between a change in a theorem's signature and a change in its proof body, we can halt the recompilation cascade at the exact point of mutation.

### The Prototype Architecture ("Levelized Lean")
We have prototyped this methodology externally by manually enforcing an Interface-Implementation split:
1. **Signature Proxies (`M_Interface.lean`):** Contains only `Prop` signatures and definitions (using `opaque` or `axiom` as placeholders).
2. **Implementations (`M_Proof.lean`):** Imports the Interface and provides the actual proofs (e.g., via `attribute [implementation]`).
3. **Strict Downstream Linking:** All downstream modules are restricted to importing *only* the Interface module.

To handle logical cycles (mutual recursion), we employ a higher-order parameterization strategy, breaking the logical loop into an acyclic physical tree consisting of the Interface, parameterized implementations, and a higher-level knot-tying module.

## 3. The Wins for Lean 4

Implementing this physical design natively within Lake and the Lean compiler yields three transformative benefits:

### A. Massive Non-Monotonic Parallelization
Under the current paradigm, verifying a 98-level deep proof chain is an $O(N)$ serial operation. With isolated interfaces, it becomes an $O(1)$ parallel operation. 
If an interface contract is established, 98 separate CPU cores can simultaneously verify all 98 levels in isolation. Core $N$ assumes the interface of $N-1$ is true, checks its local proof, and reports back. The build system simply verifies that all interface contracts were satisfied at the end.

### B. Zero-Cost Proof Refactoring
A developer can refactor a massive, heavily-depended-upon proof in a low-level Mathlib file without triggering a downstream cascade. If the semantic hash of the declarations remains constant, Lake can intelligently skip re-elaborating the thousands of files that import it.

### C. Low-Latency AI Verification Pipelines
For AI-driven formal verification, latency is the primary bottleneck. LLM agents exploring proof spaces require instant feedback on type-correctness and interface validity. By utilizing a "Short-Circuit" switch (linking downstream modules to axiom-based interfaces during the exploration phase), AI agents can iterate on complex proofs in sub-second time, deferring the full Kernel proof-check to the final commit phase.

## 4. Proposal & Next Steps

The manual "Intrusive" levelization we are running at `lean4.ai` proves that O(1) parallel verification is possible today, but it requires heavy boilerplate. 

We propose collaborating to bring this to the core toolchain. The goal is a native capability where Lake can say: *"The source file changed, but the resulting semantic hash of its public declarations is identical; therefore, downstream dependents are still valid."*

This evolution from logical encapsulation to physical decoupling is the key to scaling Lean 4 beyond its current limits.
