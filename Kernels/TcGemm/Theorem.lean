-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Correct
public import Lemmas.Kernel.Existence

@[expose] public section

namespace PTX.Kernels.TcGemm
open PTX

section
variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0}

/-! ## Readings this result depends on

These results hold for the executions of the Core model (`Consistent`); besides the kernel
assumptions in the statement they rely on the following readings and obligations, each
documented beside its rule (see `Core/README.md`):

- EXT-ISA, EXT-IMPORT: `ptxas` and the hardware implement the PTX ISA; the Lean source is
  the compiled PTX.
- EXT-ADDR-WRAP (THREAD-ADDR): the `[reg+immOff]` address sum is taken modulo the address width
  (`2^64` global, `2^32` shared).
- EXT-LAUNCH, with its six launch obligations (no aliases, pointer state spaces, immutable tensor
  maps, Tensor Memory requested by co-resident CTAs, no conflicting outside access and no
  PDL-dependent launch, no multimem addresses): the launch description is the real one. No
  conflicting outside access: while the kernel runs, no other agent reads or writes the memory
  the kernel writes, and no other agent writes the memory it reads or that `Post` constrains.
- EXT-VECTOR-ELEM (THREAD-ACCESS): in the kernel's `ld`/`st` with `.v2`/`.v4`, element `j` is the
  scalar operation on the bytes at `base + j·size` and carries register `j` of the vector operand;
  the elements of one access are unordered among themselves (§8.2.4, MEM-PROGRAM-ORDER).
- EXT-FAIR (CORRECT-FAIR): `progress` and `terminates` are statements about
  the model; that a real run is a `FairRun` (fair scheduling, eventual completion of
  asynchronous operations) is taken from the CUDA programming guide, not from PTX, and is not
  proved here (the termination-transfer gap).
- EXT-CVTA (THREAD-MOVE): `cvta.to.global` of a global allocation's generic address is the same
  address.
- EXT-SHARED (PROG-DECODE): the kernel's `.shared` variables lie at the decoder's offsets from
  `Launch.sharedBase`.
- EXT-WARP (PROG-CTA-WARP): a warp is 32 consecutive threads of a CTA.
- EXT-BAR-PARTICIPANTS (ERR-BARRIER-MISMATCH): listed because the kernel has `bar.sync`; warps are
  compared at a barrier generation by barrier name and count, not by source position.
- EXT-OBJECT-ORDER (MEM-OBJECT-ORDER-CAUSALITY): the operations on one mbarrier and on one CTA
  barrier (CTA and barrier ID) are totally ordered consistently with causality, not derived from
  PTX.
- EXT-TMEM-ALLOC-ORDER (OBJ-TMEM-ORDER, DEP-TMEM-ALLOC-WAIT): the CTA's Tensor Memory
  allocator performs its requests in an order that contains causality, each before the issuing warp
  returns from the instruction.
- EXT-TMEM-ALLOC-RESULT-ORDER: an allocating warp's local result precedes its same-byte readback.
- EXT-TCALLOC-STORER (THREAD-TC): lane 0 of the allocating warp stores the allocated address with
  one generic-proxy weak store; fixing lane 0 and the generic proxy decides which reads are ordered
  after the store, and the kernel reads the address only after the whole allocating warp has
  synchronized, so it does not depend on which lane writes.
- EXT-TCFIG (THREAD-TC-MMA-RESULT-LAYOUT): the `cta_group::1` Layout D for M = 128, the `.32x32b`
  load map, given by figures and CUTLASS (the 8-bit K-major canonical shared layout follows the text
  of §9.7.18.3.3 and is not part of this reading).
- EXT-TCI8-WRAP (DEP-TC-MMA-VALUE): integer MMA accumulation wraps modulo 2^32.
- EXT-TMEM-LANE-FIELD (THREAD-TC-DATA-ADDRESS): the lane field of a `tcgen05.ld.32x32b` address is a
  lane of the issuing warp's chunk, as an offset into it or as an absolute lane; the kernel fills
  the absolute lane `32 w` in warp `w`, which reads lanes `32 w` to `32 w + 31`.
- EXT-ASYNC-OBJECT and EXT-ENABLES-OBJECT (MEM-OBJECT-ORDER-CAUSALITY): an asynchronous update
  (bulk-copy complete-tx, MMA commit arrive-on) follows its issue in its object's order, not derived
  from PTX; the enabling order also places the MMA's completion before the CTA's exit
  (ERR-SHARED-LIFETIME).
- EXT-STAGE-ORDER (MEM-OBJECT-ORDER-CAUSALITY): an operation's issue precedes its completion, the
  operand reads of a tracked MMA precede its completion, and the participating warps of a Tensor
  Memory allocation-management operation precede its blocking return, not derived from PTX.
- EXT-TCACQUIRE (DEP-TC-COMPLETION): an acquire wait orders later `tcgen05` operations without
  `tcgen05.fence::after_thread_sync`.
- EXT-TC-SOURCE-REUSE: an acquire that observes the completion of an MMA orders its shared
  operand read before a later ordinary overwrite of the same byte in the acquiring thread.
- EXT-TC-COMMIT-OPERAND-ORDER: an observed MMA commit carries prior shared operand writes to
  the observer's later accesses to those bytes.
- EXT-ENDIAN (MEM-BYTE): multi-byte values are stored little-endian, low byte first; the
  memory bytes `Pre` and `Post` describe are read in this order.
- EXT-TC-EXEC-ORDER (DEP-TC-FENCE): a `tcgen05.fence::before_thread_sync`, one mbarrier or
  barrier synchronization and a `tcgen05.fence::after_thread_sync` order the tcgen05 operations
  around them.
- EXT-TCFIG (THREAD-TC-SHARED-ADDRESS): listed because the kernel issues MMAs with shared-memory
  descriptors, whose swizzling mode is runtime data; it affects an operand only when its descriptor
  selects the 32-byte-atomic mode. -/

/-- **Main theorem.** For every one-CTA launch of 128 threads and launch memory satisfying
`Pre`, under no kernel assumptions: no possible execution has undefined behaviour (in
particular the Tensor Memory is allocated once, every MMA operand byte is the bulk-copied
input, every loaded cell is the MMA's result, and the deallocation follows every access);
every execution that cannot grow has every thread exited and all issued asynchronous work
completed (operand copies and MMA finish, their notifications occur, and waits can then
succeed); the counted events are bounded; and after a complete
execution `D = A * B` as 32-bit integers, with the rest of global memory unchanged. -/
theorem correct (hpre : Pre L A B D a b mem0) : Correct kernel [] L mem0 (Post D a b mem0) :=
  Proof.correct hpre

/-- The correctness theorem is non-vacuous: its model admits a completed execution. -/
theorem completed_execution (hpre : Pre L A B D a b mem0) :
    ∃ X, Consistent L kernel [] mem0 X ∧ Complete L X :=
  (correct hpre).complete_exists (Proof.valid hpre) (by simp )

/-- A completed execution and output satisfying this kernel's postcondition exist. -/
theorem realizable_result (hpre : Pre L A B D a b mem0) :
    ∃ X mf, Consistent L kernel [] mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post D a b mem0 mf :=
  (correct hpre).output_exists (Proof.valid hpre) (by simp )

end

end PTX.Kernels.TcGemm
