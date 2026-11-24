-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Correct
public import Lemmas.Kernel.Existence

@[expose] public section

namespace PTX.Kernels.Fp16Gemm8192
open PTX
noncomputable section
local notation "Prod" => [Assumptions.idealArith, Assumptions.clusterMbar, Assumptions.pollAgree]

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
- EXT-CVTA (THREAD-MOVE): the generic address of a global allocation is its global address; the
  global bases of the tensor maps are the host pointers of the allocations (the kernel executes no
  `cvta.to.global`).
- EXT-SHARED (PROG-DECODE): the kernel's `.shared` variables lie at the decoder's offsets from
  `Launch.sharedBase`.
- EXT-WARP (PROG-CTA-WARP): a warp is 32 consecutive threads of a CTA.
- EXT-BAR-PARTICIPANTS (ERR-BARRIER-MISMATCH, ERR-SETMAXNREG): warps are compared at a barrier
  generation by barrier name and count, and at a warpgroup's `setmaxnreg` by direction and count,
  not by source position.
- EXT-ENDIAN (MEM-BYTE): multi-byte values and packed pairs are stored little-endian, low half
  first.
- EXT-OBJECT-ORDER (MEM-OBJECT-ORDER-CAUSALITY): the operations on one mbarrier, CTA barrier and
  cluster barrier of one CTA or cluster are totally ordered consistently with causality, not derived
  from PTX.
- EXT-TMEM-ALLOC-ORDER (OBJ-TMEM-ORDER, DEP-TMEM-ALLOC-WAIT): each CTA's Tensor Memory
  allocator performs that CTA's requests in an order that contains causality, and performs its CTA's
  half of a `cta_group::2` request before the issuing warp returns from the instruction, also when
  the warp does not wait for the peer CTA's warp. An allocation performed after such a deallocation
  half that the peer CTA's half does not causally precede is reported unsafe
  (`PendingReleaseAlloc`), so the result does not depend on when the half takes effect; the kernel
  allocates only before it deallocates.
- EXT-PAIR-ALLOC-ORDER (OBJ-TMEM-PUBLICATION): listed because the kernel's allocation is a
  paired `tcgen05.alloc.cta_group::2`: each CTA's allocation also covers the accesses that the
  peer warp's allocation happens before. Every access of the kernel is covered by its own CTA's
  allocation event; the reading adds records to the release check, which the proof discharges
  for them too.
- EXT-TMEM-ALLOC-RESULT-ORDER: an allocating warp's local result precedes its same-byte readback.
- EXT-TCALLOC-STORER (THREAD-TC): lane 0 of the allocating warp stores the allocated address with
  one generic-proxy weak store; fixing lane 0 and the generic proxy decides which reads are ordered
  after the store, and the kernel reads the address only after the whole allocating warp has
  synchronized, so it does not depend on which lane writes.
- EXT-TCFIG (THREAD-TC-MMA-RESULT-LAYOUT): the `.32x32b` load map (Figure 186) and the
  register-to-column map of the epilogue load.
- EXT-TCFIG (THREAD-TC-MMA-RESULT-LAYOUT): the Layout A result map of a CTA pair and the
  numbering of its 256 output-lane mask bits.
- EXT-TCFIG (THREAD-TC-MMA-OPERANDS): with `cta_group::2` A is split along M and B along N
  between the even and the odd CTA of the pair.
- EXT-TMEM-LANE-FIELD (THREAD-TC-DATA-ADDRESS): the lane field of a `tcgen05.ld.32x32b` address is a
  lane of the issuing warp's chunk, as an offset into it or as an absolute lane; the kernel fills 0
  in every warp `w` of the epilogue warpgroup, which reads lanes `32 w` to `32 w + 31`.
- EXT-TMA-GEOMETRY (THREAD-TENSOR-TILE): tiled tensor addresses, shared pitch and descriptor limits
  follow the CUDA Driver API.
- EXT-TMA-STORE-OOB (DEP-TENSOR-STORE-EFFECTS): out-of-bounds elements of a tensor store are not
written.
- EXT-BAR-PARTICIPANTS (ERR-BARRIER-MISMATCH): for `bar.sync b, 128` in a CTA of 384 threads the
  "all threads in CTA" of `.aligned` means the 128 participants.
- EXT-CLUSTER-RANK (PROG-CLUSTER, OBJ-CLC-ARBITRATION): the cluster of CTA `c` is `c / s` and its
  rank `c % s`; a canceled cluster's first CTA is `(t * s, 0, 0)`.
- EXT-ELECT-SITE (DEP-WARP-ELECT): the lanes of one election execute one `elect.sync` instruction.
- EXT-SETMAXNREG-VIRTUAL (THREAD-SETMAXNREG): PTX registers keep their values across `setmaxnreg`.
- EXT-SETMAXNREG-EFFECTIVE (THREAD-SETMAXNREG): the launch's register configuration is valid, so
  every `setmaxnreg.inc/dec` takes effect and returns once all lanes of the warp have executed it.
  If the registers at launch cannot satisfy every `setmaxnreg.inc 224`, hardware blocks the warp
  forever and `progress` does not transfer; with a configuration that is not valid a request may
  have no effect. The direction of each warp's first request relative to the launch's per-thread
  register count is not checked (kernel: producer `dec 56`, consumer `inc 224`); each warp makes
  one request, so no later request is compared with one that may not have taken effect.
- EXT-READ-WAIT-ORDER (MEM-OBSERVED-COMPLETION): after `cp.async.bulk.wait_group.read` returns, the
  asynchronous source reads of that bulk group are ordered before later generic accesses of the
  waiting thread's causal successors without a `fence.proxy.async`; wider than the text, relies on
  hardware. The kernel's epilogue does `wait_group.read 1`, then `bar.sync`, then `st.shared` to the
  reused buffer (fp16_gemm_8192.ptx lines 1770, 1813, 1857, 1901, 1945, 1989, 2033, 2077).
- EXT-CLUSTER-WAIT-PHASE (OBJ-CLUSTER-BARRIER-STATE): `barrier.cluster.wait` waits for the phase
  of the executing thread's most recent `barrier.cluster.arrive`.
- The kernel's assumptions (`Assumptions.lean`), in the statement: `Assumptions.idealArith`
  (`idealReal`) reads `cvt.rn.f16x2.f32` and the `kind::f16` MMA with f16 inputs and f32
  accumulator as exact real arithmetic; `Assumptions.clusterMbar` (`clusterScopeMbarAt`) treats
  the `.cta`-scoped release arrivals and acquire waits at the kernel's 37 mbarrier arrival and
  wait sites as cluster-scoped (all of them: the proof treats every poll and arrival uniformly);
  `Assumptions.pollAgree` (`pollAgreeAt`) states that the consumer warps' lanes spinning in
  their `try_wait P; @P bra.uni` loops on one mbarrier stay converged and get the same poll
  result, at the branches after their accumulator-full and CLC-response waits (pcs 747, 708).
- EXT-ASYNC-OBJECT and EXT-ENABLES-OBJECT (MEM-OBJECT-ORDER-CAUSALITY): not derived from PTX. The
  enabling order also places the completions of the tensor loads, commits, CLC responses, MMA reads
  and tensor-store reads before the exits of the CTAs whose shared memory they use
  (ERR-SHARED-LIFETIME).
- EXT-STAGE-ORDER (MEM-OBJECT-ORDER-CAUSALITY): an operation's issue precedes its completion, the
  operand reads of a tracked MMA precede its completion, a `clusterlaunchcontrol.try_cancel` request
  resolves before its response is written, and the participating warps of a Tensor Memory
  allocation-management operation (both warps of a `cta_group::2` pairing) precede its blocking
  return, not derived from PTX.
- EXT-PAIR-ASYNC (MEM-MODEL-CAUSALITY): for a `cta_group::2` CTA pair, asynchronous-proxy accesses
  to shared memory of either CTA of the pair, issued by either CTA of the pair, count as performed
  by the same thread block in §8.9.5; the odd CTA's tensor loads and the leader CTA's `tcgen05.mma`
  operand reads are ordered through it.
- EXT-TCACQUIRE (DEP-TC-COMPLETION): an acquire wait orders later `tcgen05` operations without
  `tcgen05.fence::after_thread_sync`.
- EXT-TC-SOURCE-REUSE: an acquire that observes the completion of an MMA orders its shared
  operand read before a later ordinary overwrite of the same byte in the acquiring thread.
- EXT-TC-COMMIT-OPERAND-ORDER: an observed MMA commit carries prior shared operand writes to
  the observer's later accesses to those bytes.
- EXT-DEPENDENCY-ORDER (ERR-NONUNIFORM-GUARD): listed because the kernel has guarded `bra.uni`; two
  executions of one position by two lanes are compared unless the execution-dependency order
  orders them. The kernel's other poll branches are polled by one elected lane per warp, and its
  consumers' branches are exempt by `Assumptions.pollAgree`.
- EXT-BAR-ZERO-COUNT (THREAD-BAR): listed because the kernel's `bar.sync` has an explicit count;
  its count (128) is below the CTA size (384), so the reading does not change its meaning.
- EXT-TMA-BOX-ALIGN (THREAD-TENSOR-DESCRIPTOR), stricter: a tensor copy whose box start is not
  16-byte aligned faults; the proof shows that none does.
- EXT-INIT-FENCE-ARRIVE (OBJ-MBAR-INIT-PUBLICATION): the mbarrier initializations, followed by
  `fence.mbarrier_init.release.cluster` and a `barrier.cluster.arrive`, are ordered before the
  operations that follow the `barrier.cluster.wait` observing that arrival.
- EXT-IEEE754 (THREAD-FLOAT-IEEE): an instruction with a rounding modifier computes the exact
  result of its operands and rounds it as IEEE 754 specifies (rounding directions, infinity and
  NaN arithmetic, the sign of an exact zero, invalid operations and overflow); the manual's own
  overrides (`.ftz`, `.sat`, `.relu`, `.satfinite`, the unspecified NaN) take precedence, and the
  rules come from IEEE 754-2008/2019, not from PTX.
- EXT-FLOAT-BITS (THREAD-BITS): under the ideal-arithmetic assumption a result is a real number
  that may not be representable in its format; where its bits are read, they are that number
  rounded to nearest, ties to even.
- EXT-TCFIG (THREAD-TC-SHARED-ADDRESS): listed because the kernel issues MMAs with shared-memory
  descriptors, whose swizzling mode is runtime data; it affects an operand only when its descriptor
  selects the 32-byte-atomic mode. -/

/-- The frozen production FP16 GEMM is safe, makes progress, terminates and
computes the real-number GEMM specified by `Post`, under the explicit launch,
input, storage and resource precondition. -/
theorem correct {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) : Correct kernel Prod L mem0 (Post P mem0) :=
  Proof.correct hpre

/-- The production model admits a completed execution. -/
theorem completed_execution {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X, Consistent L kernel Prod mem0 X ∧ Complete L X :=
  (correct hpre).complete_exists (Proof.valid hpre) (by
    simp [Assumptions.idealArith, Assumption.idealReal, Assumptions.clusterMbar,
      Assumption.clusterScopeMbarAt, Assumptions.pollAgree, Assumption.pollAgreeAt])

/-- A completed execution with the specified real GEMM output exists. -/
theorem realizable_result {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X mf, Consistent L kernel Prod mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post P mem0 mf :=
  (correct hpre).output_exists (Proof.valid hpre) (by
    simp [Assumptions.idealArith, Assumption.idealReal, Assumptions.clusterMbar,
      Assumption.clusterScopeMbarAt, Assumptions.pollAgree, Assumption.pollAgreeAt])

end
end PTX.Kernels.Fp16Gemm8192
