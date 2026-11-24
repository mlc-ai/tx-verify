-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Correct
public import Lemmas.Kernel.Existence

@[expose] public section

namespace PTX.Kernels.FlashAttn4Fwd
open PTX
noncomputable section

/-! ## Readings this result depends on

These results hold for the executions of the Core model (`Consistent`); besides the kernel
assumptions in the statement they rely on the following readings and obligations, each
documented beside its rule (see `Core/README.md`). `Tools/reading_uses.py` checks that this list
is the set of readings whose instruction forms or assumption constructors the statement names.

- EXT-ISA, EXT-IMPORT: `ptxas` and the hardware implement the PTX ISA; the Lean source is
  the compiled PTX.
- EXT-LAUNCH, with its six launch obligations (no aliases, pointer state spaces, immutable tensor
  maps, Tensor Memory requested by co-resident CTAs, no conflicting outside access and no
  PDL-dependent launch, no multimem addresses): the launch description is the real one,
  including the parameter bytes and the four tensor maps.
- EXT-FAIR (CORRECT-FAIR): `progress` and `terminates` are statements about
  the model; that a real run is a `FairRun` (fair scheduling, eventual completion of
  asynchronous operations) is taken from the CUDA programming guide, not from PTX, and is not
  proved here.
- EXT-ADDR-WRAP (THREAD-ADDR): the `[reg+immOff]` address sum is taken modulo the address width.
- EXT-CVTA (THREAD-MOVE): the global bases of the tensor maps are the host pointers of the
  allocations.
- EXT-SHARED (PROG-DECODE): the kernel's `.shared` variables lie at the decoder's offsets from
  `Launch.sharedBase`.
- EXT-WARP (PROG-CTA-WARP): a warp is 32 consecutive threads of a CTA.
- EXT-ENDIAN (MEM-BYTE): multi-byte values and packed pairs are stored little-endian, low half
  first.
- EXT-VECTOR-ELEM (THREAD-ACCESS): in the kernel's `st.shared.v4.b32`, element `j` is the scalar
  store at `base + 4 j` and carries register `j`.
- EXT-IEEE754 (THREAD-FLOAT-IEEE): an instruction with a rounding modifier computes the exact
  result of its operands and rounds it as IEEE 754 specifies (rounding directions, infinity and
  NaN arithmetic, the sign of an exact zero, invalid operations and overflow); the manual's own
  overrides (`.ftz`, `.sat`, `.relu`, `.satfinite`, the unspecified NaN) take precedence, and the
  rules come from IEEE 754-2008/2019, not from PTX.
- EXT-FLOAT-BITS (THREAD-BITS): under `idealArith` a result is a real number that may not be
  representable in its format; where its bits are read, they are that number rounded to nearest,
  ties to even.
- EXT-OBJECT-ORDER, EXT-ASYNC-OBJECT and EXT-ENABLES-OBJECT (MEM-OBJECT-ORDER-CAUSALITY): the
  operations on one mbarrier, CTA barrier and cluster barrier are totally ordered consistently with
  causality; an asynchronous update (tensor-load complete-tx, commit arrive-on) follows its issue in
  its object's order; enabling respects each object's order. Not derived from PTX.
- EXT-STAGE-ORDER (MEM-OBJECT-ORDER-CAUSALITY): an operation's issue precedes its completion, the
  operand reads of a tracked MMA precede its completion, and the participating warps of a Tensor
  Memory allocation-management operation precede its blocking return; not derived from PTX.
- EXT-INIT-FENCE-ARRIVE (OBJ-MBAR-INIT-PUBLICATION): the mbarrier initializations, followed by
  `fence.mbarrier_init.release.cluster` and `barrier.cluster.arrive.relaxed`, are ordered before
  the operations that follow the `barrier.cluster.wait` observing that arrival.
- EXT-CLUSTER-RANK (PROG-CLUSTER): the cluster of CTA `c` is `c / 2` and its rank `c % 2`
  (`%cluster_ctarank`, `mapa`, the CTA pair).
- EXT-CLUSTER-WAIT-PHASE (OBJ-CLUSTER-BARRIER-STATE): `barrier.cluster.wait` waits for the phase
  of the executing thread's most recent `barrier.cluster.arrive`.
- EXT-BAR-PARTICIPANTS (ERR-BARRIER-MISMATCH): for the kernel's `bar.sync` and `bar.arrive` with 416
  and 64 threads in a CTA of 512, "all threads in CTA" of `.aligned` means the participants.
- EXT-BAR-PARTICIPANTS (ERR-BARRIER-MISMATCH, ERR-SETMAXNREG): warps of different roles execute
  "the same" barrier or `setmaxnreg` instruction when they use the same barrier name and count, or
  the same request, from their own code (barrier 2 from five positions, warpgroup 3's
  `setmaxnreg.dec 72` from four).
- EXT-BAR-ZERO-COUNT (THREAD-BAR): listed because the kernel's `bar.sync` has an explicit count;
  its counts (416, 64) are below the CTA size, so the reading does not change their meaning.
- EXT-ELECT-SITE (DEP-WARP-ELECT): the lanes of one election execute one `elect.sync` instruction.
- EXT-WARP-INSTANCE (DEP-WARP-INSTANCE): the kernel's `vote.sync.ballot` pairs each lane's n-th
  execution with a given member mask with the n-th execution of every other non-exited lane of it.
- EXT-DEPENDENCY-ORDER (ERR-NONUNIFORM-GUARD): two executions of a guarded `bra.uni` by lanes of a
  warp that the execution-dependency order orders (MEM-BASE-CAUSALITY, program order and the
  rendezvous of blocking collectives) are not executed together; the loader's and the MMA warp's
  ring polls in different rounds are ordered through the `elect.sync` and `shfl.sync` between the
  rounds.
- EXT-PAIR-ALLOC-ORDER (OBJ-TMEM-PUBLICATION): the MMA warp's paired `tcgen05.alloc.cta_group::2`
  makes each CTA's allocation complete before the instruction returns in the peer warp, so the
  odd CTA's allocation covers the leader CTA's later MMAs on the odd CTA's cells.
- EXT-SETMAXNREG-VIRTUAL and EXT-SETMAXNREG-EFFECTIVE (THREAD-SETMAXNREG): PTX registers keep their
  values across `setmaxnreg`, and the launch's register configuration is valid, so every
  `setmaxnreg.dec 72`, `dec 88` and `inc 176` takes effect and returns.
- EXT-TMA-GEOMETRY (THREAD-TENSOR-TILE): tiled tensor addresses, shared pitch and descriptor limits
  follow the CUDA Driver API.
- EXT-TMA-BOX-ALIGN (THREAD-TENSOR-DESCRIPTOR), stricter: a tensor copy whose box start is not
  16-byte aligned faults; the proof shows that none does.
- EXT-TMA-STORE-OOB (DEP-TENSOR-STORE-EFFECTS): out-of-bounds elements of a tensor store are not
written.
- EXT-READ-WAIT-ORDER (MEM-OBSERVED-COMPLETION): after `cp.async.bulk.wait_group.read` returns, the
  source reads of that bulk group are ordered before later generic accesses of the waiting thread's
  causal successors without a `fence.proxy.async`.
- EXT-PAIR-ASYNC (MEM-MODEL-CAUSALITY): for the `cta_group::2` pair, asynchronous-proxy accesses to
  the shared memory of either CTA count as performed by one thread block.
- EXT-TMEM-ALLOC-ORDER (OBJ-TMEM-ORDER, DEP-TMEM-ALLOC-WAIT): each CTA's Tensor Memory
  allocator performs its requests in an order that contains causality, and its half of a
  `cta_group::2` request before the issuing warp returns.
- EXT-TMEM-ALLOC-RESULT-ORDER: an allocating warp's local result precedes its same-byte readback.
- EXT-TCALLOC-STORER (THREAD-TC): lane 0 of the allocating warp stores the allocated address with
  one generic-proxy weak store.
- EXT-TCACQUIRE (DEP-TC-COMPLETION): an acquire wait orders later `tcgen05` operations without
  `tcgen05.fence::after_thread_sync` (the kernel has no tcgen05 fence).
- EXT-TC-SOURCE-REUSE: an acquire that observes the completion of an MMA orders its shared
  operand read before a later ordinary overwrite of the same byte in the acquiring thread.
- EXT-TC-COMMIT-OPERAND-ORDER: an observed MMA commit carries prior shared operand writes to
  the observer's later accesses to those bytes.
- EXT-TCFIG (THREAD-TC-MMA-OPERANDS): with `cta_group::2` A is split along M and B along N
  between the even and the odd CTA of the pair.
- EXT-TCFIG (THREAD-TC-MMA-RESULT-LAYOUT): the result layouts of the MMAs and the
  `.32x32b` load and store maps.
- EXT-TCFIG (THREAD-TC-MMA-RESULT-LAYOUT): the P V MMAs read A from Tensor Memory, laid out as D
  (at `[tmem_a + imm]`, the offset added to the column index, THREAD-TC).
- EXT-TCFIG (THREAD-TC-SHARED-ADDRESS): listed because the kernel issues MMAs with shared-memory
  descriptors, whose swizzling mode is runtime data; it affects an operand only when its
  descriptor selects the 32-byte-atomic mode.
- EXT-TMEM-LANE-FIELD (THREAD-TC-DATA-ADDRESS): the lane field of a `tcgen05.ld/st.32x32b` address
  is a lane of the issuing warp's chunk.

The kernel's own assumptions (`Assumptions.all`, listed and justified in `Assumptions.lean` and
in `DECISIONS.md`), each narrowed to the instruction forms or positions it covers:

- `idealArith`: the `kind::f16` MMAs (f16 inputs, f32 accumulator), the `.f32` and `.f32x2`
  `add`, `sub`, `mul` and `fma` forms, `max.f32`, floating `setp` including `setpInf` (a `setp`
  with the `-inf` constant `0fFF800000`, compared in the extended reals) and
  `cvt.rn.f16x2.f32` are read as exact real operations.
- `approx`, `swExp2`: `ex2.approx`, `rcp.approx` and the software `exp2` sequences are read as
  the exact functions.
- `clusterMbar`: the listed mbarrier operations act at cluster scope.
- `peerBit`: clearing bit 24 of a shared address names the even CTA of the pair.
- `tcLd`: a `tcgen05.ld` whose values are consumed is completed by the implicit wait.
- `commitOrder`: the selected commit completes in order with the thread's next commit.
- `pollAgree`: at the kernel's 37 poll branches, lanes of a warp spinning on one mbarrier stay
  converged and get the same poll result. -/

/-- The FlashAttention-4 forward kernel is safe, makes progress, terminates and computes the
attention output specified by `Post`, under the launch, shape, input, storage and resource
precondition `Pre` and the kernel assumptions `Assumptions.all`. -/
theorem correct {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) : Correct kernel Assumptions.all L mem0 (Post P mem0) :=
  Proof.correct hpre

/-- The model admits a completed execution. -/
theorem completed_execution {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X :=
  Proof.completed_execution hpre

/-- A completed execution with the specified attention output exists. -/
theorem realizable_result {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X mf, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post P mem0 mf :=
  Proof.realizable_result hpre

end
end PTX.Kernels.FlashAttn4Fwd
