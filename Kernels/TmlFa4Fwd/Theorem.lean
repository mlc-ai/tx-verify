-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correct
public import Lemmas.Kernel.Existence

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX
noncomputable section

/-! ## Readings this result depends on

These results hold for the executions of the Core model (`Consistent`). Besides the kernel
assumptions in the statement they rely on the following readings and obligations, each
documented beside its rule (see `Core/README.md`). `Tools/reading_uses.py` checks that this list
is the set of readings whose instruction forms or assumption constructors the statement names;
the same set is kept in `READINGS.md`.

- EXT-ISA, EXT-IMPORT: `ptxas` and the hardware implement the PTX ISA; the Lean source is the
  compiled PTX.
- EXT-LAUNCH: the launch description is the real one, including the parameter bytes and the
  tensor maps, with its launch obligations.
- EXT-FAIR: `progress` and `terminates` are statements about the model; that a real run is a
  `FairRun` is taken from the CUDA programming guide, not from PTX, and is not proved here.
- EXT-ADDR-WRAP: the `[reg+immOff]` address sum is taken modulo the address width.
- EXT-CVTA: the global bases of the tensor maps are the host pointers of the allocations.
- EXT-SHARED: the kernel's `.shared` variables lie at the decoder's offsets from
  `Launch.sharedBase`.
- EXT-LOCAL-CONST-LAYOUT: the `.local` and `.const` variables lie at the decoder's offsets, in
  disjoint and aligned bytes.
- EXT-WARP: a warp is 32 consecutive threads of a CTA.
- EXT-ENDIAN: multi-byte values and packed pairs are stored little-endian, low half first.
- EXT-VECTOR-ELEM: in a vector access, element `j` is the scalar access at `base + size * j`.
- EXT-IEEE754: an instruction with a rounding modifier computes the exact result of its operands
  and rounds it as IEEE 754 specifies, with the manual's own overrides taking precedence.
- EXT-FLOAT-BITS: under `idealArith` a result is a real number; where its bits are read, they
  are that number rounded to nearest, ties to even.
- EXT-OBJECT-ORDER, EXT-ASYNC-OBJECT and EXT-ENABLES-OBJECT: the operations on one mbarrier and
  CTA barrier are totally ordered consistently with causality; an asynchronous update follows its
  issue in its object's order; enabling respects each object's order.
- EXT-STAGE-ORDER: an operation's issue precedes its completion, the operand reads of a tracked
  MMA precede its completion, and the participating warps of a Tensor Memory allocation-management
  operation precede its blocking return.
- EXT-INIT-FENCE-ARRIVE: the mbarrier initializations and their fence are ordered before the
  operations that follow the barrier observing them.
- EXT-BAR-PARTICIPANTS, EXT-BAR-ZERO-COUNT: warps of different roles execute "the same" barrier
  or `setmaxnreg` instruction when they use the same barrier name and count, or the same request,
  from their own code; an explicit barrier count below the CTA size names the participants.
- EXT-ELECT-SITE: the lanes of one election execute one `elect.sync` instruction.
- EXT-WARP-INSTANCE: the n-th executions of a masked warp collective with one member mask form
  one instance.
- EXT-SHFL-UP-INDEX: the source lane of `shfl.sync.up` is an integer difference; a lane below the
  offset receives its own operand.
- EXT-DEPENDENCY-ORDER: two executions of a guarded `bra.uni` by lanes of a warp that the
  execution-dependency order orders are not executed together.
- EXT-SETMAXNREG-VIRTUAL and EXT-SETMAXNREG-EFFECTIVE: PTX registers keep their values across
  `setmaxnreg`, and the launch's register configuration is valid, so every request takes effect
  and returns.
- EXT-TMA-GEOMETRY: tiled tensor addresses, shared pitch and descriptor limits follow the CUDA
  Driver API.
- EXT-TMA-BOX-ALIGN, stricter: a tensor copy whose box start is not 16-byte aligned faults; the
  proof shows that none does.
- EXT-TMA-STORE-OOB: out-of-bounds elements of a tensor store are not written.
- EXT-READ-WAIT-ORDER: after `cp.async.bulk.wait_group.read` returns, the source reads of that
  bulk group are ordered before later generic accesses of the waiting thread's causal successors.
- EXT-TMEM-ALLOC-ORDER: each CTA's Tensor Memory allocator performs its requests in an order that
  contains causality.
- EXT-TMEM-ALLOC-RESULT-ORDER: an allocating warp's local result precedes its same-byte readback.
- EXT-TCALLOC-STORER: lane 0 of the allocating warp stores the allocated address with one
  generic-proxy weak store.
- EXT-TCACQUIRE: an acquire wait orders later `tcgen05` operations without
  `tcgen05.fence::after_thread_sync`.
- EXT-TC-COMMIT-OPERAND-ORDER: observing the completion of an MMA through a tracked commit
  carries the order of writes that precede a shared operand read to the waiting thread's later
  accesses of the same byte.
- EXT-TC-SOURCE-REUSE: an acquire that observes the completion of an MMA orders its shared
  operand read before a later ordinary overwrite of the same byte in the acquiring thread.
- EXT-TCFIG: the operand and result layouts of the MMAs and of the `tcgen05.ld` and `tcgen05.st`
  shapes the kernel uses.
- EXT-TMEM-LANE-FIELD: the lane field of a `tcgen05.ld/st.32x32b` address is a lane of the
  issuing warp's chunk.

The kernel's own assumptions (`Assumptions.all`, listed and justified in `Assumptions.lean` and
in `DECISIONS.md`), each narrowed to the instruction forms or positions it covers:

- `idealArith`: the BF16 QK and PV MMAs and the listed FP32 operations, maximums and comparisons
  are read as exact real operations.
- `approx`, `lg2`, `swExp2`: `ex2.approx`, `rcp.approx`, the LSE `lg2.approx` and the software
  `exp2` sequences are read as the exact functions on their finite inputs.
- `bf16Convert`: the Bias widening and the probability packing preserve their finite real
  values.
- `pollAgree`: at the listed poll branches, lanes of a warp spinning on one mbarrier get the
  same poll result.
- `commitOrder`: the selected Q-empty commit completes in order with the next commit of the same
  lane.
- `tcLdDataflow`: the listed `tcgen05.ld` without a wait are complete once their results are
  consumed.
- `delayedTmem`: the biased score loads have completed by the first probability store of their
  round.
- `inputReadOnly`: the kernel never writes its input tensors. -/

/-- The tml-fa4 SM100 forward kernel is safe, makes progress, terminates and computes the
attention output and log-sum-exp specified by `Post`, under the launch, shape, input, storage and
resource precondition `Pre` and the kernel assumptions `Assumptions.all`. -/
theorem correct {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) : Correct kernel Assumptions.all L mem0 (Post P mem0) :=
  correct_of_pre hpre

/-- The model admits a completed execution. -/
theorem completed_execution {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X :=
  completed_execution_of_pre hpre

/-- A completed execution with the specified final memory exists. -/
theorem realizable_result {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X mf, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post P mem0 mf :=
  realizable_result_of_pre hpre

end
end PTX.Kernels.TmlFa4Fwd
