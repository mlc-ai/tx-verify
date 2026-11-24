-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Correct

@[expose] public section

namespace PTX.Kernels.InklingRelDecode
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
  PDL-dependent launch, no multimem addresses): the launch description is the real one, including
  the parameter bytes and the one tensor map `kv_desc`. The kernel is compiled for programmatic
  dependent launch (it has `griddepcontrol.wait` and `griddepcontrol.launch_dependents`); the
  obligation requires that this launch is not a dependent grid and has no dependent grid running
  concurrently. Its 512 Tensor Memory columns per CTA need one CTA of the kernel per SM and no
  co-resident CTA of another kernel that allocates Tensor Memory.
- EXT-GRIDDEP-SINGLE (THREAD-NO-EFFECT): listed because the kernel has `griddepcontrol`; under
  the launch obligation above the kernel runs as a single grid, so `griddepcontrol.wait` returns
  at once and `griddepcontrol.launch_dependents` has no effect.
- EXT-FAIR (CORRECT-FAIR): `progress` and `terminates` are statements about
  the model; that a real run is a `FairRun` (fair scheduling, eventual completion of
  asynchronous operations) is taken from the CUDA programming guide, not from PTX, and is not
  proved here.
- EXT-ADDR-WRAP (THREAD-ADDR): the `[reg+immOff]` address sum is taken modulo the address width.
- EXT-CVTA (THREAD-MOVE): the pointer parameters of the kernel (the query, relative-logit,
  block-table, sequence-length, `cu_seqlens_q` and the two output arrays) and the global base of
  the tensor map `kv_desc` are the host pointers of the allocations, used as global addresses.
- EXT-SHARED (PROG-DECODE): the kernel's `.shared` variable `global_smem` lies at the decoder's
  offset from `Launch.sharedBase`.
- EXT-WARP (PROG-CTA-WARP): a warp is 32 consecutive threads of a CTA.
- EXT-ENDIAN (MEM-BYTE): multi-byte values and packed pairs (the bf16 pairs of the query tile
  and of `P`) are stored little-endian, low half first.
- EXT-VECTOR-ELEM (THREAD-ACCESS): in the kernel's `st.shared::cta.v4.b32` (8 sites),
  `st.shared.v2.b32` and `ld.shared.v2.b32`, element `j` is the scalar access at `base + 4 j` and
  carries register `j`.
- EXT-IEEE754 (THREAD-FLOAT-IEEE): listed because the kernel has floating-point and `cvt`
  instructions; an instruction with a rounding modifier that no kernel assumption reads as exact
  computes the exact result of its operands and rounds it as IEEE 754 specifies (rounding
  directions, infinity and NaN arithmetic, the sign of an exact zero, invalid operations and
  overflow); the manual's own overrides (`.ftz`, `.sat`, `.relu`, `.satfinite`, the unspecified
  NaN) take precedence, and the rules come from IEEE 754-2008/2019, not from PTX.
- EXT-FLOAT-BITS (THREAD-BITS): under `idealArith` a result is a real number that may not be
  representable in its format; where its bits are read, they are that number rounded to nearest,
  ties to even.
- EXT-OBJECT-ORDER, EXT-ASYNC-OBJECT and EXT-ENABLES-OBJECT (MEM-OBJECT-ORDER-CAUSALITY): the
  operations on one mbarrier and on one CTA barrier (named barriers 0 and 1) are totally ordered
  consistently with causality; an asynchronous update (the complete-tx of a tensor load, the
  arrive-on of a `tcgen05.commit`) follows its issue in its object's order; enabling respects each
  object's order. Not derived from PTX.
- EXT-STAGE-ORDER (MEM-OBJECT-ORDER-CAUSALITY): an operation's issue precedes its completion and
  the operand reads of a tracked MMA precede its completion; not derived from PTX.
- EXT-BAR-PARTICIPANTS (ERR-BARRIER-MISMATCH): for the kernel's `bar.sync 0, 128` (21 sites, the
  four softmax warps in a CTA of 256), "all threads in CTA" of `.aligned` means the participants.
- EXT-BAR-PARTICIPANTS (ERR-BARRIER-MISMATCH, ERR-SETMAXNREG): warps of different roles execute
  "the same" barrier or `setmaxnreg` instruction when they use the same barrier name and count, or
  the same request, from their own code (named barrier 1 without a count from the 13 sites of the
  default warps, the loader, the MMA warp and the idle warps; the `setmaxnreg.inc 256` and
  `setmaxnreg.dec 24` of the worker warps from several positions).
- EXT-BAR-ZERO-COUNT (THREAD-BAR): listed because the kernel's `bar.sync` has an explicit count;
  its count (128) is below the CTA size, so the reading does not change its meaning.
- EXT-ELECT-SITE (DEP-WARP-ELECT): the lanes of one election execute one `elect.sync` instruction
  (31 sites).
- EXT-DEPENDENCY-ORDER (ERR-NONUNIFORM-GUARD): two executions of one of the kernel's six guarded
  `bra.uni` poll branches by lanes of a warp that the execution-dependency order orders
  (MEM-BASE-CAUSALITY, program order and the rendezvous of blocking collectives) are not executed
  together.
- EXT-SETMAXNREG-VIRTUAL and EXT-SETMAXNREG-EFFECTIVE (THREAD-SETMAXNREG): PTX registers keep their
  values across `setmaxnreg`, and the launch's register configuration is valid, so every
  `setmaxnreg.dec 24` and `inc 256` takes effect and returns.
- EXT-TMA-GEOMETRY (THREAD-TENSOR-TILE): tiled tensor addresses, shared pitch and descriptor limits
  follow the CUDA Driver API; the kernel's 20 `cp.async.bulk.tensor.2d` loads read 64 x 64 boxes
  of `kv_desc` with 128-byte swizzle.
- EXT-TMA-BOX-ALIGN (THREAD-TENSOR-DESCRIPTOR), stricter: a tensor copy whose box start is not
  16-byte aligned faults; the proof shows that none does.
- EXT-TMEM-ALLOC-ORDER (OBJ-TMEM-ORDER, DEP-TMEM-ALLOC-WAIT): the CTA's Tensor Memory allocator
  performs the requests of the kernel's `tcgen05.alloc.cta_group::1`, `relinquish_alloc_permit`
  and two `dealloc` in an order that contains causality, and each before the issuing warp returns.
- EXT-TMEM-ALLOC-RESULT-ORDER: an allocating warp's local result precedes its same-byte readback.
- EXT-TCALLOC-STORER (THREAD-TC): lane 0 of the allocating warp stores the allocated address with
  one generic-proxy weak store.
- EXT-TCACQUIRE (DEP-TC-COMPLETION): an acquire wait orders later `tcgen05` operations without
  `tcgen05.fence::after_thread_sync` (the kernel has no tcgen05 fence).
- EXT-TC-SOURCE-REUSE: an acquire that observes the completion of an MMA orders its shared
  operand read before a later ordinary overwrite of the same byte in the acquiring thread.
- EXT-TC-COMMIT-OPERAND-ORDER: an observed MMA commit carries prior shared operand writes to
  the observer's later accesses to those bytes.
- EXT-TCFIG (THREAD-TC-MMA-RESULT-LAYOUT): the result layout of the QK and PV MMAs (`cta_group::1`,
  M = 128): row `i` of D in lane `i`, column `j` at column `base + j`.
- EXT-TCFIG (THREAD-TC-MMA-RESULT-LAYOUT): the PV MMAs read A from Tensor Memory, laid out as D
  (at `[tmem_a + imm]`, the offset added to the column index, THREAD-TC).
- EXT-TCFIG (THREAD-TC-SHARED-ADDRESS): listed because the kernel issues MMAs with shared-memory
  descriptors, whose swizzling mode is runtime data; it affects an operand only when its
  descriptor selects the 32-byte-atomic mode.
- EXT-TMEM-LANE-FIELD (THREAD-TC-DATA-ADDRESS): the kernel's `tcgen05.ld.16x32bx2.x64` (3 sites)
  and `tcgen05.st.16x32bx2` (`.x64` and `.x32`): the register fragment is the stated coordinate
  map, the lane field of an address is an offset into the issuing warp's 32-lane chunk or an
  absolute lane inside it, and the second access starts `immHalfSplitoff` columns after the first
  on the same 16 lanes.

The kernel's own assumptions (`Assumptions.all`, listed and justified in `Assumptions.lean` and in
`Assumptions/*.lean`), each narrowed to the instruction forms or positions
it covers:

- `idealArith`: the `kind::f16` MMAs (bf16 inputs, f32 accumulator), the `.f32` `add`, `sub`,
  `mul`, `fma`, `min` and `max`, the `.f32x2` `add`, `mul` and `fma`, and floating `setp`
  including `setpInf` (a comparison with the infinity constant, in the extended reals) are read as
  exact real operations.
- `approx`: `ex2.approx.ftz.f32` (65 sites) and `rcp.approx.ftz.f32` (1 site) are read as the
  exact functions `2 ^ x` and `1 / x`.
- `swExp2`: the 16 instances of the software `exp2` sequence of 11 instructions (pc 1913 to 2088)
  are read as the exact function `2 ^ x`, `0` for `-inf`.
- `lg2Exact`: `lg2.approx.ftz.f32` at pc 2562 is read as the exact `log2` of a finite positive
  operand.
- `divFullExact`: `div.full.f32` at pc 600 is read as the exact quotient of finite operands; a
  zero divisor is undefined.
- `negExact`: `neg.f32` at pc 807 is read as the exact negation.
- `bf16Exact`: `cvt.f32.bf16` (64 sites) and `cvt.rn.bf16x2.f32` (32 sites) are read as exact; the
  pack keeps both numbers without rounding them to bf16.
- `commitOrder`: the `tcgen05.commit` of the key-value slot release (pc 2546) and the one of the
  `o_done` barrier (pc 2548) complete in order with the thread's next commit.
- `pollAgree`: at the kernel's six poll branches, lanes of a warp spinning on one mbarrier stay
  converged and get the same poll result.
- `setMaxNRegSync`: the `setmaxnreg.inc 256` at the head of the worker dispatch loop (pc 2337)
  needs no warpgroup synchronization after the request before it.
- `inputReadOnly`: a plain `ld.global` at one of the kernel's 203 global loads returns the launch
  content, and a write of a byte of an input array is undefined. -/

/-- The Inkling 2 Small relative decode kernel (`_rel_verify_kernel`) is safe, makes progress,
terminates and stores the partial attention output and normalizer specified by `Post`, under the
launch, shape, input, storage and resource precondition `Pre` and the kernel assumptions
`Assumptions.all`. -/
theorem correct {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) : Correct kernel Assumptions.all L mem0 (Post P mem0) :=
  Proof.correct_of_pre hpre

/-- The model admits a completed execution. -/
theorem completed_execution {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X :=
  Proof.completed_execution_of_pre hpre

/-- A completed execution with the specified partial attention output exists. -/
theorem realizable_result {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X mf, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post P mem0 mf :=
  Proof.realizable_result_of_pre hpre

end
end PTX.Kernels.InklingRelDecode
