-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Main
public import Kernels.FlashKdaFwd.Proof.Top.Reading

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd
open PTX
noncomputable section

/-! ## Readings this result depends on

These results hold for the executions of the Core model (`Consistent`); besides the kernel
assumptions in the statement they rely on the following readings and obligations, each
documented beside its rule (see `Core/README.md`). `Tools/reading_uses.py` checks that this list
is the set of readings whose instruction forms or assumption constructors the statement names.

- EXT-ISA, EXT-IMPORT: `ptxas` and the hardware implement the PTX ISA; the Lean source is the
  compiled PTX of the patched kernel (`packed_fp32_sm100a.ptx`, see the README).
- EXT-LAUNCH, with its six launch obligations (no aliases, pointer state spaces, immutable tensor
  maps, Tensor Memory requested by co-resident CTAs, no conflicting outside access and no
  PDL-dependent launch, no multimem addresses): the launch description is the real one,
  including the parameter bytes, the two parameter objects and the eleven tensor maps. The kernel
  uses no Tensor Memory and no `griddepcontrol`.
- EXT-FAIR (CORRECT-FAIR): `progress` and `terminates` are statements about the model; that a
  real run is a `FairRun` (fair scheduling, eventual completion of asynchronous operations) is
  taken from the CUDA programming guide, not from PTX, and is not proved here.
- EXT-ADDR-WRAP (THREAD-ADDR): the `[reg+immOff]` address sum is taken modulo the address width.
- EXT-CVTA (THREAD-MOVE): the two pointer parameters the kernel converts with
  `cvta.to.global.u64` (the packed offsets `cu_seqlens`, parameter 15, and the output array,
  parameter 11, for the element stores of a partial last tile) and the global bases of the eleven
  tensor maps are the host pointers of the allocations, used as global addresses.
- EXT-SHARED (PROG-DECODE): the kernel's one `.shared` variable `shared_mem` lies at the decoder's
  offset from `Launch.sharedBase`.
- EXT-BRKPT (PROG-DECODE), stricter: the kernel's 14 `brkpt` (the debug assertions of the CUTLASS
  pipeline classes, compiled because the build does not define `NDEBUG`) are read as `trap`; the
  proof shows that no consistent execution reaches one. Three of them check that the thread an
  `elect.sync` chose is lane 0 and are excluded by the assumption `electZero`; the other eleven
  are behind conditions on the thread index that never hold.
- EXT-WARP (PROG-CTA-WARP): a warp is 32 consecutive threads of a CTA.
- EXT-CLUSTER-RANK (PROG-CLUSTER): listed because the kernel reads `%cluster_ctarank` and has two
  `mapa.shared::cluster.u32`; `Pre` launches it without clusters, so every CTA is alone in its
  cluster, has rank 0, and `mapa` returns the CTA's own shared address.
- EXT-ENDIAN (MEM-BYTE): multi-byte values and packed pairs (the bfloat16 pairs of the matrix
  operands, the 64-bit entries of `cu_seqlens`) are stored little-endian, low half first.
- EXT-VECTOR-ELEM (THREAD-ACCESS): in the kernel's one `ld.shared.v4.b32`, element `j` is the
  scalar access at `base + 4 j` and writes register `j`.
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
  operations on one mbarrier (the kernel has eleven per CTA) and on one CTA barrier (barriers 0
  and 8) are totally ordered consistently with causality; the complete-tx of a tensor load follows
  its issue in its mbarrier's order; enabling respects each object's order. Not derived from PTX.
- EXT-STAGE-ORDER (MEM-OBJECT-ORDER-CAUSALITY): an operation's issue precedes its completion;
  not derived from PTX.
- EXT-INIT-FENCE-ARRIVE (OBJ-MBAR-INIT-PUBLICATION): listed because the kernel has
  `fence.mbarrier_init.release.cluster` (3 sites); it has no `barrier.cluster.arrive`, and its
  mbarrier initializations are published to the other threads by `bar.sync 0`, so the proof does
  not use the reading.
- EXT-BAR-PARTICIPANTS (ERR-BARRIER-MISMATCH): for the kernel's `bar.sync` on barrier 8 with 128
  threads in a CTA of 192 (the four compute warps, once per tile), "all threads in CTA" of
  `.aligned` means the participants; the load warp and the store warp do not execute it.
- EXT-BAR-ZERO-COUNT (THREAD-BAR): listed because that `bar.sync` has an explicit count; the count
  (128) is neither zero nor the CTA size, so the reading does not change its meaning.
- EXT-ELECT-SITE (DEP-WARP-ELECT): the lanes of one election execute one `elect.sync` instruction
  (5 sites).
- EXT-DEPENDENCY-ORDER (ERR-NONUNIFORM-GUARD): listed because the kernel has `bra.uni` (4 sites);
  none of them is guarded, so no execution of one is compared with another.
- EXT-MATRIX-FIGURES (THREAD-MATRIX-LAYOUT): the fragment layouts and row addresses of the
  kernel's `ldmatrix.sync.aligned.x4.m8n8.shared.b16` (44 sites, 8 of them `.trans`),
  `stmatrix.sync.aligned.x4.m8n8.shared.b16` (18 sites, 16 of them `.trans`) and
  `movmatrix.sync.aligned.m8n8.trans.b16` (16 sites) are those of the manual's figures.
- EXT-MMA-FRAGMENTS (THREAD-MMA-SYNC): the A, B and C fragments of the kernel's 104
  `mma.sync.aligned.m16n8k16.row.col.f32.bf16.bf16.f32` follow the manual's formulas; the
  exception the note makes (`m16n8k256`) does not occur.
- EXT-TMA-GEOMETRY (THREAD-TENSOR-TILE): tiled tensor addresses, shared pitch and descriptor
  limits follow the CUDA Driver API; the kernel's 226 tensor loads and 32 tensor stores use the
  eleven maps of `Pre` (`Data/TensorMaps.lean`): nine without swizzle, and the two maps of the
  FP32 state (boxes of 8 × 128 floats) with the 32-byte swizzle.
- EXT-TMA-BOX-ALIGN (THREAD-TENSOR-DESCRIPTOR), stricter: a tensor copy whose box start is not
  16-byte aligned faults; the proof shows that none does.
- EXT-TMA-STORE-OOB (DEP-TENSOR-STORE-EFFECTS): out-of-bounds elements of a tensor store are not
  written; the proof shows that no tensor store of the kernel selects one (a partial last tile is
  stored element by element with `st.global.b16`).
- EXT-READ-WAIT-ORDER (MEM-OBSERVED-COMPLETION): after `cp.async.bulk.wait_group.read` returns
  (2 sites: the store warp after the stores of a tile, and the epilogue after the stores of the
  final state), the source reads of that bulk group are ordered before later generic accesses of
  the waiting thread's causal successors without a `fence.proxy.async`.

The kernel's own assumptions (`Assumptions.all`, listed and justified in `Assumptions.lean` and
in `Assumptions/*.lean`), each narrowed to the instruction forms or positions it covers:

- `idealArith`: the 104 `mma.sync` (bfloat16 inputs, FP32 accumulator) and the `.f32` `add`, `sub`,
  `mul` and `fma` (2, 16, 18 and 128 sites) are read as exact real operations.
- `approx`: `ex2.approx.ftz.f32` (2 sites) and `rcp.approx.ftz.f32` (2 sites) are read as the
  exact functions `2 ^ x` and `1 / x`.
- `narrow`: `cvt.rn.bf16.f32` (186 sites) of a finite value keeps its real value.
- `sharedBits`: at the 266 swizzle triples (`shr.u64 …, 3`, `and.b64 …, 16`, `xor.b64`) a generic
  shared pointer is read as its byte address.
- `electZero`: an `elect.sync` over the full warp elects lane 0.
- `inputReadOnly`: a plain `ld.global` at one of the kernel's 21 global loads returns the launch
  content of the packed-offsets array, and a write of a byte of that array is undefined. -/

/-- The FlashKDA forward recurrence kernel (packed batch, FP32 state) is safe, makes progress,
terminates and writes the outputs and the final state that `Post` specifies, under the launch,
shape, input and storage precondition `Pre` and the kernel assumptions `Assumptions.all`. -/
theorem correct {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) : Correct kernel Assumptions.all L mem0 (Post P mem0) :=
  Proof.Top.correct_of_contracts hpre (Proof.Ref.Assembly.contracts hpre)

/-- The model admits a completed execution. -/
theorem completed_execution {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X :=
  Proof.Top.completed_execution_of_correct hpre (correct hpre)

/-- A completed execution with the specified final memory exists. -/
theorem realizable_result {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) :
    ∃ X mf, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post P mem0 mf :=
  Proof.Top.realizable_result_of_correct hpre (correct hpre)

end
end PTX.Kernels.FlashKdaFwd
