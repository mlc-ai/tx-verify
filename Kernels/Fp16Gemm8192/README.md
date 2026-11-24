# Production FP16 8192 GEMM

[Theorem.lean](Theorem.lean) exports `correct`, `completed_execution` and
`realizable_result`, covering safety, progress, termination and real GEMM results.
The premises are the explicit launch, input, storage and resource conditions in
[Spec.lean](Spec.lean), together with the kernel's three assumptions in
[Assumptions.lean](Assumptions.lean): `idealArith` (exact real arithmetic for
`cvt.rn.f16x2.f32` and the `kind::f16` f16→f32 MMA), `clusterMbar` (cluster scope for the
`.cta`-scoped arrivals and waits at all 37 mbarrier arrival and wait sites) and `pollAgree`
(lanes of a consumer warp spinning on one poll stay converged and get the same poll result, at
the two consumer poll branches).
Task ownership, phases and notification FIFO are not additional premises.

## Readings and launch obligations

Besides `idealArith`, `clusterMbar` and `pollAgree`, which appear in the statement, the result relies
on readings of the specification that are not derived from the PTX ISA text, and on launch
obligations the model does not check (the list is also in [Theorem.lean](Theorem.lean)):

- EXT-OBJECT-ORDER, EXT-ASYNC-OBJECT and EXT-ENABLES-OBJECT (below).
- EXT-STAGE-ORDER (MEM-OBJECT-ORDER-CAUSALITY): an operation's issue precedes its completion, the operand
  reads of a tracked MMA precede its completion, a `clusterlaunchcontrol.try_cancel` request
  resolves before its response is written, and the participating warps of a Tensor Memory
  allocation-management operation (both warps of a `cta_group::2` pairing) precede its blocking
  return.
- EXT-PAIR-ASYNC (MEM-MODEL-CAUSALITY): for a `cta_group::2` CTA pair, asynchronous-proxy accesses
  to shared memory of either CTA of the pair, issued by either CTA of the pair, count as
  performed by the same thread block in §8.9.5. The odd CTA's tensor loads are ordered with the
  leader CTA's `tcgen05.mma` operand reads only through it (`InputRing.pairAsync_of_pair`).
- EXT-TMEM-ALLOC-ORDER and EXT-TCALLOC-STORER: each CTA's Tensor Memory allocator performs that
  CTA's requests in an order that contains causality, and performs its CTA's half of a
  `cta_group::2` request before the issuing warp returns from the instruction, also when the warp
  does not wait for the peer CTA's warp; an allocation performed after such a deallocation half
  that the peer CTA's half does not causally precede is reported unsafe, and the kernel allocates
  only before it deallocates; lane 0 of the allocating warp stores the address with one
  generic-proxy weak store.
- EXT-PAIR-ALLOC-ORDER (OBJ-TMEM-PUBLICATION): the allocation is a paired
  `tcgen05.alloc.cta_group::2`, so each CTA's allocation also covers the accesses that the peer
  warp's allocation happens before. Every access is covered by its own CTA's allocation event;
  the reading adds records to the release check, which the proof discharges for them too.
- EXT-TCFIG and EXT-TMEM-LANE-FIELD: the `.32x32b` load map,
  the Layout A result map and mask numbering of a CTA pair, the split of A and B between the
  pair's CTAs, and the `tcgen05.ld` lane field read as a lane of the issuing warp's chunk,
  absolute or relative (every epilogue warp fills 0, the offset of its own 32 lanes).
- EXT-TMA-GEOMETRY and EXT-TMA-STORE-OOB: tiled tensor addresses, pitch and descriptor limits
  from the CUDA Driver API; out-of-bounds elements of the tensor store are not written.
- EXT-BAR-PARTICIPANTS: `bar.sync b, 128` in a CTA of 384 threads has the 128 participants as
  the "all threads in CTA" of `.aligned`.
- EXT-CLUSTER-RANK: the cluster of CTA `c` is `c / s` and its rank is `c % s`; a canceled
  cluster's first CTA is `(t * s, 0, 0)` (OBJ-CLC-ARBITRATION).
- EXT-ELECT-SITE: the lanes of one election execute one `elect.sync` instruction (stricter:
  lanes at two `elect.sync` instructions would block, which the progress proof excludes).
- EXT-ADDR-WRAP: the `[reg+immOff]` address sum is taken modulo the address width (`2^64`
  global, `2^32` shared).
- EXT-SETMAXNREG-VIRTUAL: PTX registers keep their values across `setmaxnreg`.
- EXT-SETMAXNREG-EFFECTIVE: the launch's register configuration is valid, so every
  `setmaxnreg.inc/dec` takes effect (with a configuration that is not valid, §9.7.21.5 says a
  request "may have no effect") and returns once all lanes of the warp have executed it. Hardware
  blocks a warp whose `inc` the registers at launch cannot satisfy, which the
  model's progress conclusion does not reflect; the launch must provide enough registers for
  every consumer `setmaxnreg.inc 224`. The 4 producer warps' `dec 56` and the 8 consumer warps'
  `inc 224` total 32 * (8 * 224 + 4 * 56) = 64512 registers, within the 65536 registers of an
  SM with one CTA per SM; the compiled kernel's per-thread count at launch is recorded as
  168 in [Validation/verification.json](Validation/verification.json) (168 * 384 = 64512). The
  model does not represent the launch's per-thread register count, so the direction of each
  warp's first request relative to it (producer `dec 56`, consumer `inc 224`) is not checked.
  Each warp makes one request, so no later request is compared with one that may not have taken
  effect.
- EXT-READ-WAIT-ORDER (MEM-OBSERVED-COMPLETION): after `cp.async.bulk.wait_group.read` returns, the
  asynchronous source reads of that bulk group are ordered before later generic accesses of the
  waiting thread's causal successors without a `fence.proxy.async`. This is wider than the text
  and relies on hardware; the epilogue does `wait_group.read 1`, `bar.sync`, then `st.shared` to
  the reused buffer (fp16_gemm_8192.ptx lines 1770, 1813, 1857, 1901, 1945, 1989, 2033, 2077).
- EXT-CLUSTER-WAIT-PHASE: `barrier.cluster.wait` waits for the phase of the executing thread's
  most recent `barrier.cluster.arrive`.
- EXT-WARP, EXT-SHARED, EXT-ENDIAN and EXT-VECTOR-ELEM: warps are 32 consecutive threads;
  `.shared` variables sit at the decoder's offsets from `Launch.sharedBase`; packed `f16`
  pairs and 32-bit words are little-endian; element `j` of a `.v2`/`.v4` access is at
  `base + j·size` and carries register `j` (the elements' execution order is unspecified,
  §8.2.4).
- EXT-CVTA (THREAD-MOVE): the generic address of a global allocation is its global address; the
  global bases of the tensor maps are the host pointers of the allocations (the kernel executes no
  `cvta.to.global`).
- EXT-TCACQUIRE: the acquire wait before the epilogue's `tcgen05.ld` orders it without
  `tcgen05.fence::after_thread_sync`.
- EXT-DEPENDENCY-ORDER and the assumption `pollAgree`: every guarded `bra.uni` of the kernel is
  a wait loop `try_wait P; @P bra.uni DONE` (`Proof.poll_guards`). ERR-NONUNIFORM-GUARD compares
  every two executions of such a branch by two lanes of a warp that the execution-dependency order
  does not order. The proof shows that each poll position polls one object in all lanes of a warp
  (`Proof.poll_obj_uniform`) and that the loader, MMA and scheduler polls run on their warp's
  single elected lane (`Proof.poll_ordered`). The consumers poll on all lanes, so two lanes polling
  one phase in one round are never ordered: the kernel assumption `pollAgree` (`pollAgreeAt`,
  ASM-POLL-AGREE, a hardware assumption: lanes of a warp spinning on one poll stay converged and
  get the same poll result) exempts the consumers' two poll branches (pcs 747 and 708, after their
  accumulator-full and CLC-response waits; `Assumptions.pollAgreeSites_ops`). Before 2026-11-15
  this was Core's reading EXT-UNI-POLL, applied to every kernel.
- EXT-BAR-ZERO-COUNT, EXT-FLOAT-BITS, EXT-INIT-FENCE-ARRIVE, EXT-TCFIG and EXT-TMA-BOX-ALIGN: also
  used by the statement; `Theorem.lean` lists every reading the statement uses, and
  `Tools/reading_uses.py` checks that list against the Core contracts.
- EXT-FAIR: progress and termination are proved for the model's fair runs; that
  a hardware run is one is not proved (the termination-transfer gap).
- EXT-LAUNCH, six obligations, met by the launch as follows. The kernel declares no
  `.ptr .space` parameter. The three tensor maps are by-value kernel parameters, which no
  decoded instruction writes. No conflicting outside access and no PDL-dependent launch (E1):
  the launch runs the kernel with no other reader or writer of the output memory the kernel
  writes and no other writer of the input or tensor-map memory (no concurrent kernel in another
  stream, no host or peer-device access) and not as a PDL dependent grid; `griddepcontrol.*` is not decoded. No multimem addresses (E2): the launch
  passes ordinary allocations. Tensor Memory requested by co-resident CTAs: the kernel's
  230400 bytes of shared memory per CTA allow one CTA per SM (checked in
  [Tests/Kernel/LaunchObligations.lean](../../Tests/Kernel/LaunchObligations.lean)), and the launch must
  ensure that no co-resident CTA of another kernel allocates Tensor Memory on that SM; this is
  an obligation of the launch, not checked by the model.

## Execution-order assumption

The conclusions hold for executions that satisfy `Consistent`. Its execution-order part
is four fields, stated in [Core/Assembly/WaitOrder.lean](../../Core/Assembly/WaitOrder.lean)
(MEM-OBJECT-ORDER-CAUSALITY) in the shape of the PTX axioms, with one object's order at a time:

- `observation` (`ObservationCausal`): a successful wait or blocking return does not
  causally precede the issue of what it observed.
- `object` (`ObjectCoherent`, EXT-OBJECT-ORDER): causality together with the order of any single object
  (one mbarrier, one CTA barrier ID, one cluster barrier; one CTA's Tensor
  Memory allocator under EXT-TMEM-ALLOC-ORDER) has no cycle.
- `asyncObject` (`AsyncObjectOrdered`, EXT-ASYNC-OBJECT): an asynchronous update (TMA
  complete-tx, commit arrive-on, CLC response) is not placed in its object's order before
  an operation that causally precedes the instruction that issued it.
- `dependency` (`DependencyOk`, EXT-ENABLES-OBJECT and DEP-ORDER): every returned event is ready
  (each wait has a witness) and the dependency order (an issue and the stages of its
  asynchronous operation, a witness before the return it fills, a return before the events
  that depend on it) together with any single object's order has no cycle; in particular no
  operation enables itself.

`observation` follows the PTX causality axiom. **EXT-OBJECT-ORDER, EXT-ASYNC-OBJECT and
EXT-ENABLES-OBJECT are not derived from the PTX specification.**
They read §8.9.1.1 and the completion and blocking sentences of the instruction
descriptions as event-occurrence dependencies. By §8.9.1.1 the complete-tx of
`cp.async.bulk` does not transitively order prior instructions of the issuing thread, so
the specification does not state, for example, that a TMA complete-tx cannot be counted in
a barrier phase that completed before the copy was issued. These rules are explicit
assumptions of this result; their rationale is in the review notes of the same file.

The joint wait relation `Waits` and its acyclicity `WaitAcyclic`, which ordered the atomic
orders of all objects together with program order, are not part of Core; they remain a proof
device in [Lemmas/Order/JointWaits.lean](../../Lemmas/Order/JointWaits.lean). The shared-memory
lifetime checks (ERR-SHARED-LIFETIME) order events by base causality or by the enabling relation
with one object's order, so the exit coverage of the tensor loads, commits, CLC responses, MMA
reads and tensor-store reads rests on EXT-ENABLES-OBJECT: the observing poll spins, and an exit
of another CTA of the pair is reached through the exit cluster barrier. [Tests/Memory/WaitOrderLitmus.lean](../../Tests/Memory/WaitOrderLitmus.lean)
contains the litmus tests, and [Tests/Progress/RingCountProto.lean](../../Tests/Progress/RingCountProto.lean)
derives the round attribution of one input-ring slot from the enabling rule.

## Layout

The top level contains the specification, raw PTX AST, public theorems, current PTX
and this guide. `Data/` contains specification data and source fingerprints;
`Flow/` contains the generated site and instruction tables (`Tools/flow_gen.py`,
`Tools/code_table.py`); `Proof/` contains the proof; `Audit/` contains the static decoding and schedule audits; `Scripts/` contains reproduction
tools; `Validation/` contains the final validation summary.

## Verified program

The production configuration retains the 8192-cubed FP16 shape, task scheduling
and four-stage pipeline. The upstream fixes use explicit cluster shared-address
conversion, 1024-byte backing allocation alignment, and an empty-barrier tail wait
for all four stages in both CTA loaders before exit. Shared storage remains
230400 bytes.

[fp16_gemm_8192.ptx](fp16_gemm_8192.ptx) contains 1097 instructions generated directly
by CUDA 13.2.51 for `sm_100a`. [manifest.json](Data/manifest.json) records production
source fingerprints, the toolchain, configuration and tensor maps. The generator
does not rewrite PTX strings.

## Proof entry points

- [Proof/SafeFacts](Proof/SafeFacts.lean): `safe_goal`, all Unsafe branches and source UB.
- [Proof/ProgressFacts](Proof/ProgressFacts.lean): `progress_goal`, strictly growing extensions of unfinished executions and exit of all threads.
- [Proof/BoundFacts](Proof/BoundFacts.lean): `bound_goal`, a uniform work bound.
- [Proof/ValueFacts](Proof/ValueFacts.lean): `result_goal`, actual inputs, MMA dot products and complete output.
- [Proof/Correct](Proof/Correct.lean): the four assembled into `correct`.

[Tests/Kernel/Fp16GemmProduction.lean](../../Tests/Kernel/Fp16GemmProduction.lean) checks public
statements, standard axioms and the exact specification-data whitelist. The
specification cannot depend on proof modules.

## Reproduction and validation

- `Scripts/gen_ptx.py`: compile the production DSL and record actual tensor-map encodings.
- `Scripts/validate.py`: check production sources, PTX and tensor maps; `--gpu` adds B200 execution checks.

```bash
lake --wfail build
TXVERIFY_BUILD=1 python -m pytest -q tests
python Kernels/Fp16Gemm8192/Scripts/validate.py
```

Run GPU checks in the workspace TIRx environment, preserving the inherited `PYTHONPATH`:

```bash
python Kernels/Fp16Gemm8192/Scripts/validate.py --gpu --device 0 --seeds 0 7 23 101 --launches 8
```

[verification.json](Validation/verification.json) is the sole validation summary.
When it was recorded, a clean full Lean build passed with zero warnings and all 40 Python
checks then in `tests/` passed.
B200 configuration, partial-ring, poisoned-output and asynchronous stress checks
passed. The five-round A/B median regression was approximately 6.323%, accepted
because correctness takes priority over speed. Runtime checks and the real-number
proof are separate evidence. Historical programs, baselines, development records
and raw logs are not retained in the current tree.

## Reproducing the PTX

`Data/manifest.json` records the upstream state in `source`: tirx-kernels commit
`13f586f` and TVM (tvm-tirx) commit `6a1e2e4ed`, with their repository URLs. Its `verified`
field says what was checked: the four upstream source hashes in the manifest equal the hashes
of those files at the two commits. The PTX was not regenerated and compared at those commits.

1. Check out the two commits into `tirx-kernels/` and `tvm/` next to this repository (the
   manifest keys are paths relative to that workspace directory) and build TVM-TIRx.
2. In that TIRx environment, preserving the inherited `PYTHONPATH`, generate the PTX
   (nvcc, no GPU needed):

   ```bash
   python Kernels/Fp16Gemm8192/Scripts/gen_ptx.py -o /tmp/fp16_gemm_8192.ptx
   ```

   `--tensor-maps Kernels/Fp16Gemm8192/Data/manifest.json` instead records the host's
   `cuTensorMapEncodeTiled` arguments into that manifest and needs a GPU.
3. Compare: `sha256sum /tmp/fp16_gemm_8192.ptx` against `ptx_sha256` in the manifest (and
   `sha256sum Kernels/Fp16Gemm8192/fp16_gemm_8192.ptx`, which `validate.py` also checks).
4. `Scripts/validate.py` (no GPU) checks that the committed PTX has the manifest hash, the
   shared alignment agrees with `Spec.lean`, the four upstream source hashes match the
   checkout (`--workspace`, default the directory above this repository), and the manifest
   tensor maps equal the Lean ones. `--gpu` additionally compiles and runs the production
   kernel on an SM100 device.
