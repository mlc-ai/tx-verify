# FlashKDA forward recurrence (packed batch, FP32 state)

The kernel is `_flash_kda_fwd_recurrence` of [FlashKDA](https://github.com/MoonshotAI/FlashKDA),
the second of the two kernels of its forward pass, in the instantiation for a packed batch of
variable-length sequences with a single-precision state passed in and out. This directory holds
its frozen PTX, the Lean decoding of that PTX, the specification, the kernel assumptions and the
proof that the PTX meets the specification.

**Status: proved.** [Theorem.lean](Theorem.lean) states `correct` (safety, progress, the bound
on the number of events and the result), `completed_execution` and `realizable_result`; Lean
checks them with no axiom besides `propext`, `Classical.choice` and `Quot.sound`. The
precondition is not vacuous: `Tests/Kernel/FlashKdaPre.lean` writes down a launch that satisfies
it (one sequence, one head, one token), and `Tests/Kernel/FlashKdaRealized.lean` concludes that
this launch has a completed execution with the specified result.

## Verification target

- Source: FlashKDA commit `b8a96a6db49e785ba0ee103e9d87d2588ffcc4f2`, `csrc/smxx/fwd_kernel2.cuh`
  (the kernel), launched by `csrc/smxx/fwd_launch.cu`; CUTLASS commit
  `5c149f52a436782210263fb2f19b354443a61c6a`. Template arguments of the verified entry:
  `CHUNK = 16`, `D = 128`, three input stages, two output stages, 192 threads,
  `HasStateIn = HasStateOut = StateFP32 = IsVarlen = true` (the fourth of the fourteen
  instantiations of the kernel in the compiled module).
- **The program that is verified is that commit with one added line**,
  [checks/proxy_fence.patch](checks/proxy_fence.patch): a
  `cutlass::arch::fence_view_async_shared()` before the `__syncthreads()` that separates the
  reads of the FP32 state buffer from the tile loads that reuse its memory. The unpatched
  kernel is not covered by the theorem; see "Findings" for why.
- [packed_fp32_sm100a.ptx](packed_fp32_sm100a.ptx): the 3,836 instructions that `nvcc` 13.2.51
  produces for the patched entry on `sm_100a` (no line information). It differs from the PTX of
  the unpatched source, kept as
  [checks/upstream_packed_fp32_sm100a.ptx](checks/upstream_packed_fp32_sm100a.ptx), by exactly
  one instruction: `fence.proxy.async.shared::cta` at index 1401. Hashes of both files, of the
  compiler's module and of the native code are in [manifest.json](manifest.json). No PTX text
  is rewritten after the compiler; [checks/select_packed.py](checks/select_packed.py) cuts the
  entry out of the module.
- [Ptx.lean](Ptx.lean) is generated from the PTX by `Tools/export_lean.py`.
  [Data/Decoded.lean](Data/Decoded.lean) is the Core decoder's output on it, and
  [Audit/Decode.lean](Audit/Decode.lean) checks by kernel reduction that the Core decoder
  produces exactly that program. [Data/TensorMaps.lean](Data/TensorMaps.lean) states the eleven
  tensor maps of the launch.

## Findings

Three things came out of stating and proving the theorem. The first is a defect of the kernel
with respect to the PTX memory model; the second is a property the kernel relies on that PTX
does not promise; the third is a limit of the model.

1. **A missing proxy fence (fixed by the patch).** With an FP32 state, the kernel loads the
   initial state into a shared buffer with the copy engine (TMA), reads that buffer with ordinary
   loads (the conversion to the bfloat16 copy, and the per-thread carry registers), and then lets
   the tile loads of the main loop overwrite the same bytes, with only `__syncthreads()` in
   between. PTX orders an access through the generic proxy before a later access through the
   asynchronous proxy only across a `fence.proxy.async` (PTX ISA 9.2, "Proxies"); a barrier alone
   does not. In the model the ordinary reads and the later TMA writes of the same bytes are
   therefore unordered, which is a data race, in every launch with a non-empty sequence. The
   kernel already issues this fence at its other three hand-offs between the two proxies; the
   patch adds the fourth. We do not know of hardware on which the unpatched kernel misbehaves.
2. **The elected lane must be lane 0.** The CUTLASS load pipeline checks that the thread that
   issues the tile loads is lane 0 of its warp, with an explicit `brkpt` that it compiles unless
   `NDEBUG` is defined; FlashKDA's build does not define it, so the compiled kernel keeps the
   breakpoint (three sites in the load producer). The producer is chosen by `elect.sync`, for
   which PTX fixes one leader per member mask but not which lane. With any other leader the
   kernel stops at the breakpoint. The theorem assumes the leader is lane 0 (`electZero`).
3. **Launch inputs that steer global writes.** The addresses of the kernel's global writes are
   computed from the packed-offsets array `cu_seqlens`, which the kernel reads with plain
   `ld.global`. Nothing orders the threads of two thread blocks, and the model has no clause
   that excludes a value cycle through memory, so the memory clauses alone do not rule out an
   execution in which two blocks each read an offset from the other's output store. The theorem
   assumes that these 21 loads return the launch content and makes any write of that array
   undefined (`inputReadOnly`); the proof then shows that no operation writes it. The Inkling
   kernel of this repository needs the same assumption for the same reason.

A fourth point concerns the model, not the kernel: `brkpt` now decodes as `trap` (Core note
EXT-BRKPT), so a reached breakpoint is undefined behaviour and the proof must exclude it.

## What is proved

`correct : Pre P L mem0 → Correct kernel Assumptions.all L mem0 (Post P mem0)`: every
execution of a launch that satisfies `Pre` is free of undefined behaviour and data races, a
maximal execution is complete, the number of events is bounded, and the final global memory
satisfies `Post` ([Spec.lean](Spec.lean)):

- for every sequence `s`, head `h`, token `t` of the sequence and value channel `v`, the output
  is `scale * ⟨S_{t+1}, q_t⟩`, where `S_{t+1}` is the state row after token `t` of the
  real-number recurrence `S' = S * exp g_t`, `S := S' + β_t * (v_t - ⟨S', k_t⟩) * k_t`
  ([Data/Recurrence.lean](Data/Recurrence.lean));
- the final state of every sequence and head is the state after its last token;
- no other byte of global memory changes.

The statement is over the real numbers: floating-point values denote exact reals under the
assumptions below.

## The precondition

`Pre` describes one launch as `fwd_launch.cu` makes it and the memory before it; it says nothing
about the execution. In particular:

- the grid is `(N sequences, H heads, 1)` with 192 threads per block and no clusters;
- the eleven tensor maps, the six scalar parameters and the two stride words the kernel reads
  from the parameter objects;
- number ranges for the 32-bit arithmetic, alignment of the arrays, the shared-memory window;
- `cu_seqlens[i]` is the index of the first token of sequence `i`;
- `v` and `beta` hold finite bfloat16 bit patterns (the kernel widens them with integer
  instructions);
- the workspace holds, for every tile, real numbers that satisfy the contract of the
  preparation kernel (`Recurrence.Tile.Prepared`), and the initial state holds real numbers.
  This idealizes the first kernel of the forward pass: its outputs are taken as the exact real
  quantities, as float payloads. The padding rows of a partial tile are constrained only where
  the preparation kernel determines them;
- the output and the final-state arrays are allocated, do not overlap each other and do not
  overlap any input. An in-place state update (the same buffer for the initial and the final
  state) is not covered, and neither is a `cu_seqlens` that does not start at 0 or does not end
  at `T_total`; the library accepts both.

The real inputs are float payloads in the model's memory (a byte of a payload carries the exact
real number), also where the preparation kernel writes a zero as an integer bit pattern (the
upper triangle of `Mqk`, the keys of padding rows). `Post` states the results in the same
payload form, so the final state of one launch satisfies the next launch's `Pre`.

## The assumptions

`Assumptions.all` ([Assumptions.lean](Assumptions.lean)):

- `idealArith`: `add`, `mul`, `sub`, `fma` on `.f32` and the `mma.sync` products over bfloat16
  operands with an FP32 accumulator are exact real operations;
- `approx`: `ex2.approx` and `rcp.approx` of the gate are the exact `2^x` and `1/x`;
- `narrow`: `cvt.rn.bf16.f32` of a finite value keeps its real value;
- `sharedBits`: the shift, mask and exclusive-or of the swizzled address computation read a
  generic shared pointer as its byte address ([Assumptions/SharedBits.lean](Assumptions/SharedBits.lean));
- `electZero`: an election over a full warp elects lane 0 (finding 2);
- `inputReadOnly`: the packed-offsets array is read-only (finding 3,
  [Assumptions/InputReadOnly.lean](Assumptions/InputReadOnly.lean)).

## Proof structure

The proof is in layers. Each layer is stated against the one below and checked by Lean. The
kernel's directory has about 77,000 hand-written lines and about 250,000 generated ones (the
decoded program, the control-flow tables, the thread machine and the tables of the layers above
it), written from the frozen PTX by the scripts in [Gen/](Gen/); nothing generated is trusted,
Lean checks every generated statement against the decoded program.

Words used below. A *thread block* (CTA) has 192 threads: four *compute warps* (threads 0 to
127), the *load warp* (128 to 159) and the *store warp* (160 to 191); one elected lane of the
load warp and of the store warp, the *leader*, issues the tensor copies. A *tile* is 16 tokens
of one sequence. An *event* is one step of a thread that the model orders (a memory access, a
barrier, an mbarrier operation, a tensor copy, a warp-level matrix instruction); an *event site*
is an instruction that makes one.

1. **Decoding** ([Data/Decoded.lean](Data/Decoded.lean), [Audit/](Audit/)). The Core decoder's
   output on the PTX, and the proof that the decoder produces exactly that program.
   `Audit/AssumptionSites.lean` checks the instruction positions the assumptions name.
2. **The thread machine** ([Proof/Thread/](Proof/Thread/), generated by `Gen/thread.py`). One
   machine for every thread. A state is the event site the thread is at, the words of its
   control registers, its predicates, and the values of its data registers, which the machine
   does not interpret. For each of the 836 event sites there is a transition function ("after
   this event with this returned value, the thread is at that site with these registers") and a
   theorem that the decoded program does exactly that (`Sound.lean`).
3. **The reference layer** ([Proof/Ref/](Proof/Ref/)). The thread machine derives nothing; this
   layer proves, as an invariant along each thread's trace, the closed forms of the control
   registers (the thread's role, its sequence and head, tile and stage indices, every address)
   and a ledger of how many events of each kind the thread has made, and reads off the shape,
   footprint and count of every event. One directory per phase of a thread's run: `Startup`
   (instructions 0 to 386: roles, mbarrier initialization, the scan of the packed offsets, the
   loads of the initial state), `Conversion` (387 to 621: the bfloat16 copy of the state),
   `CarryLoad` (622 to 1401: the per-thread carry registers), then the tile loop of the
   thread's role, `Producer` (the load warp, 1402 to 2105), `Compute` (the compute warps, 2106
   to 2944) or `Store` (the store warp, 2945 to 3112), and `Epilogue` (3113 to 3835: the final
   state). `Chain.lean` joins the phases into one statement about the whole run of a thread;
   `Source/` identifies the launch bytes that each tensor load copies.
4. **Protocols** ([Proof/Protocol/](Proof/Protocol/)). From per-thread facts to facts about a
   whole thread block: the eleven mbarriers are initialized once and published before use; the
   load pipeline (three stages) and the store pipeline (two stages) hand each stage back and
   forth without a fault; the conflicting accesses of the bfloat16 state copy and of the buffer
   that the FP32 state shares with the pipeline stages are ordered (by barriers, by observed
   completions of loads, by proxy fences, by the group wait); no asynchronous operation
   outlives the block.
5. **Values** ([Math/](Math/), [Proof/Values/](Proof/Values/)). `Math/` is real-number algebra
   only: the tile computation in the block structure of the compiled code
   (`Math/Fragments.lean`) equals the recurrence of the specification
   ([Data/Recurrence.lean](Data/Recurrence.lean)). `Proof/Values/` is the induction over the
   182 warp-level matrix instructions of a tile and over the tiles (`Tile.lean:
   tile_induction`): every data register of every lane holds the value the algebra says, and
   every row a lane reads back is the one the loads or the lane itself wrote
   (`StageReads.lean`, `AccRows.lean`). `Proof/Values/Ends/` does the same for the four
   stretches around the tile loop: the conversion loop, the carry loads, the final stores and
   the element stores of a partial last tile.
6. **Progress** ([Proof/Schedule/](Proof/Schedule/), [Proof/Progress/](Proof/Progress/)). Every
   wait of a maximal incomplete execution has a blocker that is earlier in a fixed schedule
   (startup, then per tile the load leader, the compute warps and the store leader, then the
   epilogue), and a thread makes at most `2705 + 100 N + 3100 T` counted events, where `N` is
   the number of sequences and `T` the tile count of a sequence as long as the whole batch.
7. **The assembly and the top theorem** ([Proof/Ref/Assembly/](Proof/Ref/Assembly/),
   [Proof/Top/](Proof/Top/), [Theorem.lean](Theorem.lean)). `Proof/Top/` derives the theorem
   from one structure of contracts about every consistent execution (`Top/Final.lean:
   Contracts`): safety class by class of undefined behaviour (14 of the 28 classes are excluded
   by scanning the decoded program: the kernel has no instruction of the kind), progress, the
   bound and the result. `Proof/Ref/Assembly/` fills the structure (`Main.lean: contracts`) by
   one case split over the phases of a thread's run (`Stage.lean`), with the exports of each
   phase, the protocols and the value layers.

Library additions that are independent of the kernel are in `Lemmas/`: the warp-level matrix
instructions (`ldmatrix`, `stmatrix`, `movmatrix`, `mma.sync`) as steps of a site machine and
their 32-lane instances (`Lemmas/Matrix/`, `Lemmas/Flow/Matrix*.lean`,
`Lemmas/Step/WarpMatrix.lean`); mbarrier rings whose loads have different sizes
(`Lemmas/Protocol/TmaSized*.lean`); and the order facts that follow from an observed load
completion (`Lemmas/Protocol/LoadObserved.lean`).

## Check it

    lake build Kernels.FlashKdaFwd.Theorem          # the proof
    lake build Kernels.FlashKdaFwd.Audit.Decode     # the PTX decodes to Data/Decoded.lean
    lake build Tests.Kernel.Statements              # statement and axioms of the three theorems
    lake build Tests.Kernel.FlashKdaRealized        # a launch satisfies `Pre` and has the result
    python3 Kernels/FlashKdaFwd/regenerate.py --check    # generated files are fresh
    python3 Kernels/FlashKdaFwd/regenerate.py --check --only-gen    # the same without Lean

`regenerate.py` has two parts: the files made from the PTX with the shared tools of `Tools/`
(`Ptx.lean`, `Data/Decoded.lean`, `Audit/Decode*.lean`, `Flow/`), which needs a Lean build, and
the generators of `Gen/` (the thread machine and the tables of the layers above it), which
`--only-gen` runs alone.

Two scripts are reading aids and no proof inputs: `Gen/simulate.py` runs the control flow of one
thread on concrete launch numbers and prints its events (how the schedules and address formulas
were tested before they were proved), and `Gen/phase_map.py` lists the event sites by phase.

## Regenerate the PTX

Apply `checks/proxy_fence.patch` to FlashKDA at the commit above, compile
`csrc/smxx/fwd_launch.cu` to PTX with `nvcc` 13.2.51 for `sm_100a` without line information
(the options are in the manifest), and run `checks/select_packed.py` on the module; the result
must have the SHA256 recorded in `manifest.json`. `regenerate.py` rebuilds the Lean files from
the PTX.
