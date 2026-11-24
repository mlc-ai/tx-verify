# tml-fa4 SM100 forward decisions

## Frozen program

The proof target is [full_p16_s1.ptx](full_p16_s1.ptx), copied byte for byte from
`txverify-archive/surveys/tmlfa4/out/full_p16_s1.ptx`. The generation log stays in
that archive because the diagnostics include host paths.

| Input or output | Revision or SHA-256 |
| --- | --- |
| [tml-fa4 source](https://github.com/vllm-project/tml-fa4/tree/75765e76a9c2c012c1f6ecd64577eb646eb4d303) | `75765e76a9c2c012c1f6ecd64577eb646eb4d303` |
| [Inkling 2 patch](https://github.com/vllm-project/vllm/blob/d664cd1e96052857aea2aa844eeba571c24758b4/cmake/patches/tml_fa4_inkling2.patch), PR 67325 | `fb911fdc186b875ad434f5f0ddc50922a19f78091a70f5853d79bde1b400767c` |
| Archived `scripts/gen_ptx_inkling2.py` | `3d4d4e19db39247d1d29d0db42f3079eb122b36cc8317f433214971f8fdaadab` |
| `full_p16_s1.ptx` | `45cf1b7068f65ab66ddf3a112994babd3f55e1bc6310ac8338fd431320a8d16c` |
| Archived `out/full_p16_s1.log` | `2639d97ef351d281e7d8a3a293fc9c03d4155e3c0cee8f6364dd159694ee48d5` |

[gen_ptx.py](gen_ptx.py) preserves the archived generator's compile arguments.
It uses FakeTensorMode and keeps the device PTX emitted by CuTeDSL. The archive
used Python 3.11.13, nvidia-cutlass-dsl 4.7.1, quack-kernels 0.5.3,
torch 2.13.0, and apache-tvm-ffi 0.1.14.post1. The PTX header records NVVM
23.0.0, CUDA 13.3.27 (CL-37800683), PTX 9.3, and target `sm_100a`.

```sh
CUTE_DSL_ARCH=sm_100a python -I gen_ptx.py --tml-fa4 "$PATCHED_CHECKOUT" \
  --layer full --page-size 16 --num-splits 1 --max-seqlen-q 8192 \
  --heads 12 --kv-heads 2 --num-reqs 1 -o full_p16_s1.ptx
```

The compile instance uses BF16 Q, K, V, and relative bias, FP32 O and LSE,
128-dimensional heads, scale `128 ** -0.5`, causal full attention, one split,
unpacked GQA, and disabled scheduler metadata. The constructor gets
`use_clc_scheduler=True`, then disables it when `self.use_tma_KV` is false
(`flash_attn/cute/flash_fwd_sm100.py:274–278` of the patched source). The
frozen entry has no cluster-launch-control instructions and uses a
512-thread CTA.

## Interface and ABI audit

Source locations below refer to the patched tml-fa4 tree unless marked vLLM or
QuACK. PTX line numbers refer to [full_p16_s1.ptx](full_p16_s1.ptx).
The exact device ABI comes from the entry declarations and the executed reads.

| Parameter | Declaration | Read bytes or use | Meaning |
| --- | --- | --- | --- |
| 0 | 12 bytes | Unread | Q tensor argument; data comes through map 9 |
| 1 | 48 bytes | 0–7, 8–15, 24–31, 32–39, 40–47 | K base, packed shape words, row/head/page element strides |
| 2 | 48 bytes | 0–7, 24–31, 32–39, 40–47 | V base and row/head/page element strides |
| 3 | 8 bytes | Unread | O tensor argument; stores use map 10 |
| 4 | 24 bytes | 0–7, 16–23 | LSE base and head stride in elements |
| 5 | 16 bytes | 0–7 | Cumulative Q lengths pointer |
| 6 | 16 bytes | 0–7 | Used K lengths pointer |
| 7 | 24 bytes | 0–7, 16–23 | Page-table pointer and batch stride in elements |
| 8 | 12 bytes | Unread | Bias tensor argument; data comes through map 11 |
| 9 | 128 bytes | Object address | Rank-3 Q tensor map |
| 10 | 128 bytes | Object address | Rank-4 ragged O tensor map |
| 11 | 128 bytes | Object address | Rank-3 bias tensor map |
| 12 | FP32 | Scalar | `scale_log2` |
| 13 | FP32 | Unread | Original softmax scale |
| 14 | FP32 | Scalar | `inv_scale` |
| 15 | 32 bytes | Unread | Opaque entry object |
| 16 | 32 bytes | Unread | Opaque entry object |
| 17 | U32 | Scalar | Number of Q heads |
| 18 | U32 | Unread | Scheduler KV-head count |
| 19 | U32 | Scalar | Batch size |
| 20 | U32 | Unread | Scheduler total-Q count |
| 21 | U32 | Unread | Scheduler split count |
| 22 | U32 | Scalar | Scheduler maximum KV blocks in L2, 800 |
| 23 | 12 bytes | Unread | Scheduler KV-head divisor data |
| 24 | 16 bytes | 0–7 | Scheduler's copy of the cumulative Q lengths pointer |
| 25 | U32 | Unread | Device split count |

- The entry declares all 26 arguments at PTX lines 17–42. The initial object
  reads and descriptor-address moves are at lines 56–74. Later scalar reads
  appear at lines 250, 279, 386–387, 4150–4151, 7361 and 9301, among other
  uses of the same words. The upper shape word from argument 1 at offset 12
  is loaded into `%r604` and unused. The lower word feeds page-size division
  at lines 436, 457, 483–498 and 596–598. `Spec.lean:128–139` binds all
  consumed words and records the accompanying shape word.
- **Runtime shape and dispatch** (`Spec.lean:46–82,161–174`). The patched
  `flash_fwd_sm100.py:516–609,1086–1109,1348–1354` and
  `tile_scheduler.py:893–945,1027–1058` define the launch and scheduler
  arguments. The grid uses the sum of packed query rows with per-request
  padding allowance, rounded into 256-row work tiles. A 512-thread CTA
  drives two stages of 128 rows. Cumulative Q rows and `seqused_k` carry
  the lengths at launch. The precondition models Inkling 2 suffix queries
  (`qLength ≤ kLength`), and bounds products used in signed scheduling
  arithmetic. It supports different lengths in the same launch.
- **K/V bytes and paging** (`Spec.lean:32–42,84–107,185–204`). The source
  `paged_kv.py:122–123,172–193,195–215,270–292` supplies the KV head view,
  page-table lookup and in-page row. PTX lines 500–523 implement division
  of the Q head by six and add the selected head to both BF16 bases.
  Lines 585–599 select a page-table word for a valid row, and preserve the
  physical page and row remainder in private storage. Lines 622–631
  reconstruct the source from element strides. Lines 644–648 use a
  16-byte copy, with source size zero for an invalid tail row. The physical
  cache may interleave K and V, and read-only pages may be shared.
- **Descriptors** (`Spec.lean:108–125,177–184`).
  `flash_fwd_sm100.py:896–903,1012–1023,1041–1061` constructs Q, O and
  bias maps respectively. PTX lines 795–807 and 832–845 show the two
  64-element BF16 subboxes and order `(d or bias column, packed query row,
  head)`. Lines 3473–3499 select FP32 subboxes at columns 0, 32, 64 and 96
  with order `(d, shifted row, head, query end)`. QuACK 0.5.3
  `quack/copy_utils.py:338–361,378–403` supplies the ragged O transform.
  Its row extent is `2^30`, its extra-axis extent is `2^31-1`, its added
  stride equals the row stride, and the base is biased down by
  `2^30 × rowStrideBytes`. The precondition admits a non-wrapping base in
  Core's natural-address geometry. Tail rows clip against the row extent
  of the descriptor. Maps carry their allocation class, including backing
  for large-class out-of-bounds requests.
- **Causal diagonal and bias** (`Spec.lean:146–158,205–209,219–224`).
  `block_info.py:26–70` and `mask.py:482–490` place row `r` at key
  position `seqlen_k - seqlen_q + r`. `interface.py:862–868` accepts the
  BF16 tensor already sheared, with 128 padded rows and 1280 packed columns.
  `shearing_bias.py:357–377,399–405` anchors each stage's bias to the
  end of the last causal key block and fills right padding with negative
  infinity. `flash_fwd_sm100.py:2388–2423,2445–2467,2498–2512,3163–3173`
  selects matching bias blocks, including a dummy first-stage load where
  the first explicit mask hides the whole block. Lines 3335–3407 pass
  the causal and residual mask on the first KV block and rely on packed
  bias masking on later biased blocks. Keys before the packed interval
  receive no bias. For a suffix query, every valid row has at least one
  visible key.
- **Numerics and outputs** (`Spec.lean:217–246`). The host computes
  `inv_scale = 1 / softmax_scale` and `scale_log2 = softmax_scale × log₂ e`
  in `flash_fwd_sm100.py:1255–1265`. Lines 3585–3601 and PTX lines
  4150–4161 use `dot + inv_scale × bias` before base-2 scaling. The ideal
  score uses both ABI FP32 values independently. Lines 4010–4026 and PTX
  lines 9938–9962 form LSE with a `lg2`, FP32 FMA and multiplication
  by `0f3F317218`. That encoding denotes the rational
  `1453635 / 2097152`. The ideal result is the base-two log-sum multiplied
  by this rational, or natural log-sum multiplied by its ratio to
  `ln(2)`. FP32 O and LSE use the patched `interface.py:429–435` and
  the vLLM adapter `vllm/models/inkling2/ops/attention.py:111–139`.
  Ordinary LSE stores use the supplied head stride and skip query tail
  rows. `Post` preserves every other global byte, including strided LSE
  padding.
- **Storage** (`Spec.lean:161–215`). The PTX requests one CTA of 512
  threads, one 1024-aligned dynamic shared area and a 128-byte, 32-byte
  aligned local area per thread (lines 14, 44–55). The bias copy at
  `sharedBase + 216064` uses a 16384-byte subbox through byte 232447.
  The launch premises allocate the working areas and the output regions
  and place the output away from immutable inputs.
- **Exp2 patch.** The `bias_ex2_emu` branch at
  `flash_fwd_sm100.py:3371–3405,3650–3678` selects the software exp2 path
  for biased blocks for which the causal and local boundaries do not
  require the hardware path. The unbiased and biased emulation branches
  call the same `apply_exp2_convert` routine. The decoded template audit
  below checks both forms.

## Decoder audit

The compiled decoder exported 9206 instructions. A Lean evaluation against
the exported program found a rule at every instruction, and all 1209
generated event sites matched `Op.isLocal`. The generator keeps local
loop cut points separate from event sites. At pc 398 the shift register
starts at 2, and pc 401 returns to pc 398 while the shifted word is below
the page-size word. PTX lines 457–482 screen signed-negative and small
inputs before entry. The first 30 shifts cannot wrap, and the thirtieth
shift reaches `2^31`.

[Audit/SpecWitness.lean](Audit/SpecWitness.lean) proves `Pre` for two
requests with 129 and 8 query rows and 145 and 19 key rows. Q stage 1 has
one valid row for the first request. Key rows 15 and 16 use distinct
physical pages, the last page has one valid key, and a visible key has
nonzero BF16 bias. The example has a nonzero local base and a padded LSE
head stride.

The kernel-checked `decode_eq` relates the raw PTX function to
the whole exported kernel. The generated certificate covers twenty raw scope
slices and their order, four slices of prepared instructions, and 145 slices
of individually decoded instructions. The prepared header is checked
separately. The proof uses the kernel evaluator and the existing decoder
rules. The local four-instruction loop proof supplies a 120-step bound
(`Audit/ShiftLoop.lean`), for the source path with at most 30 bodies.

The targeted decoder build completed 2,426 jobs with the copied dependency
cache. `DecodeResolved` and the final assembly took 5.2 s and 0.93 s,
respectively. The run also checked `Coverage`, `ShiftLoop` and `SpecWitness`.

## Numeric rules and masked blocks

[Assumptions.lean](Assumptions.lean) uses `idealReal` for the 64 decoded
CTA-group-1 BF16-input, FP32-accumulator MMAs and these FP32 forms.
[Assumptions/Audit.lean](Assumptions/Audit.lean) checks the counts.

| Form | Instructions |
| --- | ---: |
| Scalar add | 3 |
| Scalar multiply | 9 |
| Scalar subtract | 2 |
| Scalar fused multiply-add | 2 |
| Packed add | 191 |
| Packed subtract | 32 |
| Packed multiply | 256 |
| Packed fused multiply-add | 368 |
| Maximum | 230 |
| Finite comparison | 7 |
| Comparison with infinity immediate | 3 |

`approxExact` covers 450 hardware exp2s and the reciprocals at pcs 8471
and 8767. The code selects one as the reciprocal input when the row sum
is zero. The local exact log rule applies to positive finite inputs at
pcs 9061 and 9075. The BF16 rules inspect the exact instruction form and
use the lists in [Assumptions/Sites.lean](Assumptions/Sites.lean) for 256
bias widenings and 192 probability pair conversions. Core handles the
negative infinity bias encoding on widening. Probability pairs keep
ideal real payloads through the BF16 packing step, so the specification
describes ideal arithmetic through the PV MMA.

Repeated softmax can publish the literal FP32 bit pattern for one when it keeps the previous reference. The correction proof carries that word through the scalar and packed rescale paths alongside ideal FP32 results and checks that both representations decode to the same coefficient.

The FA4 software exp2 template matches sixteen segments, two defining
constants and fourteen reusing them. The audit checks that no branch
enters a segment interior. The biased branches start at pc 6059 and
the unbiased group at pc 7090. The cutoff at pc 5535 leads through the
branch at pc 5815 for the biased software path. The patch may send an
invalid query row with the negative infinity encoding through this
path. The decoded clamp takes it to -127, whose integer exponent
construction cancels the exponent bits of one and gives positive zero.
The site-scoped rule includes that encoding. Finite inputs use the same
ideal base-two rule as FA4. The run that built the numeric audit with
cached dependencies took 1.2 s for the rules and 1.9 s for the audit.

`Proof/SoftmaxNumerics.lean` gives the recurrence over descending
128-key blocks, including an empty first block and the lazy correction
threshold of eight. The per-stage causal block ends can differ by one.
For stage 0 this can require the loader's dummy bias tile before the
valid tiles and a phase count separate from stage 1. The final recurrence
returns the FP32 O value and base-two LSE multiplied by the ABI constant.

## Common startup and warp 13

The first startup cut ends with the CTA rendezvous at pc 173. The
warp-zero lane election selects the initializer and prefetch threads.
The other warps take the non-initializing path. ABI setup includes the
128-byte per-thread local stack and all parameter words and map addresses
read before the first event.

The nine startup modules contain 1,801 handwritten Lean lines and use
8,877 lines in their directly imported generated site and code modules.
The incremental build using cached dependencies took 7.0 s for the
ABI startup, 3.1 s for the warp 13 dispatch, 2.1 s for the broadcasts,
2.4 s for prefetch, 1.9 s for election, 1.8 s for barrier initialization,
1.8 s for the other warps, 2.0 s for warp zero and 1.5 s for the common
startup interface.

The first two warp 13 modules contain 906 handwritten Lean lines and
use 9,387 lines in their directly imported generated site and code
modules. With cached dependencies their targeted Lake builds took
22 s and 2.1 s. The writeback code visits the two ready barriers at
pcs 2958 and 2972. Each stage issues four 32-column boxes, commits its
bulk group, and releases its shared source after a bulk read wait.
The four-dimensional map clips the second stage of a short request at
its own row boundary. The stage releases use offsets 224 and 232
from the shared base.

## Paged K/V and ordinary asynchronous copies

The 192 static K/V copies form six groups of 32 instructions. Each second
half uses the first half's source and source-size registers with source
offset 128 and destination offset 16384. Every group is followed by a
commit and an arrive-on using `.noinc`. The arrival barriers start at
pending count 64. The kernel uses no ordinary `cp.async.wait_group` for
these copies, so the consistency extension is stated for copies tracked
by the arrive-on rather than by a group wait. A zero-source-size copy
still checks address alignment.

The geometry in [Proof/PagedKvGeometry.lean](Proof/PagedKvGeometry.lean)
gives the physical page and in-page row, aligned 16-byte source
intervals, and disjoint shared destinations within a group. Four
32-byte scratch slices fit in the declared 128 bytes. The local
memory lemmas preserve the thread owner through address lowering and
relate a read to the corresponding last write. The ordinary-copy and
arrive-on extension lemmas construct strictly larger consistent
executions. The phase lemmas link a successfully observing acquire
wait to the shared writes of copies gated by that arrival.

## Physical input padding

[Proof/InputGeometry.lean](Proof/InputGeometry.lean) verifies the
rank-three Q and bias subboxes against their byte locations. The Q map
can reach later requests' packed rows in a tail box. The bias map can
also reach the 128 allocated rows after `totalQ`. Its zero fill starts
at `totalQ + 128`.

The host allocations in `interface.py:694–703` and the vLLM adapter's
`ops/attention.py:229–236` use `torch.empty`. The shearing store at
`shearing_bias.py:499–508` masks rows beyond the query length.
`Pre.biasBytes` therefore supplies an explicit premise for the
physical padding consumed by the device. It accepts finite BF16 values
and the negative-infinity mask. The causal mask in `mask.py:478–492`
uses key limits. An invalid Q row can still run the numerical path
before the O and LSE stores clip it. An arbitrary NaN or positive
infinity there can reach the software exponential or PV operand
conversion, which requires the stated input premise.

## Synchronization assumptions

The guarded branch after each of 44 mbarrier polls is marked uniform
and uses that same poll's result. Four other polls branch without
`.uni` and are outside the agreement assumption. The existing
`commitOrderAt` rule selects pc 2537. Its Q-empty arrive-on has no
tail wait. The following Q-empty commit at pc 2541 has a matching
loader wait at pc 1893. The two MMA elections use the same full warp.

Of 60 TMEM loads, 32 have an explicit load wait and 20 pass the existing
straight-line implicit-completion checker. The remaining eight loads
are at 3428, 3446, 3463, 3481, 5112, 5129, 5146 and 5163. Their
consumers are separated from them by Bias-full polling, shared bias
loads, a 128-lane barrier and optional Bias-empty release. The last
registers of the four loads in each group are consumed by pc 3849
and 5534, respectively. The first writes of the corresponding P
storage are at 4826 and 6508. The executable site audit checks these
paths against the frozen decoded instructions.

The numerical dependency of each FMA on the completed score word gives
the latest relevant point before P overwrites score storage. The
kernel-local `delayedTmem` assumption inserts a load-completion wait at
substep zero of each of the two first P stores. Its enabled store must
be unguarded and use the audited sixteen-word format. Substep one
issues the existing store and resumes its original continuation.
The modeled wait orders the earlier score reads for cross-warp memory
reuse and allocation release. It adds this ordering at the P store,
after the intervening Bias work. This placement is an explicit model
assumption about the hardware register dependencies.

The Core hook is disabled by default. Existing assumptions retain
their event behavior. The targeted TMEM tests exercise default stores,
the new intermediate wait and store continuation, and unsupported
encodings. The site audit checks where the hook can act in this kernel.

## Startup and output-role checkpoint

The common startup and output role now connect from the actual warp
trace to the final exit. In a completed consistent execution, the
proof aligns each lane's full-mask collectives by its trace position,
derives the request from the inclusive tile prefix, and descends over
the remaining request groups in steps of 31. For a CTA with assigned
work it records both output ready waits, every store issue, both
commits and the source-buffer releases. Failed polls retry the same
site. An exhausted CTA takes the direct exit. The output drain
independently rescans the groups and proves the final ballot and
indexed shuffles. The trace proof takes write protection of the
actual cuQ bytes as a premise. The input-region separation discharges
it once the global write footprint has been confined to O and LSE.

At this checkpoint the 16 `Proof/Prologue*.lean` modules contain 3,264
handwritten lines and directly import 10,317 lines across nine distinct
generated modules. The 47 `Proof/Epilogue*.lean` modules contain 12,021
handwritten lines and directly import 10,843 lines across ten distinct
generated modules. These counts include the case splits, register frames
and trace links in each named group. The cache-warm strict build of
`EpilogueComplete`, `PrologueScheduler` and `ResultGeometry` checked
2,475 jobs. In the preceding incremental build, the top-level epilogue
composition took 1.3 s and the result geometry took 1.5 s. The
fallback scan compiled in 8.4 s in its own strict 2,452-job build.

## Termination and the global write frame

The termination bound uses the decoded loop counters. In particular,
the loader's raw signed trip word is bounded before its value is
identified with the request's logical key count. The bound therefore
covers all consistent prefixes, including those ending in a poll,
and takes no write-protection premise. The strict termination target
checked 2,712 jobs. Its declaration depends on `propext`,
`Classical.choice` and `Quot.sound`.

The output issuer proofs recover O and LSE footprints in arbitrary
consistent prefixes once the CuQ words are protected.
`outputIntent_iff_cuQProtected` includes pending writes and derives UsedK
protection as a consequence of launch separation. The ragged O descriptor
alone can yield a CuQ address at an arbitrary aligned origin, as checked
by `Audit.arbitraryOutputOriginMayWriteCuQ`. The witness leaves the origin
unconstrained by a thread execution.

The ordinary reads-from relation does not supply a well-founded
execution order. A checked two-CTA load/store example can return a
noninitial value on both loads by reading each other's dependent
write. The frozen kernel's proxy fences cover CTA shared memory, so
the forward order from an ordinary instruction to an asynchronous O
store at a global byte also does not follow from program order alone.
These facts rule out the generic induction on a first bad write.
Any proof of metadata protection needs a property of this kernel's
specific addresses or value dependencies.

Commits `a441bc25e`, `8ede81101` and `984ea35f3` trace the possible CuQ
sources. A local writeback run with the endpoint changed from 137 to 138
can place its O destination over all four bytes of CuQ in a valid layout.
The numeric certificate checks that finite BF16 inputs can yield that
FP32 bit pattern through exact normalization. Closing the same value
and address in a single `Consistent` execution remains open. With
`Mixed` and `Race` excluded, every changed CuQ byte requires an earlier
ordinary LSE writer. The LSE tail can transmit that order only within
its own correction lane or to the terminal MMA warp, so the output
warp's CuQ reads then use launch values.

## Thread interface

Each role uses a sound `Flow.Machine` over semantic observations of its checked trace prefix. Thread refinements establish event payloads and state transitions, with decoded instruction lookups checked by closed computation where available. The correction vector-address table uses one decision over the decoded guard and integer operands, and the statistics credit protocol consumes the Thread poll payload.

The protocol, safety, progress and result layers consume event payloads and abstract role state. The correction and loader input proofs replay the actual CuQ and UsedK reads under the output footprint, including a prefix ending at a read. The loader proofs use Lean’s default heartbeat budget, with the initial V admission proof split at the trip-counter checkpoint.

## Q/output shared-memory reuse

Core commit `84343118a` adds `EXT-TC-COMMIT-OPERAND-ORDER` for the Q/output
handoff. The standalone cherry-pick is `421e97b6a`
(`refs/tmlfa4/core-commit-operand-order`), based on `466a901f1`.
The adaptations of `CpAsyncArriveOrder` and `CpAsyncCompletionOrder`
remain in the branch commit because those protocol files were added during
the TML-FA4 proof. The standalone patch applies to `origin/main` at
`25f8115ea` and includes support for checking standalone EXT contracts.

The successful correction wait observes the commit that tracks the MMA operand reads.
At each actual shared operand byte, Core carries the order of earlier writes
to the waiting thread's subsequent accesses. The old kernel-local reading is
removed. The base proxy rules left this mixed-footprint pair unordered, as
recorded by `Audit.isolatedLegacyQueryOutputConflict`.
`Audit.isolatedQueryOutputOrdered` checks all four bytes of the first correction
element against the corresponding performed Q TMA writes. The audit launch puts
all actual global writes above CuQ, which supplies its output footprint.
The original proxy order also puts the four actual query operand reads before
that correction staging event. `Protocol.firstQueryOperandsBeforeStagingAt`
uses the score wait, shared proxy fence and matched statistics rendezvous.
Commits `8dc9fad1d` and `6720914d8` use both actual Q banks and all sixteen
query MMA fragments to order any overlapping tensor input intent before a
stage-zero correction write, even in a suspended execution. A pending input
is proved performed before its bytes are reused.
Commit `088e21eb1` reconstructs every staging vector element on either stage
from the actual role trace, including its precise shared address. Commit
`ea194d5fa` then establishes that every overlap of a pending tensor input
with an ordinary shared write is ordered in any consistent prefix. The
allocator and statistics writes sit below the first input byte. A staging
overlap must use stage zero. The same-byte path can continue to a tensor
output read once the correction publication orders that read.

The [upstream `overlap_sO_sQ` comment](https://github.com/vllm-project/tml-fa4/blob/75765e76a9c2c012c1f6ecd64577eb646eb4d303/flash_attn/cute/flash_fwd_sm100.py#L3677-L3679)
ties the first stage-zero correction write to completion of the top-half MMA.
The Core contract cites the PTX ISA 9.5 commit and successful wait sequence.
The new order applies only to the operand bytes. It is used consistently for
`Race`, `Mixed`, read-source constraints and coherence.

The impact review identified FA4's Q and K/V ring proofs, FP16 GEMM's input
ring proofs, and the generic TMA, mbarrier and collective extension lemmas.
The ring proofs continue to inspect the base paths to recover the original
TMA notifications. Tensor store progress selects a maximal source in the
extended byte order. FA4 and GEMM obtain those source bytes through their
existing staging writer proofs. The small kernels retain their base-order
arguments for individual accesses and use the generic extension lemmas for
progress.

## Paged K/V sources and ring order

Commit `010fb6df8` derives the first priming K pair from each active loader
lane's actual trace. The launch metadata and scratch page words select the
batch, KV head and last visible key tile. The two vectors report their
exact cache addresses, valid source lengths and launch bytes under the
output-footprint invariant. The thread interface exposes copy identities
and byte sources. Commit `58f43c108` links its completed copies to those BF16 bytes
or to zero filling for a masked row. Commit `3e7f747a8` identifies those
exact issues as members of the first published K group. Commit `9d16d0e61`
extends this to all sixteen pairs. The audited straight-line interval between
the real first and second pointer reloads contains no local write. The second
reload therefore uses the second saved page pointer. Both halves run the same
checked shuffle and copy template, with the correct source register bank and
lane selector. The first committed group now exposes the bytes of every K
vector from the launch or its mask's zero fill.

The K/V ring proof aligns the ready and empty histories by induction on the
checked generation. Earlier empty releases account for distinct ready
acquires. A publication ahead of its ready generation would depend on a
poll ordered after that publication in the ready history. A release ahead
of its empty generation would likewise depend on a poll ordered after it
in the empty history. Both cycles are ruled out by the existing dependency
check. `Protocol.LoaderReady.phaseAlignment` takes the observed lower bound
of each actual loader guard. Its prefix proof uses free parity one on all
three slots. The first waits on slots zero and one occur in the priming
packets before the recurring cursor starts at use two. Only polls through
the guarded publication contribute to that proof. The actual loader trace
discharges this premise in `Protocol.LoaderReady.actualEmptyGuardLower`.

A ready publication names the lane's immediately preceding ordinary commit.
The thread proof recovers all 32 indexed issues and shows that their
vectors in issue order are exactly the loader role's committed group.
Every earlier copy has a commit before this packet's entry. The protocol
uses the committed group of the observed generation to order its writes
before the MMA operand reads they cover.

The actual loader publication history includes exactly one K and one V
priming packet before the recurring packets. The slot and its generation
therefore recover the K/V plane. The consumer's abstract successful
acquisition counts determine the same generation for its next logical use.

A later packet's empty wait observes exactly the preceding generation.
A newer observation would require that packet's own publication in the
ready history, creating a dependency cycle even if the publication were
initially pending. The next guard therefore orders a released MMA read
before overlapping vectors in every later published group on that slot.

Use `decide +kernel` for computable decoded predicates. Instruction equality still uses the generated code table because `Instr` has no decidable equality.

At an MMA fragment, the decoded release gate has one more successful
ready acquisition than release elections. The pending acquisition's
ordinal identifies the actual poll, including in a prefix that stops
before the release. A delivered release for that same slot generation
recovers the same poll and must follow the fragment.

## Output publication and source reads

The actual warp-13 ready wait identifies the same-stage publication of
each of the 128 correction rows. Each publication follows all of that
row's staging writes and its shared proxy fence. The publication and
the wait give a byte-specific order to the pending TMA source read.
Commits `6350c32ce`, `8249e73e4` and `669e9ca5e` recover each element,
its physical address and its unique writer in the observed stage.

Commit `7de7bc42e` establishes the ordered source of every first-stage
output byte in any consistent prefix. Tensor inputs that cover it
precede that staging write. Ordinary cache copies begin at the end of
the first output stage. The second output stage overlaps precisely the
first two cache slots. Its successful final-accumulator wait observes
the actual MMA commit by `36f22a087`. A tracked operand read can carry
an earlier cache write's order through that observation. Identifying
the consuming fragment for every overlapping copy remains a separate
protocol obligation.

For progress, both output stages now supply a visible performed writer
at each backed slot. Every competing visible write provides an actual
byte. Together with guarded synchronization this suffices for an issued
output store to complete in a maximal execution, including when its
issuer has not exited. The numerical result still needs the staged
value and the order of competing writes.

## Priming V and first-round Bias

Commit `9b9dddaa0` replays the sixteen V pointer reload and copy pairs
from the K tail cursor. Commit `b6ce05c81` checks that those vectors
belong to the actual published V group and gives their completed BF16
bytes or mask zero fill once the cursor's mask frame is supplied.
Commit `ed347d80d` derives the ABI strides, mask frame and both saved
metadata slots on the actual V path. The K and V priming byte theorems
now take the same premises. Commit `6af9d1793` extends vector replay to
arbitrary issued prefixes and derives the first loader group's actual
selection from its scan and ballot. The backing proof for an arbitrary
pending packet still needs its actual source coordinates.

Commit `9218a3fbd` keeps the typed pair returned by an ordinary shared
load of two BF16 bias fragments. Its unpack proof restores each finite
value and each negative-infinity mask. The actual successful Bias poll
orders the selected TMA bytes before the reads. Matching all selected
boxes and ordering their competitors remain protocol obligations.

Commits `5bc86f37e` and `159ca63f5` recover actual first-visit Bias
notifications and prove that two distinct priming issues in one CTA
use different halves. The proof recovers the issuing lane from the
full-warp election and the half from the decoded loader transition.

## Output barriers and Tensor Memory lifetime

Commits `ed2b24036` and `83379aab8` prove that the query return objects
and both output completion and output release histories are fault
free. Each MMA completion object receives one possible notification.
Each output release object has 32 credits, one per output lane, and
each actual lane can contribute once. The fault proof counts credits
already in the history and uses the actual initializer. It applies to
prefixes before the epilogue and correction exit.

Commits `402a29e79` and `091630b71` replay the allocator's actual
initial allocation, relinquish and final release, and use the first
416-thread rendezvous to order the allocation before the actual
Tensor Memory data events. Both MMA accumulator and operand cells
use the issuing CTA's allocated columns. Commits `d74a83991` and
`bae984e2f` order the recorded load and store waits before release.
The eight biased score loads have their implicit wait at the first
probability store. Their proof uses the indexed occurrence in the lane
trace so identical events from later iterations cannot serve as its
witness. Commit `4823a342e` orders every issued MMA before release when
the scheduling offsets are preserved. The initial Q acquire identifies
the CTA's work, and the correction lane observes its terminal O1 commit
before arriving at the final allocation barrier.

## Actual barrier storage accesses

Commits `bd7e8b2fa`, `3ac7efb0a` and `15ba7ffc8` establish byte
exclusion for every write intent and every read intent except MMA
operands. The checks include pending copies and pending tensor-store
source reads. The allocator uses its four-byte slot at shared base plus
312. Correction reads statistics at shared base plus 368 or higher.
The first and recurring Bias reads are derived from their actual
softmax register states. Their shared footprint starts at shared base
plus 166912 or higher. The thread proof replays the straight-line
address segments and carries their outputs through branch targets
audited against the decoded table. The safety proof uses the abstract
Bias-read observation.

Commit `d00d325a3` proves each actual softmax probability publication
contributes one arrival credit and no transaction bytes. The code table
check compares the decidable integer and move instruction fields in one
closed audit. The first probability object also receives correction
credits for initialization or completion of the output rescale.

## Tensor Memory access bounds and lifetimes

Commit `31e837720` uses the recorded addressing events to bound ordinary
Tensor Memory data accesses to the issuing CTA's 512-column allocation.
The safety theorem checks both coverage and completion before deallocation,
using the existing CuQ protection invariant for the repeated scheduling path.
Commit `f34082b20` uses the actual shared operand ranges for the ordinary
backing and mbarrier storage disjointness checks for every issued QK and PV.

The mbarrier dispatcher classifies actual updates by their object and
uses the corresponding protocol history. It leaves only the two
joint softmax and correction credit histories to the joint protocol,
with metadata protection still needed for the statistics histories.
The safety and progress proofs share the resulting fault-free check.

Commit `d49437685` proves both joint probability histories from the
actual softmax and correction credits. The barrier safety dispatcher
and the progress adapter now need only the existing CuQ protection
for their metadata-dependent checks.

The shared lifetime check follows completed Q, Bias, and terminal O
notifications to actual exit events in the owner CTA. A completed input
notification proves every input write stage occurred, including writes
that the lifetime check first encounters as pending intents. The two
terminal O notifications use the correction lane's actual finalization
waits. The remaining asynchronous lifetime cases involve the ordinary
loader ring and nonterminal MMA notifications.

Memory conflict checking removes local bytes by the thread-private
owner and program order, and removes constants because the kernel
never writes them. Every remaining shared conflict is within one CTA.
Given the output intent frame, every overlap between two global output
writes has identical footprints, and tensor input reads are disjoint
from global output writes. Any global mixed-width conflict would pair
an output with an ordinary metadata load or paged-copy source.

Score-ready notifications use the final joint probability acquire to
find an actual softmax credit. A completed joint generation has 256
distinct credits while only 128 correction lanes can contribute. The
softmax lane's earlier score acquire recovers the chosen notification
from the score history and carries its order through the terminal
output notification to the correction lane's exit.

The active loader's Q1 return wait uses the phase reset by the decoded
drain entry. Its successful observation completes the Q1 notification.
The two query return commits are consecutive on the elected MMA lane.
The existing selected commit-order reading therefore completes the Q0
return as well. This leaves the three paged-cache effects as the only
cases of the shared-memory lifetime check. A paged-cache release is
matched to its actual ready acquisition and publication. A drain that
covers the publication's generation orders the release record before
the loader's exit.

The scalar LSE proof retains the issuing CTA's selected request and
tile through the address calculation. Two covering scalar stores then
have the same packed row, head, tile and correction lane. The remaining
unordered pairs of global writers are tensor stores of the same CTA.

The actual loader drain covers every published cache generation.
Combined with the matching ready acquisition and release history,
this proves copy writes, ready publications, and cache release
notifications finish before CTA exit. Under the existing CuQ
protection invariant, the shared-memory lifetime check is discharged.
A maximal prefix with every role exited is therefore complete.

The actual MMA issue check now covers every QK and PV descriptor,
mask, destination column, and operand address. For shared QK A,
the physical plane and the lane's successful query acquire select
the unique loader issue for that subbox, including recurring QK.
Two input effects at one shared byte can be distinct only for
different uses of the same physical Bias half. Ordinary shared
writes at one byte share a physical lane, and the initial named
barrier orders the allocator's scalar write before any result read.

The QK and PV instruction tables compare the decoded guard and MMA fields in one kernel-checked decision per table.

The actual score and probability handoffs order every MMA Tensor Memory operand read and every competing Tensor Memory write. The safety assembly uses these read and write checks under the existing CuQ protection invariant.

The statistics credit object uses the existing unit gate with each correction row paired to its softmax lane. Named-barrier handoff and the next credit acquire order both directions of every statistics overlap.
Bias tensor writes and all issued paged-copy source bytes are checked in arbitrary execution prefixes. Together with the output footprint, this removes paged-copy allocation and global output overlap cases.

The safety proof classifies ordinary global loads as four-byte CuQ, UsedK or page-table observations. Bounded words have launch backing and cannot overlap output writes once the output intent footprint is established.

Every lane's common CTA synchronization has barrier ordinal zero. The MMA warp's two later rendezvous use the same synchronous barrier ID and count, and the loader and drain have no later CTA rendezvous. The remaining barrier agreement case is confined to the softmax and correction warps.

The correction lane's statistics stage follows from the parity of its CTA barrier ordinal. Its final allocation arrival is later than the last statistics ordinal of its CTA's tile. With protected CuQ, this rules out same-warp correction barrier disagreements and leaves the softmax rendezvous case.

A stage-zero staging store cannot precede a covering MMA operand read already tracked by its O0 acquire. That order would close a byte-causality cycle through the observed commit. The opposite direction still requires a covering proxy fence after a completion observer. The mixed-access audit leaves the presence of such a fence as a separate obligation for actual prefixes.

The output staging instruction table now compares its decoded memory operands and guard with one checked decision. The proxy-fence audit enumerates the four decoded fences and recovers a real earlier stage-zero staging write for each correction fence. Consequently no correction fence can precede a causally earliest stage-zero staging write in its CTA.

The original 16-block audit distinguished the Q TMA write order from the later QK operand read.
Every same-CTA Bias fence precedes the QK banks of generation 15, and every correction output
fence has a prior stage-zero store in its own lane. At the causally earliest store there is
therefore no covering proxy fence after an observation of that QK read. The reverse direction
would cycle through the observed O0 completion and the commit operand rule. The original
counterexample applied to the proxy-only completion relation. See the approved source-reuse
reading and its checked audit below.

The first-group MMA proof checks the scan register footprint and decoded shuffle fields with
closed decisions. Recorded warp ordinals recover the selected request. The maximal-trace cursor
retains the launch ABI, the per-lane tile count, and the inclusive prefix for the indexed exchanges.

The same ballot and indexed exchange proof now covers every active MMA request. Each skipped
scheduler group adds seven actual shuffles, and selection retains the one ballot and the exact
shuffle count at the metadata boundary.

The idle CTA proof now follows every request group through the softmax, correction, MMA, loader,
and epilogue exits. The final allocation rendezvous and its deallocation use the actual
participants' arrivals and the untouched output and statistics credits. The existing counted
termination bound admits a maximal execution for every legal launch. When no tiles are scheduled,
ordered initialization and CuQ protection suffice for completion and the original result.

MMA completion uses the shared operand source condition only until the MMA records its operand
snapshot, preserving the existing general lemma for FA4. The decoded elections establish one
physical issuer per warp. Actual Q, K, and V acquire histories supply the source of each shared
byte. An overlapping stage-zero output store requires an already observed Q operand read, so it
does not compete with a pending read. This proof discharges the MMA and commit drainage
premises under the output footprint and leaves the complete-trace Q read/overwrite audit intact.

The opening Bias proof keeps the selected loader's actual expectation and two box descriptors.
The checked notification log establishes completion of the first ready phase using one arrival
and two 16 KiB credits. This lower bound also holds after the CTA reuses the Bias stage.

The same Bias credit accounting covers both stages. On the second stage the selected loader
passes the opening Q1 empty wait, then uses the request row plus 128 for its two Bias copies.
A later ready phase requires a later expectation, which requires a returned Bias buffer.
The actual named rendezvous before that return includes every participating softmax lane.
A lane that still lacks its opening Bias acquire therefore sees exactly ready phase 1.

The opening Q operand checks use the recorded softmax statistics release to order
reads against shared output staging in consistent prefixes. The initial Bias words
use the actual returned stage rendezvous to exclude later boxes. The first observed
box keeps its launch coordinates through the loader's recorded request selection,
CuQ and UsedK reads, and packed-row arithmetic. This removes the complete-execution
premise from the opening Bias word values.

## Approved source reuse and remaining correctness obligations

On 2026-11-19 the user approved taking the existing FlashMLA Core source-reuse
reading for the stage-zero output overwrite of the late QK operand. The merge
order is the standalone commit-operand patch `421e97b6a`
(`refs/tmlfa4/core-commit-operand-order`) first, then the source-reuse series
`480c340c3`, `72eb781b3`, `8e1e574ee`, `81b341d00`, `4db284922` with the
fp16 GEMM adaptations `86a6f2969` and `18ce0ce93`. Follow with `a94ac4579`
for execution extension compatibility and `1eeef55f1`, `e2807a939` for the strict build.
The resolutions preserve both readings and use the existing alloc-result model on this branch. The
FlashMLA-local proof and documentation hunks have no corresponding files here.

The actual O0 acquire observes the terminal MMA commit in the staging lane.
That commit tracks every overlapping earlier MMA in its CTA, including both
QK banks at score generation 15. The store follows the acquire in program
order. The resulting byte edge uses `EXT-TC-SOURCE-REUSE` at every overlapping
shared byte and is independent of the KV trip count. The long-query audit
retains the no-proxy-fence evidence for the previous relation and checks the
forward order of the same pair in the current relation.

The statement check audits the shared CuTeDSL exp2 template's imports. The delayed TMEM hook keeps its
original scope. The Thread proof checks its store shape using the existing
probability instruction lemma.

`Proof/Correct.lean` no longer has an `Open` premise; see "Current status" at the end.

The global write footprint (formerly `outputFootprint`) is proved from the read-only input
assumption; see "Read-only input assumption".

The softmax bias, statistics, and final allocation rendezvous have distinct
participant counts. Each decoded named barrier is aligned. After initial
allocation, a disagreement in rendezvous kind at a common warp ordinal
therefore falls under `alignedWorkBarriers`. This subsumes `softmaxBarriers`.

In correction, the matched barrier ordinal fixes the stage and statistics
generation. The initial, rescale, and terminal rounds occupy disjoint
generation intervals of the selected tile. Its final allocation arrival
follows every statistics ordinal. This reduces work-barrier alignment to
the softmax rendezvous sequence.

The counted execution bound, asynchronous drainage after exit, and assembly
of the final memory from the output slots and LSE values are already proved.

A decoded fault terminates its lane and is preserved by execution growth.
The counted bound gives a maximal extension of any consistent prefix. The
scheduled-role exit obligation and the idle-role exit proof give a normal
exit for each lane of that extension, ruling out a fault in the prefix.
This discharges `decodedFaults` using the existing progress obligation.

The observed opening and recurring cache packets and the query acquisitions
supply BF16 bytes for all completed QK inputs and the V input of PV, including
zero-filled K/V entries. The proofs use the operand bytes recorded by each
completion. This discharges the Q/K/V part of
`mmaOperands` and leaves only the P operand of completed PV in
`mmaProbabilities`. The probability publication identifies the same stored
BF16 cell for both bytes of each P element. The packed-vector proof supplies
its two reals once the observed store values are linked to the softmax replay.
Establishing those values for all observed probability stores remains open.

Appending the startup initialization fence preserves the visibility of old
reads. The startup proof now extends a consistent prefix directly, so
the idle-exit proof applies with CuQ protection in every request group.
The progress obligation `scheduledRoleExits` covers precisely the CTAs
assigned work.

The single-visit result proof supplies O for each single-visit row.
The scoped statistics callback supplies LSE for each CTA assigned a
single-visit tile. These two deductions also apply in a launch with
repeated visits. The remaining O and LSE fields cover repeated-visit
tiles.

The two loader warps now publish the opening V packet in a maximal
execution. The per-lane proof checks the paged addresses, vector masks,
zero fill and arrival completion at the ready object. For a single-visit
tile, the MMA warp returns both Q buffers and reaches the actual first V
acquire. Progress through the probability gates and the rest of the
scheduled-role exits remains in `scheduledRoleExits`.

The final MMA commit's actual V acquire has cache-use ordinal
`2 * trips - 1` for the selected request. One opening K acquire precedes the
steady loop, and each steady traversal contributes exactly one V and one
K acquire. The terminal gate returns only once, and the single-visit path
reaches it without a steady traversal.

The same ordinal determines the slot and shared operand descriptor of
each actual terminal PV fragment in both output stages.

The counted bound supplies a maximal extension of any consistent prefix.
In a scheduled CTA, the extension identifies the terminal MMA commit's selected
metadata checkpoint. Every acquisition in the selected extent precedes the
original commit, so its observation and ordinal already belong to the original
prefix. An overlapping recurring copy supplies the evidence that its CTA has
work. This orders cache writes before both correction staging and the TMA output
read. It also fixes the unique published correction byte for coincident output
writes. QK and PV cache reads order earlier overlapping copies through the
serving publication, and later copies through their empty-slot acquire. With
the existing output-footprint obligation, all shared conflicts and output-write
disagreements are discharged. The remaining `memoryConflicts` obligation covers
unbacked global metadata reads overlapping output writes.

The selected MMA lane's two cumulative-query loads and used-K load now have
bounded launch-word addresses in any consistent prefix, including a prefix
ending at the load. The proof recovers the active request in a bounded maximal
extension and matches the original observation to the unique read in its
recorded metadata prefix. Neither `metadataBacking` nor `memoryConflicts`
requires a separate check for these three reads anymore.

The normal-exit argument for decoded faults cannot replace address backing.
In `Core/Memory/Read.lean`, the initial-source case of `RfWf` imposes a byte
value only when `mem0` supplies a byte. With an absent launch byte, that case
does not force the read to return an absent byte or raise an instruction
fault. Changing that implication would require a Core contract change.
The remaining metadata proof therefore continues through the actual array
bounds.

The output warp's two selected CuQ reads now have bounded launch-word
addresses even when the execution stops at one of the reads. The common
scheduler replay follows the winning request group to tile selection, and
the decoded suffix cannot revisit either read. These observations are
excluded from both the unbacked-metadata and metadata/output-conflict cases.
The `metadataBacking` and `memoryConflicts` fields still cover unclassified
scheduler and page-table reads.

Each of the two priming scratch iterations either skips the page lookup
or reads a launch-backed page of the selected request. The proof consumes
a read only if the row guard is live and advances across the local stores
only when the target read lies later in the trace. This covers prefixes
ending at either lookup. The page-table cases of `metadataBacking` and
`memoryConflicts` now concern the warm and steady loaders.

The opening softmax path replays the actual QK loads, bias operands,
causal mask and reference calculation before the warp's packed probability
stores. Both bytes of a completed PV operand come from the same published
slot. Its opening value is a finite BF16 word, including for padding rows.
The remaining `mmaProbabilities` field concerns only values used
by completed PVs that source a later visit. The previous obligation
implies this restricted field.

For either stage of any active request, all four softmax warps of the
stage issue the bias rendezvous. The four lane-zero credits advance the
real Bias-empty barrier history. The proof finds the arrivals and
registers in the maximal execution, so it can support the progress
obligation even if the current trace stops at a rendezvous.

The MMA warp's alloc, relinquish, and dealloc are its collective ordinals
zero, one, and two. Their operands agree across the warp, and a lane's
exit covers all three ordinals. The epilogue and loader warps issue no
Tensor Memory collectives. The remaining `alignedTensor` obligation
covers same-ordinal agreement and exit coverage in the softmax and
correction warps.

The warm and steady page lookups use the same two-slot replay. The
actual shuffle ordinal locates the traversal. Its live-row guard fixes
the page address, and leaving both slots before a later lookup requires
advancing the shuffle ordinal. This covers each recorded page-table
lookup, including a prefix that stops at the read. The remaining
`metadataBacking` and `memoryConflicts` cases concern CuQ scheduler
and drain scans.

The first output-drain lookup reuses the selected writeback cursor.
The writeback frame preserves the sentinel guard and the lane's CuQ
address inputs. In both guard branches the suffix after that slot cannot
return to the lookup. Thus every recorded first drain read, including a
prefix stopping at the lookup, is covered by the lane's launch word.

The thread lookup classification exhausts the used-K and page-table
reads. Their launch backing restricts the remaining unbacked metadata
class to CuQ reads, with the already established entry, geometry, and
first output-drain lookups excluded.

The active softmax lane reaches its opening statistics arrival and
returns from the named barrier using its warp's arrivals. The recorded
opening score and bias inputs then determine the first delayed tensor
load wait and all four packed probability slices. Progress consumes
thread cursor witnesses. The decoded addresses, register facts, and
instruction replay live in the thread proofs.

Every active softmax lane reaches the first probability credit for
either stage. The thread witness identifies the three main packed P
stores and the returning store wait at their Tensor Memory ordinals.
Those observed stores supply the stage's first main-probability arrival.
The separate tail publication and its consumers remain to be proved for
maximal executions.

The first probability visit reaches the fourth packed store, its tail
store wait, the full-warp barrier, and the election. The progress witness
uses the real election event in each lane. The elected lane's arrival at
the tail object remains a separate step.

Each subsequent output-drain request group consumes the actual optional
read and seven shuffles. Replaying the scan retains the trace intervals
and shows that every recorded read addresses a bounded CuQ word. The
first down shuffle precedes these lookups, and the terminal suffix
cannot reach them. For an unfinished prefix, the counted maximal
extension and the existing scheduled-role exit obligation give a
completed trace with the same read. This removes the output drain from
the two remaining metadata safety obligations.


A correction lane has covered its final Tensor Memory collective when
the terminal load wait returns. That return requires an actual event at
the same ordinal in all peer lanes. Agreement at that ordinal
identifies their terminal wait, and their decoded suffix contains no
further Tensor Memory collective. This discharges correction's exit
coverage and reduces its remaining part of `alignedTensor` to station
and operation agreement. The operands of matching correction operations
are derived from their actual addresses and instruction forms.

The elected lane in each softmax warp supplies the first tail-probability
credit at its stage's physical barrier. The four distinct warp credits
advance that object's phase in every maximal execution of a scheduled
CTA. This provides the opening tail gate for later progress proofs.


The selected softmax tile determines the work rendezvous at each ordinal.
Each bias rendezvous pairs with its statistics arrival. The actual loop
counters give the number of repeated biased visits, and the terminal
statistics and allocation arrivals follow the plain visits. An
unfinished prefix keeps its recorded ordinals in a maximal extension.
Using the existing output footprint and scheduled-role exit obligations,
the two lanes in a warp therefore agree on the rendezvous at any common
ordinal. This discharges `alignedWorkBarriers`.

In every maximal execution, an active correction warp reaches the tile
selected by its actual scheduler events. The replay follows arbitrary
31-request groups, the selection ballot, the optional prefix shuffle,
and the tile-count shuffle. The resulting thread cursor retains the
recorded prefix for progress through the selected request.

The MMA cache-ready replay now retains failed attempts as well as
successful waits. Each attempt has the slot and phase for the count of
earlier successful waits. At a common poll site, differing release
election counts give an actual dependency from the earlier poll's lane
to the later poll. Equal counts fix the same physical object.
The remaining `pollObjects` obligation concerns loader waits.

Later plain and biased softmax replay now recovers the recorded score,
bias, exponential, and probability stores at the selected visit. The
same replay recovers correction's packed rescale inputs. The remaining
numeric obligations require showing that the maximum carried into each
later visit is the one published by the preceding visits.

Induction on the observed softmax store history now recovers the maximum
carried into each plain and biased rescale from the actual opening seed
and preceding publications. This proves that both words of each recorded
rescale store are finite F32, including in a prefix that stops at the
store or a padding row. The proof uses the existing output footprint and
discharges `rescaleValues`.

The same recorded maximum history supplies the carried reference at the
plain and biased probability stores. The actual committed PV operands
are finite BF16 in the opening visit and every later visit, with the
existing output footprint. This discharges `mmaProbabilities`.

Correction's actual ballot order and values determine its rescale
schedule at every Tensor Memory ordinal. The selected request fixes the
number of ballots before finalization, and the finalization trace fixes
the remaining slots. This proves correction's collective slot agreement
for every consistent prefix and any trip count. The remaining
`alignedTensor` obligation covers the softmax warps.

Every recurring loader poll retains its actual ring cursor, including
failed retries. At a common site, equal shuffle ranks fix the same
request round and physical slot. Unequal ranks give a dependency through
a returned warp shuffle. The three loader drain polls agree on the
idle cursor or the final cursor determined by the selected trip count.
This also covers prefixes by preserving the recorded polls in a
completed extension. With the MMA and fixed-site comparisons, this
discharges `pollObjects`.

The loader and output schedulers now retain the actual optional CuQ
lookup when they revisit the scan for another request group. The group
cursor fixes the launch word, and the intervening shuffles exclude
another lookup before the next group. The metadata-backing and memory
conflict cases therefore exclude these two lookup sites, including
lookups recorded in incomplete prefixes.

The selected softmax tile fixes how many initial, biased and plain
visits each lane runs. A replay of its complete trace identifies the
Tensor Memory operations at each collective ordinal, including the
implicit waits on the biased and opening paths. A completed extension
preserves the records and exit markers of a consistent prefix. This
gives softmax operand and exit agreement, completing `alignedTensor`.

The first loader drain lookup retains the launch CuQ base and lane
index from the actual selected request. The decoded bound check
restricts the read to the lane's launch word. This excludes the first
loader drain lookup from both outstanding global metadata cases.

The opening main probability barriers reach phase one in maximal
executions. For each stage, the proof counts the actual softmax
credits and the actual correction startup credits. Correction reaches
its first two named statistics notices and then the first rescale
or terminal wait according to the selected trip count. Its returned
statistics notices advance the first reuse slot, and also the second
slot for a single-visit tile. Later statistics reuse and role exit
remain in `scheduledRoleExits`.

The loader's later drain and the MMA fallback and drain lookups retain
the launch base and the guarded lane index through each repeated
group. The proofs account for the terminal sentinel and exclude
skipped reads. All loader and MMA metadata addresses are now bounded
by the launch arrays. The remaining metadata cases are softmax and
correction fallback and drain lookups.

For each softmax row, the opening probability packet and the first
recurring head retain the actual denominator and the reference
maximum. An individual biased or plain visit now derives its logits
from the observed score operands and launch bias, and records the
updated FP32 denominator, statistics store and probability
publication. The trace starting at one visit's publication still
has to be connected to the next visit and to the terminal handoff.

The repeated output proof now uses the actual correction acquire and
its matching softmax statistics publication to recover the rescale
factor for each PV carry. The terminal wait supplies the final
numerator and denominator for normalization and writeback. The
remaining result input is one connected softmax replay for the same
row, covering all its recurring probability and statistics packets.

Softmax and correction fallback use the recorded optional load and
the seven collective exchanges of each request group to bound every
lookup. The final exhausted branch rules out another fallback read.
This leaves the first and later drain lookups of the two roles in
the metadata-backing and global conflict cases.

For an active output warp, both correction publication cohorts imply
that the warp completes all eight TMA stores, waits for both bulk
groups, returns both staging credits, and exits after draining any
number of scheduler groups. The remaining output-warp progress
obligation is to derive the two correction cohorts in a maximal
execution.

The first and repeated softmax and correction drain lookups preserve the
launch CuQ base, lane index, and batch bound. Their group replay accounts
for an arbitrary number of requests and for the terminal sentinel.
The decoded metadata lookup table is now exhaustive against the bounded
launch words, so `metadataBacking` has been removed from `Open`.

The remaining global-conflict cases require a metadata reader outside
the launch input regions. Exhaustive metadata replay excludes both
conflict directions using the existing output footprint invariant.
This discharges `memoryConflicts`.

An exited correction lane in a scheduled CTA has published both output
stages. Applying the published-cohort progress proof to all correction
rows yields output warp exit for each scheduled CTA. The
`scheduledRoleExits` field now covers the loader, MMA, softmax, and
correction roles.

An active softmax lane at the terminal statistics cursor writes both
statistics words and publishes them in a maximal execution. The
recorded softmax publications and paired correction waits release the
terminal synchronization at the selected tile's actual trip count.
The repeated O and LSE assembly now share the same row history and
terminal publication. The remaining result proof connects each
repeated visit and its numerical state to that history.

The recurring softmax replay now assembles the first denominator, every biased
and plain visit, and the terminal drain along the same lane trace. Each step
uses the actual probability stores, acquired statistics credit, and retained
denominator and reference. The completed row history proves the repeated output
bytes through the recorded PV and rescale sequence. This removes
`repeatedOutputValues` from `Open`.

The terminal correction stores use the final denominator and reference from
the same recorded row replay. The replay supplies the repeated LSE write
values for every completed execution and removes `repeatedLseValues` from
`Open`. The footprint and active role exits remain.

The opening softmax path now records the leader's tail probability credit
and the peers' local bypass at the same join. The statistics phase at a
suspended first acknowledgement is bounded by the actual poll count. Stage
zero can advance for any scheduled tile, and stage one currently has a
progress proof for a single visit. The acknowledged row computes its real
first denominator and takes the decoded loop decision. Both softmax stages
publish their final statistics on a single-visit tile. This leaves the
recurring stage-one acknowledgement and the repeated and final role progress
in `scheduledRoleExits`.

The scheduled MMA warp now reaches the full stage-zero terminal PV packet
for a single KV visit. The value and probability objects advance to their
first physical generation, the real polls acquire those generations, and
one elected lane makes all eight fragment issues. The proof retains the
warp's actual continuation for the stage-one tail. It still needs stage
one, output commits, and the subsequent drain to discharge a scheduled exit.

A one-record extension of a CuQ-protected prefix preserves all CuQ read
bytes. A changed read requires both the reading record and the actual
write's issuer to be new records. This leaves cycles involving several
records outside that argument. The CuQ audit also checks a source
replacement that preserves full consistency when a performed O byte
covering CuQ exactly matches the recorded load byte and all retained
launch sources agree.

The local 137-to-138 address witness now replays the load with the tagged
floating value from the numeric witness. It reaches the same actual
writeback issue footprint. Turning that local witness into a consistent
prefix still requires the producer, its synchronization, and the actual
TMA write effects in the same execution, with reads-from for every
affected load. The evidence does not discharge `outputFootprint` or
establish a counterexample to `Correct`. The user-approved read-only input
assumption now excludes such cycles and discharges `outputFootprint`
(section "Read-only input assumption").

In a single-visit tile, the MMA warp records both terminal PV packets and
both output notifications. Completing their tracked work forces the two
output objects to phase one. The opening softmax ledger has exactly one
publication before the final stores. The first correction terminal wait
shares that named generation and both real reads return its paired producer's
words. The correction progress proof carries the returned cursor, including
when the original maximal prefix could have stopped at the named barrier.

The recurring softmax paths have a common first-score acquire and Tensor
Memory collective proof for biased and plain heads. The initial head comes
from the actual opening path. Subsequent use requires the producer's ready
generation, same-warp participants, and written Tensor Memory values.
An already reached terminal softmax cursor can issue the actual first drain
shuffle, and final allocation arrival by the whole warp suffices for its
exit. Reaching that allocation arrival from the remainder of the terminal
rescan is still part of `scheduledRoleExits`.

For a single KV visit, all correction lanes return the first terminal
statistics credit at the named wait's generation. The same lane computes
its guarded reciprocal and acquires the first accumulator from the actual
MMA completion phase. The output trace also shows that either staging
credit follows that stage's successful ready acquire, including the
writeback path in which some destination boxes are empty. For repeated
scores, the same-warp load cursors jointly supply collective participation
and the plain round's explicit load wait.

From a same-warp repeated score frontier, all four loads now return their
actual register pairs. The ordinary round computes its maximum and rescale
coefficient and records its statistics write and named arrival. The biased
round observes the next Bias generation and consumes all 64 shared vector
words when their decoded address frame is available. Closing the recurring
producer loop and handing off the full biased address frame are still part
of `scheduledRoleExits`.

A correction row still at its staging poll has not published its own
ready arrival. The output warp can return the slot only after observing
every row's arrival, so that slot still has its initial free phase.
Using this phase and the recorded MMA output phase, each single-visit
correction row issues its first real eight-word load at collective
ordinal zero. All lanes supply that ordinal, and the terminal PV
provenance gives finite values for the recorded load. Each lane then
issues its explicit warp wait and computes the first normalized pairs.
The writeback stores and remaining chunks are still part of
`scheduledRoleExits`.

The first correction wait has ordinal one in a single visit. All lanes
record that wait, releasing the normalized vector stores. A general
vector progress lemma now steps through each store's four observed
elements and retains the actual continuation. The first vector writes
the expected four normalized values into the decoded shared slot.

Both normalized vectors of the first single-visit correction chunk now
write all eight actual values. The next cursor retains the address
table for the subsequent chunk. The load-to-products and products-to-writes
steps also apply to any decoded chunk once its warp collective is released.

The single-visit MMA warp retains the protected scheduler inputs across
both output commits. Its drain reads the initial CuQ lane words and
records the next down shuffle at the common warp ordinal. Separately,
any MMA warp that has relinquished and has the softmax and correction
allocation arrivals can deallocate and exit.

The terminal softmax rescan can proceed from the returned down shuffle
to all five up-scan rounds and the terminal group totals. The startup
guard supplies its lane predicate. A scan that has reached exhaustion
and consumed the final statistics credits records the allocation
arrival. The intervening group-selection loop remains in
`scheduledRoleExits`.

The single-visit correction warp uses its observed load and wait ordinals
to iterate the staging transition through all sixteen chunks. Stage zero
records the proxy fence, the accumulator credit and the ready publication.
That publication leads the actual lane to the second named rendezvous.
The matching softmax row supplies its two terminal words. The lane returns
the statistics credit and completes both accumulator and staging acquires.
The remaining writes and role exits stay in `scheduledRoleExits`.

The softmax rescan now recovers its guard from the real opening scheduler
and broadcasts the first group's exact total. The following transition
selects that group or opens a new one. An arbitrary loop entry either
records exhaustion or reads the next group's protected CuQ words. The
remaining post-read loop and final ballot are still separate obligations.

Both single-visit correction surfaces are now staged in full and made
visible by their actual ready releases. The correction lane retains both
row statistics and computes the packed LSE base for the selected request.
The remaining LSE effects and the final correction drain still belong to
`scheduledRoleExits`.

Softmax's terminal scan now iterates arbitrary groups using the number of
remaining requests, with the exact CTA interval and lane counts for a
selected group or the exact exhausted bound. The final selection
rendezvous and allocation arrival remain to be connected for a selected
group.

A selected softmax terminal group now advances through the actual warp
ballot and both selected-index exchanges. From that completed scheduler
state, the two statistics credit phases enable the allocation arrival.
The matching CTA deallocation enables the actual lane exit. Connecting
the retained ABI frame and terminal phase from the preceding search
still belongs to `scheduledRoleExits`.

The actual single-visit correction lane advances through both LSE
calculations and their global row guards. The terminal softmax witness
carries nonnegative mass and a finite maximum whenever the mass is
positive. The zero-mass local path selects negative infinity. The
published surfaces also suffice for the single-visit output warp to
exit. The correction final arrival now accepts either free-slot parity
at the terminal checkpoint. Reaching that checkpoint after the
correction lane's terminal rescan remains in `scheduledRoleExits`.

A loader warp at its terminal drain checkpoint now consumes the final
cache and query releases and records its lane exits. Warp 14 publishes
the elected query notification and warp 15 bypasses that notification.
The proof accepts each observed retirement parity. Establishing the
scheduled warp's terminal checkpoint and released generations remains
in `scheduledRoleExits`.

The single-visit correction warp now reads the protected CuQ words in
its terminal scheduler and performs the actual first down shuffle.
The earlier recorded scheduler supplies its original lane guard and
warp ordinals. The proof uses the single-visit bound to rule out a
rescale ballot in that interval.

The single-visit softmax scheduler now runs from its actual denominator
through any number of terminal request groups. It retains its launch
operands and derives its collective ordinals from the actual trace.
The terminal allocation arrival still uses named release and
correction-credit availability observations.

The single-visit softmax warp now records the final allocation arrival
from its actual two correction credit cohorts and their matched named
generations. After the row-role arrivals, the single-visit MMA warp
can deallocate and exit. Its terminal scheduler searches any number of
request groups and supplies the real relinquish event. The loader's
single-visit opening publication reaches its first terminal endpoint
exchange, with the protected request words and live loop frame.

The correction's first terminal group now accumulates and broadcasts
its real tile counts. The decoded branch selects that group or advances
to the later-group search. All 32 actual output-free credits imply that
the staging object reaches phase one. The remaining role paths stay in
`scheduledRoleExits`.

In each single-visit CTA, the output warp's two actual release cohorts
advance both staging slots. Correction searches all terminal request
groups, consumes its last ballot and index exchanges, and acquires the
released second staging slot before its final allocation arrival.
Together with the softmax arrivals, this forces the allocator to
deallocate and both row roles and MMA to exit. The output warp's own
exit follows from the published surfaces.

The loader can follow its first terminal group's actual prefix scan,
ballot and index exchanges to retirement when the final cache and query
slots are available. Scheduled loader cases and repeated KV visits
remain in `scheduledRoleExits`.

For a single KV visit in any request group, the MMA warp's actual K, V
and second Q commits advance the loader's final drain objects. Together
with the first-group scan this proves both loader roles exit for a
single visit in the first request group. For repeated visits the MMA
warp reaches its steady loop and issues its first eight PV slices once
the V and main probability objects reach their required phases.

All roles now exit single-visit CTAs in every request group. Later
groups use the loader's actual scans, selected exchanges and retirement
waits. The top-level proof selects the assigned batch and dispatches a
single visit directly to this result. The remaining `scheduledRoleExits`
field now asks only about tiles with at least two KV visits. The user
assigned the separate output footprint proof to another branch.

On repeated visits, a reached softmax warp issues the first three
packed BF16 probability stores from its actual affine and exponent
results, including the biased path's delayed load wait. After the
store wait it releases the main probability credit. The MMA warp
can issue a QK packet, commit at a recurring election ordinal, and
advance its K ring and probability parity at the loop backedge.
These steps still require the matching producer or consumer phase.

On a repeated tile, the first rescale wait has named-barrier generation
one and follows exactly one scheduler ballot. Each correction peer has
joined that generation. A second publication from each paired softmax
lane therefore releases the wait. The lane reads the producer's finite
coefficient, participates in its first actual rescale vote, and reaches
the skip or tensor-update branch selected by that vote.

For a repeated cache use, 64 loader publications at the required counts
suffice for delivery and readiness at an MMA lane that has yet to
consume that use. The corresponding probability result uses the 128
softmax and 128 correction credits for main P, or four elected warp
credits for tail P. The later score commit excludes an extra unseen
generation. From reached MMA elections with the live operand frame,
both recurring QK packets issue their eight slices and score commits.
Once the last V and probability slots are ready, the final PV packets
return Q and V and commit both output stages, then reach relinquish.

For repeated visits, each softmax warp now carries its resident
denominator, coefficient and continuation registers through all four
probability stores, both credit releases and the correction acknowledgement.
The opening producer cohorts seed the probability wait counts. With the
matching producer phases, the steady MMA body reaches its next visit or
its final drain, and the loader counter and ring advance across warmup.
The scheduled exits for these repeated visits remain open.

A nonzero correction rescale ballot issues eight full-warp load, wait and
store groups and a final store wait. The accumulator words and factors
come from the recorded execution. Either ballot result returns both stage
zero credits and reaches stage one once the paired softmax producers have
published again. Both stages now have a reusable statistics read and a
release proof parameterized by the actual publication ordinal. For the
loader, the terminal rescan accepts the final use count of a repeated tile.

A full recurring MMA visit preserves its Q bank, V descriptor and trip
counter through both QK and PV packets. The loader's first used warm K
slot acquires its actual generation after the page refresh. For both
biased and unbiased repeated scores, the affine calculation produces its
actual statistics arrival and the state consumed by the probability
stores. A named arrival at the execution tail still requires its group
record before the producer can continue.

The opening MMA trace supplies its complete Q bank. A repeated visit
requires the producer phase only while its actual wait remains pending.
The full MMA loop and drain now reach relinquish given those producer
frontiers and final slot phases. Correction starts the loop at generation
one for both statistics groups. Its final decrement reaches the existing
terminal statistics cursor with the preserved tile frame. A plain softmax
warp can record its statistics group on the same lane traces before
resuming its affine calculation.

For any number of KV blocks, each paired softmax statistics publication
advances the reached correction warp through one rescale stage. Both
slots return with the exact vote, tensor and named-barrier counts.
Induction on the remaining trips now gives the first terminal statistics
cursor from the paired publications. Producing the publication cohorts
and finishing the terminal path remain part of scheduledRoleExits.

When the paired producers have published the required generations, all
correction lanes enter finalization with common tensor and ballot ordinals.
For either repeated softmax route, the probability stores and denominator
continue on a maximal history with identical lane traces and mbarrier
objects. The loader's two first warm K pointer saves preserve each
other, and the recurring MMA consumes V and main P at their actual counts.

For scheduledRoleExits, use actual final softmax row writes and the two
terminal MMA issues to carry a repeated correction lane through both
staging surfaces and the LSE tail. Peer tensor ranks include the actual
rescale ballots for any number of KV visits. Inside the recurring
producer loop, consume the V and both stage-zero P cohorts before the
next K wait, and preserve physical mbarrier histories across the biased
softmax rendezvous.

For scheduledRoleExits, retire both row roles and the allocator from the
actual final producer row frames, MMA output issues, and warp relinquish.
For arbitrary KV length, each of the 128 correction lanes returns both
terminal generation credits. Actual softmax and correction warp ordinals
then carry the scheduler through every request group to deallocation and exit.
The remaining progress argument must produce these terminal inputs and
finish the loader.

For scheduledRoleExits, drive the correction consumer by published
generations. It reaches a given rescale round from earlier publications
alone. The first stage returns the other stage's statistics slot before
that other stage publishes again, releasing its opening denominator.
The MMA steady loop now starts its exact wait counts at the actual opening
and accepts delivered cohorts across arbitrary KV lengths.

For scheduledRoleExits, force the complete first warm K packet from the
two real loader warps, including both pointer reloads, all sixteen vector
pairs, and the final ready arrivals. Each later main-P cohort uses the
actual priming and recurring correction releases, paired with softmax.
MMA retirement also returns the exact K and V generations.
For scheduledRoleExits, obtain the first steady MMA visit directly from
the two real loader warps and the opening probability cohorts for every
tile with at least two KV blocks. The following score notification fixes
the physical phase for any lane still waiting at its own generation.
Both loader warps also reach their first warm V or Bias acquire gate.

For scheduledRoleExits, check poll readiness at the returning lane's
actual ordinal. An already-consumed generation requires no assumption on
the barrier's later phase. On every tile with two or more KV blocks the
first four softmax warps acquire the second score and resume the biased
load path with their opening denominator intact. The other stage reaches
the same point after its opening statistics acknowledgement.

For scheduledRoleExits, retain the actual tensor count through the P-tail
election, acknowledgement, denominator and next score poll. All lanes of
a stage-zero warp load the four score quarters at the resulting ordinals.
Warp 15 also acquires the first warm V slot using the actual opening K
return. At any Bias generation, the expectation plus the two issued halves
advance the ready phase. Each live participant bounds it by its own
rendezvous count plus one.

For scheduledRoleExits, index a blocked Bias wait by its lane's named
rendezvous count. The second score return has exactly two successful
score polls and the packed row has exactly one Bias rendezvous. Failed
retries leave that ordinal unchanged. Given the two-piece loader packet
at this generation, all 128 first-stage lanes pass the Bias acquire, read
their vectors and reach the affine body in one trace-preserving history.

For scheduledRoleExits, keep the decremented block index and score parity
in the first recurring row. With the second stage-zero Bias generation
delivered, every first-stage lane produces its rescale notice. These
notices release the other stage's opening acknowledgement and second QK
acquire. The proof applies to every tile with at least two KV blocks.

For scheduledRoleExits, derive the second stage-zero Bias delivery from
warp 14's opening return, its actual warm expectation and the two
16 KiB transactions. The first-stage rescale publications and second QK
loads on all eight softmax warps now follow for every multi-block tile
using the existing output-footprint obligation. A later expectation
already witnesses the lower phase bound.

## Read-only input assumption

**Decision.** The user approved a kernel-local assumption that the
kernel's input arrays are read-only. This is the standing resolution for a
value cycle through plain loads of inputs, the same resolution as the
Inkling kernel's `Assumptions/InputReadOnly.lean`. It is
`Assumptions.inputReadOnly` (`Assumptions/InputReadOnly.lean`), the last
entry of `Assumptions.all`. It has no Core constructor and no Core clause,
and it is modelled on `Assumption/NcReadOnly.lean` (ASM-NC) for plain
`ld.global`.

* `wf` removes executions. A plain read (`.rd`) at one of `inputReadSites`
  returns, at every byte of an input array whose launch content is known,
  that byte. An input byte (`Assumptions.InputByte`) is a byte that
  `Params.inputRegions` names for some `P` with `Pre P L mem0`. The
  constraint mentions only bytes that `mem0` specifies, so it does not use
  `X.initialByte`.
* `ub` is only stricter and does not mention the reads. It is undefined if
  an issued ordinary or asynchronous operation of the execution writes
  (`X.Intent w a true`) an input byte.
* The statement is generated from the sites (`siteText`) and lists every
  pc. It names the input arrays (Q, the sheared bias, the K and V caches,
  `cu_seqlens_q`, the used key lengths and the page table), says that the
  kernel never writes them, and cites the contract of a CUDA
  `const __restrict__` input.

The constraint is limited to input bytes, unlike the Inkling form, which
constrains every specified byte that a site reads. The Inkling proof shows
that every site reads an input byte. This proof does not show that for the
page-table and scan loads, so a site read of any other byte keeps the
model's reads-from rules alone. The constraint then covers exactly the
bytes that `ub` protects.

**Why `wf` cannot hide a kernel that writes its inputs.** Suppose a run on
the hardware writes an input byte, and take the first such write in real
time. Before it no write has touched an input byte, so every read at a site
before it returned the launch content of the input bytes it read. The
prefix of the run up to and including that write satisfies `wf` and
contains a write of an input byte, which is `ub`. `Correct.safe`
(`Core/Assembly/Correctness.lean`) says that no consistent execution is
`Unsafe`, and `Unsafe` contains an assumption's `ub`. `Consistent.thr` asks
only `Produces K A L g (X.tr g)`, a finite run with no completion
requirement. `Maximal` and `Complete` are used only by progress and the
result. So the prefix is covered and the theorem would fail: the assumption
cannot mask a kernel that writes its inputs. The premise, as for every
safety claim, is that the real-time prefix is a consistent execution of the
model. This is why `ub` does not mention the reads. With `NcReadOnly`'s
form, a run whose read of the written byte comes after the write has no
`ub` on the prefix through the write, and `wf` removes the full run.

**Why it is needed.** The O tensor stores and the LSE stores have addresses
computed from loaded `cu_seqlens_q` words, and the kernel reads those words
with plain `ld.global`. CTAs do not synchronize, and Core has no
no-thin-air clause. So Core admits an execution in which a CuQ load of one
CTA returns a byte of another CTA's output store, whose address came from
that CTA's own wrong CuQ load. The CuQ audit above shows that a
one-record extension argument does not exclude a cycle of several records.
With the assumption every CuQ load returns its launch word, so no such
cycle exists.

**The sites** (pc, PTX line of `full_p16_s1.ptx`) are all 37
`ld.global.b32` instructions of the program. The program has no other load
of global memory and no generic load.

| Array | Parameter | pcs | PTX lines |
|---|---|---|---|
| `cu_seqlens_q` | 5, 24 | 186, 245, 381, 382, 1750, 1805, 1940, 1999, 2112, 2113, 2653, 2707, 2776, 2835, 2953, 2954, 2989, 3043, 3110, 3169, 3369, 3370, 7621, 7677, 7761, 7821, 7955, 7956, 9089, 9144 | 258, 320, 462, 463, 1975, 2033, 2216, 2278, 2397, 2398, 3139, 3196, 3272, 3334, 3458, 3459, 3508, 3565, 3638, 3700, 3906, 3907, 8442, 8501, 8601, 8664, 8804, 8805, 9973, 10031 |
| used key lengths | 6 | 385, 2116, 3373, 7959 | 466, 2401, 3910, 8808 |
| page table | 7 | 503, 946, 1416 | 590, 1096, 1621 |

`Proof/InputRead.lean` checks the sites with `decide +kernel`:
`kernel_nonShared_reads` (every load that names global memory or no space
is at a site) and `kernel_sites_global` (each site is a load of global
memory). `read_site_global` then places every read event of global memory
at a site, using `fires_read_global` from `Lemmas/Flow/AccessLocal.lean`.

**What is proved with it.**

* `inputReadValue`: every read of an input byte returns its launch byte, in
  every consistent execution. `cuQWordReads` and `cuQReadsFromLaunch` give
  this for the `cu_seqlens_q` words.
* The correction LSE chain (`Correction.lseStoreSpecs`, the first-group and
  fallback scheduler scans, the trip reads) takes the CuQ words from
  `cuQWordReads` and no longer takes CuQ protection. `Thread.lseWriteShape`
  gives the LSE write shape without a premise. The O tensor stores already
  had `Thread.Output.issuedBoxOfCuQReads`. The correction, statistics and
  barrier lemmas that took `DrainCuQProtected` only to pass it to this chain
  no longer take it. Lemmas that still use CuQ protection keep the premise,
  and `drainCuQProtected` supplies it for every consistent execution.
* `outputIntentFootprint` (`Proof/OutputProtection.lean`): every consistent
  execution satisfies `OutputIntentFootprint`. `drainCuQProtected` follows
  from launch separation. **`Open.outputFootprint` is removed**, and
  `correct_of_open` and its two corollaries use the theorem.
* `OutputIntentFootprint.noInputWrite` (`Proof/OutputFrame.lean`): the
  `ub` never holds in a consistent execution. Every global write is in the
  O or LSE region. `Pre.outputs_pinned` (`Proof/OutputPinned.lean`) shows
  that the two regions are fixed by the launch: the head count is
  `param_17`, the total query count is the row extent of the Q tensor map
  (`param_9`), the O base is the O tensor map's base (`param_10`), and the
  LSE base and stride are bytes of `param_4`. Every such `P` keeps them
  apart from its inputs (`Pre.separate`). `noAssumptionUb` takes this as a
  premise, and `Safety.unsafeCases` supplies it.
* Progress: the read steps prove the constraint for the read they append.
  `Assumptions.wf_snoc_initial` covers a read whose bytes all take the
  launch content as source (the protected scheduler reads and
  `Step.protected_read_of_maximal`). `wf_snoc_nonGlobal` covers shared and
  local reads. `wf_snoc_read` covers a read with write sources when no write
  covers an input byte it reads at a site. Extensions without a read keep
  the constraint (`inputReadOnly_wf_ext`, `Assumptions.wfStep`).
* The replay evidence (`Safety.consistentOfOutputReadReplacement`,
  `notOutputIntentAfterReadReplacement`) now also takes the input
  constraint for the new launch memory. A replacement that changes a CuQ
  read away from its launch word violates it.

**Shared `Lemmas` change.** The constraint holds only of the extensions
whose new reads return the launch bytes, so `Assumption.WfInOrder` cannot be
proved for `Assumptions.all`. Commit `2ddd65f61` ports the
progress-side interface of the Inkling branch: `Assumption.WfStep` with
`Execution.NoNewRead` and `WfInOrder.step` (inkling commit `cd7a13683`),
and `fires_read_space`, `fires_read_global`, `noNewRead_appendLanes` and the
shuffle and vote steps that ask for the constraints only for lane events
that read no memory (inkling commit `322538670`). The Lemmas files that
exist only on this branch (`PollProgress`, `ReadProgress`,
`WarpShuffleProgress`, `WarpVoteProgress`, `CpAsyncArriveOrder`,
`CpAsyncCompletionOrder`, `CtaBarFinishExit`) take `WfStep` in the same
way. `Step.protected_read_of_maximal` passes the read's launch sources
(`NewRead`) to its constraint callback, as `read_source_counted_extension`
does. FA4, TmaCopy, TcGemm, Fp16Gemm8192 and RmsNorm were adapted and
rebuilt.

## Generic repeated visits for scheduledRoleExits

The progress proof for tiles with two or more KV blocks needs every role to
advance through an arbitrary number of visits. The earlier progress lemmas are
specific to the first recurring visit. This section records the generic,
visit-indexed pieces.

**MMA.** `Progress.mmaIterationsThroughOfCohorts` issues every steady
iteration through `k` from the cohorts of the visits through `k` alone
(`Progress/MmaIterationWalk.lean`). The cohorts of later visits are not
needed, so the MMA warp can be advanced visit by visit in an induction that
interleaves the producers.

**Softmax, biased visits.** `Softmax.BiasedLoopHead` is a lane at the head of
the biased loop (pc 5032) of a repeated visit with its live registers
(`biasedHeadFacts`) and six per-lane event counts (`SoftmaxCounts`): Tensor
Memory collectives `11*visit`, warp barriers and elections (equal across the
warp), statistics notices `visit`, statistics credit acquires `visit+1` and
score acquires `visit`. The counts are needed because the warp-collective
steps require equal ordinals across the warp and the pending-readiness
arguments require the exact generation a blocked lane waits for. The step is
split at the correction acknowledgement:

* `Softmax.stageBiasedJoinsOfHeads` takes all 128 lanes of a stage from their
  heads through the score acquire, the four score loads, the Bias acquire,
  the Bias rendezvous, the affine statistics publication and the probability
  packet to the correction join (`BiasedVisitJoin`). Score and Bias
  readiness are needed only for a lane still waiting at that wait.
* `Softmax.BiasedVisitJoin.nextOfPending` acquires the correction credit
  (again only for a pending lane), updates the denominator
  (`repeatedDenominatorValid` keeps it valid) and takes the loop back edge to
  the head of the next visit or to the biased exit, back in the original
  history. The head registers the loop body never writes are recovered with
  `scoreTraceKeepsResidents` along the recorded path between the two heads.

Several statement extensions of existing lemmas support this: the Bias
acquire reports its poll window, the biased affine step reports the loop
registers it keeps, the probability join reports its counts
(`warpRepeatedProbabilityJoinWithCountsOfMaximal`), and
`scorePollCursor` identifies successful score polls by pc.

**Plain visits and transitions.** `PlainLoopAt` is a lane at the plain loop
head (pc 6661) or at the plain exit (pc 7605) with the same six counts; the
Tensor Memory count is a parameter because a plain visit adds 14 collectives
and a biased visit 11. `warpPlainJoinOfReturned` takes a warp from its score
return to the correction join (`PlainVisitJoin`), and
`PlainVisitJoin.nextOfPending` takes the credit and returns to the next plain
head or to the terminal entry. `BiasedLoopAt.exitOfLoop` takes the biased exit
(pc 6654) to the plain head, or to the terminal entry when the stage has no
plain visits; the loop geometry registers (1226, 1229, 1225, 1360, 1359) are
carried in the biased head for this. `PlainLoopAt.terminal` and
`SoftmaxTerminalAt.producerRow` give `TerminalProducerRow` from the terminal
entry and the lane's scheduler cursor at pc 3212.
`Progress.scoreReadyForPendingLane` and `Progress.ackReadyForPendingLane`
derive the score and acknowledgement readiness of a waiting lane from a
delivered score notification and from the correction credits of the visit.

**Loader.** Each cache wait needs only a lower bound on the slot's completed
MMA releases (`CacheUsesReleased`), and each warm Bias wait a lower bound on
the Bias-empty phase (`BiasEmptyReleased`). The waiting-lane side is
discharged from the warp's own shuffle and election counts. Both warps pass
every warm round, the warm tail with its stage-zero Bias generation, the
steady rounds and the drain (`loaderPublishesAndExits`). `loaderRoundsThrough`
runs rounds `0..r` from the releases of those rounds alone, which the
induction over visits needs.

**Global induction over visits.** `Progress.finalStateOfMaximal`
(`Progress/RepeatedVisitInduction.lean`) proves, for every scheduled CTA with
`2 ≤ trips`, a `LevelState` before each visit `n = 1, …, trips-1` and the
`FinalState` after the last one. A level holds stage zero at the heads of
visit `n`, stage one at its heads once stage zero has published visit `n`,
stage one's publications through `n-1`, the MMA cohorts of the visits before
`n-1`, the probability cohorts of visit `n-1`, and the Bias-empty releases of
the earlier biased visits. `levelStep` performs one visit in this order:

1. the loader rounds before `n` (`loaderRoundsThrough`, fed by the cache
   releases of the MMA iterations before `n-1`), giving the ring uses of MMA
   iteration `n-1` and the Bias generation of visit `n`;
2. the MMA iterations through `n-1` (`mmaIterationsThroughOfCohorts`), whose
   last score notification releases visit `n` of both stages;
3. stage zero's visit (`biasedStageStep` or `plainStageStep`), which
   publishes it, then stage one's visit;
4. the probability cohorts of visit `n` and the next Bias-empty phase;
5. the correction credits. Stage zero's credit of visit `n` needs both stages
   published through `n`. Stage one's credit of visit `n` needs stage zero's
   publication of visit `n+1`, so stage one's step to its next head is kept as
   an implication that the next level discharges. After the last visit, stage
   one's credit is the pc-8464 arrival (`lastStageOneCreditOfPublications`).

The per-lane head state is `LoopHeadAt` (a biased or plain head with its loop
counter and Tensor Memory count as functions of the visit) plus
`HeadArrivals`. `HeadArrivals` carries three lower bounds instead of a seventh
event count: the lane's arrivals on the main probability object, on the tail
object when it is the elected leader, and on the Bias-empty object when it is
lane zero. Lower bounds suffice because `probabilityCreditOfExtent` and
`biasEmptyReleasedOfArrivals` need only at least `gen+1` arrivals. The leader
is the same in every visit by the third clause of Core `ElectOk`
(`leader_eq_of_elections`); the joins expose their election events and the
positions of their credits for this.

The visit-one base case (`visitOneBiasedHeads`) shows that each lane has
passed exactly one warp barrier at its first biased head and that no election
lies between the opening tail election and the head. Partner elections of one
warp have equal ordinals because each lane executes pc 4859 once.

`biasScheduleMatch` (`Progress/BiasScheduleMatch.lean`) matches the softmax
biased visits with the loader's Bias schedule. A stage has more biased visits
than warm rounds, and the only biased visit beyond the warm rounds is stage
zero's visit `warmRounds+1`, which exists exactly when the warm tail issues
its extra generation.

The MMA terminal takes the final cohorts directly
(`Mma.steadyTerminalAndRelinquishOfTailCohorts`). `SteadyTailPhases` cannot be
derived from MMA-side facts, because its phases are unconditional facts about
the producer objects after the MMA has consumed the generation.
`loaderFinalReleasesOfTailCohorts` gives the loader's final cache and query
releases. `Progress.scheduledRepeatedExitsOfMaximal`
(`Progress/ScheduledRepeatedExit.lean`) assembles the exits: the rows and the
allocator through `repeatedRowsAndMmaExitOfTerminals`, and the loaders through
`loaderPublishesAndExits`.

## Current status

`Proof/Correct.lean` proves `correct_of_pre`, `completed_execution_of_pre` and
`realizable_result_of_pre` with `Pre` as the only hypothesis; the `Open`
structure is removed. `Theorem.lean` exports `correct`, `completed_execution`
and `realizable_result`, and `Tests/Kernel/Statements.lean` checks them like
the other kernels. `#print axioms` on the three theorems lists only `propext`,
`Classical.choice` and `Quot.sound`.

`Tools/reading_uses.py` reports that `EXT-TC-COMMIT-OPERAND-ORDER`, listed in
`READINGS.md` and `Theorem.lean`, has no EXT note. Its note in
`Core/Memory/CommitOperandOrder.lean` starts with `/-! ###` instead of a line
`### EXT-…` and has no `Disclosed by` sentence. This is a documentation gap in
Core, not in the proof, and is left for a Core patch.

## Proof2: the output warp as a site machine

`Proof2/` is the second proof tree of the restructuring (the role machines of the plan's §3.1);
nothing imports it until the migration is complete. Its first role is the output warp (warp 13):
`Proof2/Epilogue/Machine.lean` is a `Flow.Code` machine from the warp's `setmaxnreg` to its
`ret`, `Steps*.lean` prove `StepAt` at every state by `site_cases` (no site is a hand override),
`Shape.lean` is its event-shape table and `Ledger.lean` its counts of tensor stores, commits and
arrivals.

- The machine follows every value an event returns, with one exception: a load or shuffle of a
  32-bit register whose value is not a 32-bit word (`.bits 32 x`) stops it (`some none`). The
  scan arithmetic after such a value would follow pointer arithmetic and value types through
  some forty instructions. That no lane of warp 13 reaches `some none` is proved above the
  machine (`Warp.lean`, `good`): every state of a lane holds the reference values (`Fits`), the
  values the warp computes when every load returns the launch word and every shuffle and ballot
  returns what its source lanes hold (`Ideal.lean`), and such a state never steps to `some none`
  (`Next.lean`, `next_ne`).
- `good` is an induction on the warp collectives (shuffles and full-mask ballots) before an event,
  and along the lane's events. A load returns the launch word by the read-only input
  (`cuQReadsFromLaunch`) once its address is a request of the batch (`Reads.lean`). A shuffle's
  source lane made the same shuffle at the same site (`shfl_recv`), and a ballot's lanes made the
  same ballot at the same site (`vote_bits`): the machine counts the shuffles and ballots before
  each state (`ns`, `nv`, ledgered against the thread's trace in `Lane.lean`), `Fits` places every
  state at a position of the warp's common sequence (`Position.lean`), and a lane that is ahead in
  one kind of collective and behind in the other, or that returned before the instance, contradicts
  that order. A source lane that exited before the instance is excluded the same way
  (`shfl_lt_exit`, `vote_exit`).
- The machine starts at `setmaxnreg`. The thread's first five events are the prologue's (three
  broadcasts, the barrier-init fence, the common barrier; `Prologue.warp13StartupAt`), whose
  local steps reach the `setmaxnreg` with every live register; the registers the warp never reads
  have their startup values (`ent`). `Thread.lean` makes this the hand-off: the machine's run is
  the thread's events after the prologue (`trace`, by `Code.trace_from_steps`), and `stateAt X g k`
  is its state before event `k`.
- The ledger (`Ledger.lean`) is stated over runs of the role's machine (`Machine.Trace` from its
  first state). `Lane.counts` states the shuffle and ballot counts over the thread's trace: the
  prologue's three shuffles plus the state's counts; the prologue fires no store, commit or
  arrival, so the other counts carry over unchanged.
- `written`/`.exit late` tell the two returns apart (no tile, or after the second pass), so each
  count is a function of the state.

### Proof2: the output warp's facts for the upper layers (lane T1)

- The facts the upper layers consume about warp 13 are restated in kernel files outside the
  Epilogue family and proved from `Proof2/Epilogue`: `OutputBarrierFacts.lean` (ready polls,
  frees, the uniqueness of a lane's free per stage, the successful poll before a free),
  `OutputReadFacts.lean` (every read at an output pc reads a word of the batch's cumulative query
  offsets) and `OutputStoreFacts.lean` (every tensor store writes the selected work item's box of
  its CTA). They take `Pre` and `Consistent` only: the CuQ-protection premise of the old
  statements is no longer needed, since the read-only input assumption gives the launch words.
- Selection correctness is in `Proof2/Epilogue/Select.lean`: the scan's tile counts, its prefix
  scan, the scan's end, the ballot and the chosen request's coordinates in numbers.
  `Proof2/Epilogue/Assign.lean` combines it with the store table (`Store.lean`).
- `Proof2/Epilogue/Barriers.lean` places every event at an output pc at its machine state
  (`output_event`), and counts successful polls and arrivals along the machine's run.
- Library candidates for lane L, all used by `Proof2/Epilogue`:
  - already on this branch in `Lemmas/` (committed before the lane split): `Code.fired_pc`,
    `fires_wait_exact`, `fires_arrive_exact` (`Lemmas/Flow/Ledger.lean`), `Machine.trace_from_of`,
    `Code.trace_from_steps` and the `ShflOps` lemmas;
  - `Code.fired_tmpl` (the instruction an event of a code machine fires from) was promoted by lane L
    to `Lemmas/Flow/Ledger.lean`; the kernel copy is deleted.
- Commits on this branch carry no assistant trailer: the user's standing rule is that commit
  messages carry no assistant branding, and it takes precedence over a trailer requested in a
  coordination message.
- For lane L (reported by lane B1, not fixed here because only lane L edits `Lemmas/`):
  `seg_sym`'s `decideBool` (`Lemmas/Flow/Step/SegSym.lean`) restores the state the `sym_decide`
  rule ran in, so the decision's auxiliary declarations are lost and an error recovered by
  `sorry` loses its message. The fix is to keep the state on success and reject a proof that
  contains `sorry`.
- Restated from `Proof2/Epilogue` since: the store drain before the return (`Drain.lean`,
  `Protocol/OutputDrain.lean`, which now takes `Pre`), the ready poll before each store
  (`store_ready`, `OutputWarp.readyBox`) and the CuQ words of the output lookups
  (`OutputWarp.cuQReadWord`, `drainCuQReadWord`). The output slot geometry
  (`OutputSlotSource.lean`) and the Q-input order (`Thread/QueryInputOrder.lean`) did not concern
  warp 13 and only moved.
- Still in the old tree and still reachable: the warp-13 progress chain (`Thread/Output*Progress`,
  `IdleOutputFree`, `OutputMetadataReads`, `OutputFrame`, `Progress/IdleCtaExits`), the
  termination bound `epilogueRolePrefixFromDispatch` (a bound on a warp-13 walk from pc 174, used
  by `NonzeroRoleCounts`), `Thread/Machine.lean`'s use of the old output machine, and the Epilogue
  files these use. They wait for progress by descent (plan T4) and the glued thread machine.
- The move onto glue needs a first fragment from the thread's first instruction: the startup
  code shared by every warp up to the role dispatch. That fragment is plan task T1b
  (`Proof2/Startup`, `Proof2/Common/Roles.lean`); the Epilogue's private `stateAt` (offset of five
  events) goes once the output role is glued behind it.
- Library lane L replaced the proof of `Proof2/Epilogue/Shape.lean` (`shape`) by one call of the
  library tactic `site_shape` per family of sites (`shapeAt_scan`, `shapeAt_select`,
  `shapeAt_read`, `shapeAt_write`, `shapeAt_ends`), with the role's address tactic `ep_addr` for
  the mbarrier operands and the CTA size. The statement of `shape` and of `Ev` are unchanged; the
  helpers `shfl_ev`, `vote_ev`, `rd_ev`, `reg_of` and the `noWiden_*` facts are gone (no other file
  used them), and `loc_off` takes an `Int` offset. The file also gives the return-kind table
  (`ret`) and the stop condition of the machine (`stop_iff`, by `stop_cases`), the `stop_iff`
  field of `Fragment.OkAt` for the role's future fragment.
- Library lane L moved the generic parts of `Proof2/Epilogue/Warp.lean` to the library: the
  order of shuffles and ballots along a lane (`votes_le`, `shfls_le` by `Frame.coll_le`) and the
  induction on the collectives before a position (`good` by `Frame.coll_induction`). Statements
  are unchanged; the file is 656 lines (from 669). The rest of the file reads `Fits` and the
  role's private `stateAt`, and shrinks when the role moves onto glue and a per-site `Ref`
  (`Lemmas/DECISIONS.md`, "Sources").

## Proof2: the startup fragment and the glued thread machine (lane T1, task T1b)

- `Proof2/Startup/Machine.lean` is the code shared by every warp, from the first shuffle (pc 25)
  to the dispatch, as a site machine with 55 sites: three shuffles (`sh j`), sixteen elections
  (`elect j`), 34 mbarrier initializations (`init n`), the fence and the CTA barrier. Its exits are
  the states `enter r` at the first instruction of each role (pcs 179, 1907, 2769, 3102, 7746)
  and at the common return (9205, a warp index outside `0 … 15`). The machine follows every
  value (plan rule M1): the shuffles record their words (`x1` the shared base, `x2`, `x3` the warp
  index), a value that is not a 32-bit word stops it, an election goes to both outcomes, and the
  dispatch is the code's comparisons on `x3` (`enterOf`). Every value-table entry is the term the
  code computes (`warpW`, `ctaX`, the parameter loads as `sreg p.batch`).
- `Proof2/Startup/Steps.lean` proves every non-exit state's obligation by `site_cases` (47 s for
  the file). Warp 0's path from the third shuffle to its first election passes three
  `prefetch.tensormap` hints, whose rule reads the map parameter's object, which `seg_sym` does not
  evaluate; `seg_warp0` composes the code's own steps (by `seg_fp`) with `seg_prefetch` (the hint
  from `Pre.maps`) and the two warp-index tests that the recorded word fails. Library candidates
  for lane L: `seg_prefetch` (a tensor-map prefetch as a one-step segment) and `st_close`
  (closing a value read under `explicitParams` by the `explicitParams … = L` hypothesis): the
  restating step of `seg_fp` calls `sym_close` directly, so a role cannot pass the rewrite, and the
  CTA index the dispatch reads is therefore stated in the table under the explicit launch
  (`Startup.ctaX`); `Common/Sound.lean` `cta_word` rewrites it.
- `Proof2/Common/Roles.lean` declares the regions and exits of the startup and the five roles as
  data and checks them against the decoded code: `closed` (every region is closed up to its
  exits, `CodeCheck.closedFrom`) and `startup_sites`, `epilogue_sites` (the event instructions of a
  region, `CodeCheck.sitesFrom`, are the machine's sites; `Startup.site_mem`). The compiled
  dispatch is a sequence of `if`s, so a finished role walks the remaining dispatch tests to the
  return at 9205: a role's region includes those tests, and the first instructions of the roles
  they could reach are its declared exits, which its own facts on the warp index exclude.
- The thread machine is `Proof2.thread p L g`, the glued machine `glued p L g := Code.glue
  (Startup.code p L g) (frag p L g) (exit L)` with its ghost ledger
  (`Code.counted`), and `Common/Sound.lean` proves `thread_sound : Pre p L m → g < L.threads →
  (thread p L g).Sound` (`counted_sound` of `glue_sound` with the ABI prefix `start`, the startup steps, the roles'
  steps and the hand-offs). So `Frame.stateAt (thread p L) X g k` is the state of every launched
  thread before its `k`-th event; there is no per-role offset.
- Roles not yet migrated are stub fragments that stop at their first event (`stop`), so their
  threads are not followed past the dispatch (`stateAt` is `some none` after that event) until a
  lane replaces the stub.
- The exit `enter r` enters role `r` only when the startup's recorded words pass the role's gate
  (`Gate`: the shared base and the warp index the role's first state relies on), else the stub of
  `r`. This keeps the startup free of content stops; that every thread passes its gate is the
  startup's reference invariant (`x1` is the shared base, `x3` the warp index), proved in the
  layer above from the shuffle sources, which is what keeps followed threads away from the
  stubs of migrated roles.
- The ABI prefix (`Prologue.startWith`, `Prologue.abiFacts`, the parameter loads before pc 25)
  and the startup's transparency facts (`StartupAgreement`, `startupOut`) live in
  `Proof2/Startup/Abi.lean` and `Proof2/Startup/Transparency.lean` (moved from
  `Proof/PrologueStart.lean` and `Proof/PrologueTransparency.lean`; the old tree imports them
  from there, names unchanged). `Epilogue.params`, `ep_seg` and `segFree`
  (`Proof2/Epilogue/Base.lean`) are still shared by the startup steps.

### Fragment interface for the other tml-fa4 lanes

A lane that migrates role `r` (T2: the correction warps 8 to 11 enter at pc 7746, the MMA warp 12
at 1907, the softmax warps 0 to 7 at 3102, the loader warps 14 and 15 at 179):

1. writes its fragment `C : Flow.Code kernel Assumptions.all L g` whose first state sits at the
   role's entry pc, with `StepAt` for every state (`Proof2/<Role>/Steps*.lean`);
2. adds a constructor to `Proof2.Role`, its case to `frag`, its gate to `Gate` (the shared base
   and the warp index values its first state's facts use; `x3` is the warp index as the dispatch
   compares it) and its case to `exit`;
3. adds its case to `frag_steps` and to `handoff` in `Common/Sound.lean`: a concrete state of
   `Startup` state `enter r` whose words pass the gate is a concrete state of the fragment's first
   state. The startup's facts at `enter r` are `factsFrom (live pc) (Startup.valueOf p L g d)`:
   the shared-memory addresses as `addi x1 n` (`addi_sb` turns them into `L.sharedBase + n`), the
   CTA index as `sreg (ctaX p L g)` (`cta_word`), the batch as `sreg p.batch` (`batch_word`),
   the ABI registers as `Prologue.abiFacts`.

The fragment does not take an `ent` argument for the startup registers it never reads: they are
the startup's values, and the hand-off is the only place that relates the two tables. The
startup machine, `Decl`, `closed` and the sites checks do not change when a role is added.

## Proof2: the output warp behind the startup (lane T1, task T1a, in progress)

- The output warp's facts are stated on the public frame `Frame.stateAt (thread p L)`; the
  Epilogue's private `stateAt` (an offset of five events into the trace), its `trace` hand-off
  and `Thread.lean` are deleted. `Proof2/Epilogue/Glue.lean` gives the frame's view of a lane of
  warp 13: after the startup's five events (`prologue_take`, `enter_epilogue`) every state is a
  role state `inj d` (`stateAt_role`), which steps by the role's machine (`role_succ`); an event
  at a role state has its site's shape (`fired`, from `thread_sound` and `Code.glue_fired`); a
  count of the role's states is a count over the thread's events (`count_role`). The ledger
  facts (`free_unique`, `ready_before`, `commit_wait`) count over `(X.tr g).take k`, with no
  offset. `ent` and `M` moved to `Machine.lean`.
- Library candidates for lane L, in `Proof2/Lib/Glue.lean`: `Code.glue_fired` (an event of the
  glued machine from a role's state is one of the role's machine; `Iff.rfl`), `glue_next_inr`,
  `Code.counted_fired`.
- The thread machine carries a ghost ledger: `thread p L g := (glued p L g).counted cls` with
  the classes `Cls.shfl` (shuffles) and `Cls.vote` (full-mask ballots), in `Common/Roles.lean`.
  The output warp's state no longer has the counts `ns`/`nv`: a role state of the frame is
  `inj d n` with the ghost counts `n`, which `Frame.count_eq` ties to the thread's events
  (`Glue.counts`). `Fits d ns nv` and `Expect d ns e` take the counts as arguments; they count
  the thread's events, so the first pass starts after the startup's three shuffles
  (`PassStart false 3 0`). `fits_next` gives the successor's counts from the shape table
  (`ev_counts`); the per-step count lemma `next_cnt` and `Lane.lean` are deleted.
- Step 3 of the previous list is done: `Warp.good` is `Frame.followedOn` for the thread machine.
  - `followedOn Q` (`Proof2/Lib/Followed.lean`, for lane L): `followed` restricted to the threads
    with `Q g`; the step is asked only at their events and may use only that their predecessors
    are not bad. `Q` is "a lane of warp 13" (`Warp.Q`) while the other roles are stubs: the
    sources of warp 13's collectives are lanes of warp 13. `followedAtOn_of_lex` is the form the
    collective sources use.
  - Order: `lexOrder μ`, `μ (h, j)` the shuffles and full-mask ballots among the first `j + 1`
    events of `h`. `upTo_of_prev` turns "no bad predecessor" into the old induction hypothesis
    (`GoodUpTo`, now over all lanes of warp 13 and all positions).
  - `Ref` (`Warp.lean`): at a startup state, `StartAt` (the site, the shuffle count, the count of
    all events, and the words: `x1` the shared base after `sh 0`, `x2 = 13` after `sh 1`, `x3 = 13`
    at the fence and the barrier; elections and initializations are excluded, warp 13 does not
    reach them), no ballot, and the output warp's counts zero; at a role state `Fits`, at least
    five events, and the ledger `Led`; at a stub, `False`. `Good` is `Frame.FollowedAt` with `Ref`.
  - The startup has a shape table (`Proof2/Startup/Shape.lean`, `Startup.Ev` by `site_shape`; the
    fence by hand since `site_shape` has no class for `fence.mbarrier_init`; elections and
    initializations have the entry `True`, no reference invariant uses them yet). The startup
    shuffles' values come from the shuffle source (`start_recv`: the source lane, lane 0 of the
    warp, is followed up to the instance, its votes are bounded by `Frame.coll_le`, and its site
    is the shuffle of the same count, `start_sent`), which replaces `Prologue.firstSharedValue`,
    `secondWarpValue`, `thirdWarpValue`, `warp13StartupAt` and `nonzeroFenceBar` in `prologue_take`
    (deleted), `prologue_ev` and `prologue_pc` (deleted; `prologue_ev` now gives the pc bound and
    takes the lane's good state). `Startup.warpW_eq` evaluates the code's warp index.
  - The thread machine counts more classes (`Cls`: `all`, `store`, `commit`, `wait`, `arrive`,
    `acq st`; `cls L g`). The count of all events is the position (`count_all`), which tells
    startup states (`n .all ≤ 4`) from role states (`5 ≤ n .all`) without a startup trace. The
    output warp's counts are conjuncts of `Ref` (`Led`, one step lemma `led_step` for all of them,
    `Ledger.lean`), and `ledger_at` reads them off the frame: `count_role`, `count_at`, `startEvs`,
    `stateAt_role`, `enter_epilogue`, the Machine-run `ledger` and the per-count step lemmas are
    deleted. This is the "polls and arrivals as ghost classes" part of the T3 preparation.
  - The CuQ reads keep `Reads.read_word` (the read-only input assumption, the launch-input
    source).
  - Epilogue size: 5,636 lines (from 5,595): the startup reasoning moved from the old tree into
    `Warp.lean` (`start_recv`, `start_step`).
- Trim, first pass: the Epilogue's copy of the code's 32-bit vocabulary (`r32` … `popc`) is
  replaced by the library's (`Lemmas/Flow/Arith32.lean`, re-exported in `Epilogue` so qualified
  names keep working), and the generic word lemmas on small words (`W`, `add32_W`, `min32_W`, the
  signed comparisons, `sub32_W`, `mul32_W`, `mad32_W`, `toNat_shrs_W`, `shl8_W`, `not32_add_W`,
  `popc_W`, and `sdiv`/`divOk`/`fdiv` with `sdiv_W`, `fdiv_W`) move from `Arith.lean` (deleted),
  `Select.lean` and `Reads.lean` to `Proof2/Lib/Word.lean`, a library candidate for lane L
  (promotion target: `Lemmas/Flow/Arith32.lean`). `shrs_k_W` was a copy of `toNat_shrs_W`.
  `ev_class` and `ev_coll` are derived from `ev_counts`; `store_class`, `isColl_vote`,
  `isColl_shfl` are gone. Epilogue: 5,332 lines (from 5,636); `Proof2/Lib/Word.lean` 241.
- T3 preparation: per stage, the thread machine counts the successful polls of the ready barrier
  (`Cls.poll st`, the library's `okPoll`) and the arrivals on the free barrier (`Cls.freed st`,
  `arrivesOn`) instead of the output warp's own `isAcq`; their closed forms (`acqd`, `freedAt`)
  are conjuncts of `Led`. `stage_budget` (`Barriers.lean`) states, at every role state of a lane of
  warp 13, `arrivals (freeLoc st) ≤ okPolls (readyLoc st) ≤ 1` over the lane's events: the
  consumer and producer counts of the stage's unit hand-offs in the vocabulary of
  `MbarRing.UnitHandoff`. `ready_before` now returns the successful poll from `exists_okPoll`;
  `isAcq` and `isAcq_kind` are deleted. Epilogue: 5,337 lines.
- Remaining, in order (criterion: Epilogue at most 4.0k lines, no completion premise, no private
  `stateAt`):
  1. Trim further. Candidates measured but not done: the five shuffle cases of `Warp.expect`
     share a prefix (source lane facts from `shfl_recv` plus `lane_facts`; about 30 lines);
     `votes_le`/`shfls_le` are mirror images; `start_recv` repeats the source argument of
     `shfl_recv` for the startup (both could become one collective-source lemma over a position
     function, plan L3); `Next.next_ne` is the `ref_cases` shape (L2 tactic) and the value tables
     of `Machine.lean` are the generator's (L5).
  1. Trim further. Done: the startup's shuffle source is one lemma for every warp
     (`Common/Frame.lean`, `start_recv`), the scan shuffles' and the ballot's expectation from
     their sources are pure lemmas shared with the MMA warp (`expect_shfl_of_src`,
     `expect_vote_of_bits`), and `Next.next_ne` treats the scan's and the choice's sites as one
     case each. Epilogue: 5,079 lines. Remaining candidates: `votes_le`/`shfls_le` are mirror
     images; `start_step` of the two warps differs only in the barrier's entry (a generic
     startup step with the entry as a hypothesis); `shfl_recv`/`vote_bits` and the MMA warp's
     `mshfl_src`/`mvote_bits` are one collective-source argument over a position interface
     (plan L3, about 250 lines between the two warps); `Next.next_ne` is the `ref_cases` shape
     (L2) and the value tables of `Machine.lean` are the generator's (L5). The 4.0k target needs
     these and a cut in `Select.lean` (808 lines of number facts), which was not measured.
  2. T3: instantiate `MbarRing.UnitHandoff` for the ready barriers (producers: the correction
     warps' arrivals; consumers: warp 13's polls, `δ = 0`) and the free barriers (producer: warp
     13; consumers: the correction warps) once the correction fragment exports its counts; the
     output warp's side is `stage_budget` below. The phase contents (one arrival per producer per
     phase) come from the reuse gate and need both roles followed, so they wait for lane T2's
     correction fragment.
- The warp-13 progress chain and `epilogueRolePrefixFromDispatch` stay for T4.

## Proof2: the MMA warp as a site machine

`Proof2/Mma/Machine.lean` is a `Flow.Code` machine for warp 12 from its first named barrier after
the Tensor Memory allocation (pc 1910) to its `ret`; `Steps*.lean` prove `StepAt` at every
state by `site_cases` (176 states at 172 program counters).

- The role machine starts after the `setmaxnreg` and the allocation. On lane 0 the allocation
  fires two events at one instruction, the request and the write of the address; between them
  the thread sits at sub-step 1. A machine state there needs a `sub` that is not constant, and
  `Lands.sub` is closed by `rfl`, which fails for every successor that is an `if` of a symbolic
  condition (most of this machine's). These events are a small startup machine (`Startup.lean`,
  `S`, with `step_alloc` and `step_allocWr`) glued before the role machine with lane L's
  `Code.glue` (`G`): one machine from the `setmaxnreg` to the `ret`.
- The hand-off (`Thread.lean`, `trace`) is the output warp's: after the five prologue events
  (`Prologue.nonzeroCommonPrefix`) the dispatch's local steps (`Dispatch.lean`, the old tree's
  `dispatchWarp12` restated to keep also the registers the warp never reads, which `ent` gives
  their startup values) reach the `setmaxnreg`, and the thread's later events are a run of `G`
  (`Code.trace_from_steps`). The machine can stop on a load or shuffle that returns a value
  other than a 32-bit word; that no lane of warp 12 does is not proved here, as it needs the
  launch-input and warp-collective sources of lane L's task L3.
- The scheduler's scan is the output warp's arithmetic on other registers; its words and loop
  state are recorded in an `Epilogue.D` (`V.sc`) so that the output warp's functions of the scan
  (`tlOf`, `prefixD`, `partials`, `loopRegs`, `chosen`) are reused. The tile coordinates are
  computed differently (`coords`: the row offset is `256 (nt - q + c) + 256` with the floor
  correction `c`, where the output warp computes `256 (nt + ~q) + 2^30`).
- The Q descriptors are inline-assembly registers that each QK block moves by `∓2048`; the
  machine records their 64-bit words (`V.qd`, updated by `qstep` at the block's election)
  because a register term written from the launch would grow with every block.
- Five states are hand overrides of `site_cases`: the two named barriers (`bar.sync 2, 416`),
  the permit relinquishment and the deallocation, whose continuation lemmas `advances` does not
  include, and the poll of PV block 0 on a lane that issues no MMA (`stepOk_mw0`): its segment
  passes two guarded MMAs and then branches on the K/V slot, and `seg_sym`'s walk reads guards
  only from the end facts, so the segment is cut after the MMAs.
- Library lemmas written here for promotion by lane L (formerly `Proof2/Lib/Steps.lean`, now
  `Lemmas/Flow/IssueNext.lean`, `Lemmas/Flow/Step/Alloc.lean` and `issue_step` in
  `Lemmas/Flow/Step/SiteCases.lean`; the copies are deleted):
  `fires_barSyncN_next`, `fires_tcRelinquish_next`, `fires_tcDealloc_next` (the continuation
  of `bar.sync` with a count, `tcgen05.relinquish_alloc_permit`, `tcgen05.dealloc`) and the
  tactic `issue_step lemma trans […] seg_by (…) inv_by (…)` (the issue branch of `site_step`
  with the continuation lemma given). Two library gaps are recorded for lane L: `advances`
  should include these instructions, and `seg_sym`'s walk should pass a guarded event
  instruction whose guard the start facts give as false. Lane L has promoted the three lemmas
  (`Lemmas/Flow/IssueNext.lean`, used by `advances`) and `issue_step`
  (`Lemmas/Flow/Step/SiteCases.lean`), and later `step_alloc` and `step_allocWr`
  (`Lemmas/Flow/Step/Alloc.lean`); `Proof2/Lib/Steps.lean` is removed.
- The end sites carry whether the warp had a tile (`relinq late` and so on, as the output warp's
  `exit late`), so that every count of the ledger is a function of the state and the number of
  loop rounds.
- `Shape.lean` is the event-shape table (`Ev`, `shape`, checked in about 7 s): polls and commits
  name the barrier at their address register and the poll's parity, broadcasts their word, reads
  their address, the scheduler's sites are the output warp's `Epilogue.Ev` of the scan state;
  elections, MMAs and the two Tensor Memory resource operations are stated by kind. A poll or
  commit at a misaligned address, a read, an MMA and the deallocation may fault instead (`ub`).
  The MMA's operands (descriptors, accumulator column) are not in the table yet.
- `Ledger.lean` is lane L's ghost ledger (`Code.counted`) on the machine: successful polls and
  commits per barrier, MMAs, named-barrier arrivals, and the elections the lane wins and loses.
  The won/lost classes replace the earlier per-program-counter wins: only the lane that wins an
  election commits after it, and by Core's election rule (`ElectOk`, every election of a warp
  with one mask returns one leader) a lane wins all of the warp's full-mask elections or none.
- `Ref.lean` proves the count and loop-register conjuncts of the reference invariant
  (`RefCounts`, `ref_step`, `ref_next`). `Site.ord` numbers the pipeline's sites in program order
  (0 before the pipeline, 1–16 the first K/V block, 20–49 a loop round, 60–85 the tail, 100 the
  second pass); a site at place `x` has been passed `pq x q r` times at place `q` with `r` rounds
  done. At every state, for some `r` and some outcome `w` of the lane's elections:
  - in the loop and the tail the slot is `(2r + 1) mod 3`, its parity `((2r + 1) / 3) mod 2`, the
    P parity `r mod 2`, the accumulate flag `r ≠ 0`; in the loop `r + 1 < B` (the tile's K/V
    blocks as a signed word) and `%r6144 = r - B`; in the tail `r + 1 = B`, or `r = 0` with
    `B < 2`;
  - the successful polls of the barrier at shared offset `o` are `acqAt q r o` (Q stages once;
    the K/V ring's slot `k` once per ring index `j < ringAcq` with `j mod 3 = k`, the indices being
    K₀, then `V_i, K_{i+1}` per round, then the last V; each P half once per round and once in the
    tail);
  - the commits to `o` are `commitAt q r o` on the winning lane and zero on the others (a ring
    release `j` releases slot `j mod 3`), and the won and lost counts are all elections or none;
  - at a commit site the lane is the winner.
  Every step keeps it (`ref_step`), given that an event is not undefined behaviour (only the
  commit sites need this: their machine continues on any event, and their fault conditions,
  misaligned or unresolvable barrier, are the `ref_safe` obligation, not proved here) and that an
  election returns what `Expect` asks (`ExpectElect`: a win after a win, a loss after a loss).
  `ref_next` adds the stop condition: with `Expect` also giving the site's return kind, the
  counted machine does not stop. The definitions and generic step lemmas are `Ref.lean`; the
  per-site steps are `RefScan.lean`, `RefPoll.lean` and `RefElect.lean` (one theorem per site
  family, `StepRef`), assembled in `RefNext.lean`; each file checks in about 8–10 s, in
  parallel. A count step at concrete places is evaluated through `qmove` (the places a move
  passes, decided by `decide`) and the per-place increments `acqD`/`comD`/`elD`, so no case
  splits on the barrier offset are needed.
- Fragment interface (lane T1's "Fragment interface for the other tml-fa4 lanes"): the MMA
  role's fragment is `Mma.M p L g` (`Startup.lean`, no `ent` argument), the warp's machine from
  the role's entry, the `setmaxnreg` at pc 1907 (the startup machine `S` glued before the role
  machine). Its step obligations are `Mma.stepAt_G hp hg`, and `Mma.init_facts` lists the
  register facts of its first state (pc 1907): `1062 = 12` (the warp index word), the shared
  addresses `1069, 2390, 6497, 1178, 2535, 6495` (`sb + 192, 208, 224, 68608, 0, 144`), the CTA
  word `1072`, the batch `7203` and the ABI words `7500, 7501, 7502, 7503, 7506`. Lane T1 adds,
  in `Proof2/Common`: the constructor `Role.mma`, `frag p L g .mma := Mma.M p L g`, the gate
  `Gate L .mma d := d.x1 == BitVec.ofNat 64 L.sharedBase && d.x3 == BitVec.ofNat 64 12`, the
  case of `exit`, `frag_steps` from `Mma.stepAt_G`, and `handoff` from the startup's facts at
  `enter .mma` to `init_facts`. Until then `Thread.lean` and `Dispatch.lean` (the old tree's
  dispatch with the five-event offset) stay as the role's only hand-off; they go when the role
  is glued.
- The election source is `Proof2/Lib/Elect.lean` (`elect_leader`, `elect_winner`, library
  candidates): Core's `ElectOk` gives one leader to all full-mask elections of a warp, which is
  `ExpectElect` for a lane's own earlier elections, and gives at most one winning lane per warp,
  so the warp's commits to a barrier are the winning lane's `commitAt`. Applying it to the counts
  needs each counted election's mask, which the shape table now states (`Ev` at an election:
  the event's pc is the site's and its mask is `2 ^ 32 - 1`).
- Not done (plan task T1c, step 3, the never-dropped proof): that no lane of warp 12 reaches
  `some none`. By `stop_iff` the machine stops only when a load or a shuffle returns a value that
  is not a 32-bit word, so `ref_next` turns `Frame.followed` (or `followed_stages`) with
  `J := RefCounts` into two source obligations, plus `ExpectElect`:
  - loads (the scheduler's `word` reads, `q0`, `q1`, `uk`): the launch-input source
    (`inputReadValue`, `Frame.read_value_of_bytes`) once the address is an input word; this needs
    range conjuncts in the reference invariant (the scan's group start and `gx` in `[0, batch]`,
    so the chosen request `popc bal + gx` is in range behind the code's `< batch` test), not yet
    stated;
  - shuffles: the warp-collective source (`ShflOk`): the source lane's operand at the same
    instance, which is a word by its shape table, provided the source lane is followed up to that
    instance and did not exit before it. Excluding the exit needs warp-uniform control flow: the
    scan's last round and the tile's blocks are the same on every lane, i.e. the content of the
    scan (the output warp's `Ideal` definitions apply: the MMA warp records its scan in an
    `Epilogue.D`), the launch words `c0`, `c1`, `ukw` at the chosen request, and the position of
    each shuffle in the warp's common sequence (the scan's `7 (R + 1)` plus the pipeline's
    broadcasts per place and round), with `Frame.coll_le`/`coll_induction`;
  - `ExpectElect`: `elect_leader` applied to the lane's own earlier election, found from the
    won/lost counts by `Frame.count_eq` on the counted thread machine.
  The frame for these is `Frame.stateAt (thread p L)` once lane T1 glues the role (above); the
  role's private five-event offset (`Thread.stateAt`) is not used for them.
- Old upper-layer files whose statements the proved counts, shapes and locations cover in
  substance (they stay until the counts are lifted onto the thread frame, since the old roles
  import them): `MmaMbarAddress` (barrier addresses: `Shape`, `cm_loc`, `mw_loc`, `smLoc_*`),
  `MmaRingAddress` (slot arithmetic: `LoopRegs`, `slot1_eq`, `loopEnd_regs`),
  `MmaReleaseOrdinals`, `MmaReadyReleaseElection`, `MmaCommitGate`, `MmaElect` (release ordinals,
  commit points and their elections: `commitAt`, `ringRel`, the won/lost counts, `elect_winner`),
  `MmaReadySequence`, `MmaReadyIntervals`, `MmaReadySegments`, `MmaReadyCursor` (ready
  observations per use: `acqAt`, `ringAcq`), `MmaLoopCounter`, `MmaLoopIterations` (rounds
  against the tile's blocks: `RefQ.loop`, `RefQ.tail`). `MmaReadyHistory` (clean poll records)
  is not covered. The task's `MmaPollOrdinal*` and `MmaCommitTargets` do not exist in this tree.
- `Shape.lean` also gives the return-kind table (`ret`: a 32-bit word at the loads and shuffles,
  nothing elsewhere; the allocation's address read is followed whatever it returns) and the stop
  condition (`stop_iff`, by lane L's `stop_cases`, the `stop_iff` field of `Fragment.OkAt`):
  the machine stops exactly when a load or shuffle returns a value that is not a 32-bit word.
- Library lemmas written here for promotion (formerly `Proof2/Lib/Shape.lean`, now
  `Lemmas/Flow/Step/ShapeRegs.lean`; the copy is deleted): `smLoc`,
  `fires_wait_reg`, `fires_commit_reg`, `fires_shfl_reg`, `fires_vote_reg`, `fires_load_reg`,
  `fires_load_kind`, `fires_tcMma_kind`, `fires_elect_kind`, `fires_barImm`,
  `fires_tcResource_kind`: the event of an instruction from the values of its operand registers.

## Proof2: the MMA warp glued into the thread machine (lane T1)

- Merged the MMA lane's branch `tmlfa4-mma-proof2` (at a59845726). Its machine read the output
  warp's scan state `Epilogue.D`, which lost its counts `ns`/`nv` when the counts became ghost
  classes of the thread machine, and the 32-bit vocabulary moved to `Lemmas/Flow/Arith32.lean`;
  `Mma/Machine.lean`, `Mma/Ref.lean` and `Mma/Shape.lean` follow both (the scan's count updates
  are dropped, the vocabulary is opened from `PTX.Flow.Arith32`). No statement changed.
- `Common/Roles.lean` has the constructor `Role.mma`, `frag … .mma := Mma.M p L g`, the gate
  (`x1` the shared base, `x3 = 12`) and the case of `exit`; `Common/Sound.lean` has
  `frag_steps … .mma := Mma.stepAt_G` and the hand-off from the startup's facts at `enter .mma`
  to the fragment's first facts (the same register-by-register check as the output warp's, over
  `Mma.live_1907`). `mma_sites` checks that the event instructions of the MMA region are the
  machine's sites (`Mma.site_mem`, for the role machine and its allocation prefix).
- `Mma/Thread.lean` and `Mma/Dispatch.lean` (the hand-off with the old tree's five-event offset)
  are deleted: the glued frame `Frame.stateAt (thread p L)` replaces them, as the MMA lane's
  notes planned. Nothing imported them.
- The output warp's reference invariant is `False` at a state of the MMA role, as at a stub: no
  lane of warp 13 passes the MMA gate.

### Toward the MMA warp's never-dropped proof (lane T1)

- Merged lane L at c292de7d2. Lane L promoted the kernel's library candidates: `glue_fired` and
  `glue_next_inr` (`Lemmas/Flow/Glue.lean`), `counted_fired` (`Lemmas/Flow/Counted.lean`),
  `followedOn` and `followedAtOn_of_lex` (`Lemmas/Kernel/Followed.lean`), the word lemmas
  (`Lemmas/Flow/Arith32Word.lean`, namespace `PTX.Flow.Arith32`, re-exported in `Epilogue` with the
  vocabulary) and `elect_leader`/`elect_winner` (`Lemmas/Kernel/ElectSource.lean`). The copies
  `Proof2/Lib/Glue.lean`, `Followed.lean`, `Word.lean` and `Elect.lean` are deleted; the kernel's
  side of lane L's merge (its copy of this branch's older Epilogue commits) is this branch's.

- The MMA lane finished; lane T1 does the never-dropped proof (that no lane of warp 12 reaches
  `some none`) on the glued frame and may edit `Proof2/Mma` for it.
- The pipeline's broadcasts are counted in the state (`V.ps`, a ghost field the `sh` step
  increments; no register reads it), and `RefQ.ps` states their closed form `shAt q r` (three
  before the loop, six per round, five in the tail). The counted places now include the 14
  broadcast places, and `refQ_move`, `refc_quiet`, `refc_poll`, `refc_commit`, `refc_elect` and
  `refQ_skip` take the broadcast increment (`shD`); `refc_sh` is the broadcast step. The ledger's
  won and lost classes count full-mask elections only, so that a won election found by its
  count has the mask the election source (`elect_leader`) needs.
- `Picked` (output warp, `Ideal.lean`) no longer contains the two division conditions of the
  output warp's tile coordinates: they follow from the rest (`Select.lean`), and the MMA warp,
  which shares the scan, computes its coordinates differently. The choice of a tile is
  `fits_tilesD`, the second pass's start `fits_pass2` (both `Next.lean`), used by both warps.
- `Mma/Sim.lean`: at every scheduler site the MMA warp's step is the output warp's step of its
  scan state (`succ_scan`; `toE`/`ofE` translate the states), and the choice of a tile differs
  only in the coordinates' divisions (`succ_tiles`).
- `Mma/Fits.lean`: the MMA warp's reference values `MFits` are the output warp's `Fits` of
  `toE d` with the thread's shuffle count shifted by the broadcast before the scan and the
  pipeline's broadcasts (`v.ps`); in the pipeline the used-K length is the launch word (`ukv`),
  in the second pass `v.ps` is the full pipeline's count of the picked tile (`pipeN`, from
  `RefQ.tail` at the last commit), which makes the second pass's positions the same on every
  lane of the CTA. `mfits_next`: every step on an event that returns what `MExpect` says keeps
  `MFits` (scheduler steps by `Epilogue.fits_next`, the pipeline by `mfits_pipe`, the step into
  the second pass by `mfits_pass2`).
- `Proof2/Lib/UbLast.lean` (library candidate): an undefined-behaviour event is its thread's last
  (`Run.ub_last`, `ub_last`). The MMA warp's commit sites continue on any event, so a commit
  that faults would break `RefQ.com`; the thread-level reference invariant of warp 12 is to be
  guarded by "no undefined-behaviour event so far" (a ghost class), which `ub_last` makes
  sufficient: no event follows one.
- Remaining for warp 12's `followedOn`, in order:
  1. Thread ledger: classes for the MMA counts `RefQ` reads (successful polls and commits per
     barrier, won and lost full-mask elections) and an undefined-behaviour class; `RefCounts`
     reads only those components, so the thread counts map onto the role's.
  2. Startup facts for any warp index: `StartAt`, `start_kind`, `start_sent`, `start_recv`,
     `start_step` of `Epilogue/Warp.lean` take the warp index (13 for the output warp, 12 for
     the MMA warp) and a role-side bound (a role state is past three shuffles and five events),
     which also folds the startup's source argument into one lemma for both warps.
  3. `Ref` of a lane of warp 12: at a startup state as for warp 13; at a role state, if no
     undefined-behaviour event so far, `RefCounts`, `MFits` and the count of all events; at the
     allocation prefix `S` the counts of the startup.
  4. Positions of warp 12: pass-one states are the output warp's positions shifted by one,
     pipeline broadcasts lie between the first pass's last shuffle and the second pass's start
     (`shAt q r < pipeN` at a broadcast place, from `RefQ.loop`/`RefQ.tail`), second-pass states
     are the output warp's positions shifted by `1 + pipeN`, equal on every lane of the CTA by
     `Picked.unique`; exits after them.
  5. Sources: scan shuffles and ballots by the output warp's `shfl_recv`/`vote_bits` argument on
     these positions; a pipeline broadcast returns a word since every MMA and startup shuffle
     site sends one (only the source lane's instance and the exit exclusion are needed); reads by
     `Reads.expect_word`, the request's two reads (`reqAddr`) and the used-K read by
     `inputReadValue` (sites 2112, 2113, 2116 are input read sites; `Pre.usedK` gives the word);
     elections by `elect_leader` with the earlier won or lost election found from its count.
  6. `Mma.good` by `Frame.followedOn` with `Q` the lanes of warp 12, then the combined statement
     for warps 12 and 13 (`Frame.Bad` of a lane depends only on that lane's `Ref`).
- Warp 12's never-dropped proof is done: `Mma.good` (`Proof2/Mma/Warp.lean`) is
  `Frame.followedOn` for the lanes of warp 12, and `Mma.good_migrated` states, for every
  consistent execution under `Pre`, that every lane of warps 12 and 13 is followed and holds its
  role's reference invariant (`RefAll`: the MMA warp's on warp 12, the output warp's elsewhere).
  No new premise: the CuQ reads come from `cuQReadsFromLaunch` (the read-only input assumption).
  - Thread ledger: `Cls.mma c` counts the MMA warp's classes (`Mma.Cnt`, now with
    `DecidableEq`) and `Cls.ub` the undefined-behaviour events; the role's counts are
    `rc n = fun c => n (.mma c)`, which the counted thread machine bumps exactly as the role's
    ledger does (definitionally).
  - Startup facts for any warp (`Proof2/Common/Frame.lean`): `StartAt L w`, `start_kind`,
    `start_sent`, `start_recv` (one source lemma for both warps, generic over the warp's
    reference invariant), `start_next` (the startup's step up to the barrier), `start_bump`,
    and the frame's counts (`count`, `counts`, `count_all`, `exists_of_count`, `ub_zero`),
    `start_fired`, `good_state`, `isColl`, `μ`, `GoodUpTo`, `upTo_of_prev`, `lane_facts`, all
    moved out of the Epilogue. A startup event counts only shuffles, all events, and (the
    barrier) the MMA warp's named-barrier class (`StartCls`).
  - Warp 12's `Ref`: `StartAt L 12` with no ballot and zero MMA counts at the startup; three
    shuffles, no ballot and zero counts at the allocation prefix (its events are quiet:
    `s_quiet`, from the `setmaxnreg` and allocation templates); at a role state, if `n .ub = 0`,
    `RefCounts` and `MFits`. The guard holds before every event (`ub_zero`, from `ub_last`).
  - Positions (`eband`, `mband`, `sh_band`, `shift`): an output-warp state of the first pass is
    before the CTA's choice `nC R bal`, strictly at the scan, the ballot and the return, and a
    first-pass return contradicts a choice; a second-pass state is after it. The MMA warp's
    count is the output warp's shifted by one, plus `pipeN` in the second pass; a pipeline
    broadcast lies strictly between (`shAt q r < pipeN`, from `RefQ`). From these and the
    output warp's position lemmas: `mshfl_lt_vote`, `mshfl_lt_exit`, `mvote_exit`,
    `mshfl_same`, `mvote_same`.
  - Sources: `mshfl_src` (the source lane's shuffle of the instance, or a contradiction with
    its return), `mvote_bits`, `sent_word` (every shuffle site of warp 12 sends a word),
    `expect_uk` (`inputReadValue` on the used-K word of the chosen request), `expect_elect`
    (`elect_leader` with the earlier election found from the won/lost count), and the output
    warp's pure source lemmas `expect_shfl_of_src`, `expect_vote_of_bits` (the shared part of
    `Warp.expect`, factored out for both warps).
  - `Mma.bs_ref` (`Fits.lean`) is the pipeline's K/V block count of the picked tile, shared by
    `mfits_pass2` and `sh_band`.
  - Evaluating `isFullVote` on the literal mask `2 ^ 32 - 1` (by `simp`, `decide` or `rfl`)
    times out in the kernel; `isColl_vote` takes the mask as a hypothesis.
  - Library candidates (lane L): `Proof2/Lib/UbLast.lean` (`Run.ub_last`, `ub_last`),
    `exists_of_count` and `isColl_vote` in `Common/Frame.lean` (generic over the ledger), and
    `allocT` (the allocation's templates) in `Mma/Warp.lean`.

  Lane L has promoted them unchanged to `Lemmas/Flow/Step/ShapeRegs.lean`; `Proof2/Lib/Shape.lean`
  is removed and `Mma/Shape.lean` imports the library file.

### The correction warps glued into the thread machine (lane T1)

- Merged the Correction lane's branch `tmlfa4-corr-proof2` (at c929ce80d). Its machine recorded
  the scan's shuffle and ballot counts in the output warp's scan state, which no longer has them
  (they are ghost classes of the thread machine); the count updates are dropped from
  `Correction/Machine.lean`, as for the MMA warp. No statement changed.
- `Common/Roles.lean`: the constructor `Role.correction`, `frag … .correction :=
  Correction.code p L g`, the exit case, and the gate. `Gate` and `exit` take the thread `g`:
  the correction warps' first state holds the thread's own warp index (`%r1062`, read by their
  named barriers), so the gate fixes `x3 = g % L.block / 32` besides the shared base.
  `Common/Sound.lean`: `frag_steps … .correction := Correction.stepAt` and the hand-off from the
  startup's facts at `enter correction` to `Correction.facts_init`, register by register.
- The output and MMA warps' reference invariants are `False` at a correction state (no lane of
  warps 12 or 13 passes that gate).
- `correction_sites` checks that the event instructions of the correction region are the
  machine's sites (`Correction.site_mem`, every constructor of `Correction.Site`; the rescale
  load's implicit wait shares its load's pc), as `mma_sites` does for the MMA warp.
- Not done: the T3 `MbarRing.UnitHandoff` instances for the output stages' ready and
  free barriers: the correction warps' side (one arrival per producer per phase, from the reuse
  gate) needs the correction warps followed with their reference invariant, which lane T2's
  `Ref` (statements only so far) does not yet give.
- Batch 15 base (lane T1): the branch is fast-forwarded to `ps-merge15` (main 5c73245da with
  the glue of the correction warps, the duplicate `Proof2/Lib` files `ShapeBar`, `ShapeTc`,
  `UbLast` removed in favour of `Lemmas/Flow/Step/ShapeTc.lean` and `Lemmas/Kernel/UbLast.lean`),
  and the Correction lane's head 05b790ffa is merged on top: its `corr_sst` override (the final
  stage's vector stores and the LSE stores, which main's lane L round 5 `site_shape` no longer
  proves), the scoped role macros, the ledger closed forms and `Ref`/`Expect`/`ref_next`. The
  merge keeps this branch's machine without the scan counts `ns`/`nv` (the Correction lane's
  commits after c929ce80d do not touch them); the only conflict was an import line of
  `Correction/Shape.lean`. Lane L's test `Tests/Flow/SiteFamily.lean`, which came with the
  Correction lane's copy of lane L round 5 but is not on main, is left out (lane L's file).

### The correction warps followed (lane T1)

- `Proof2/CorrWarp/` (lane T1; the Correction lane's directory is unchanged): every lane of a
  correction warp `w` (8 to 11) is followed by the thread machine and holds its reference
  invariant (`CorrWarp.good`, `Frame.followedOn` for the lanes of warp `w`, order by the warp
  collectives as for warps 12 and 13). `Common/Migrated.lean` `good_migrated` states it for
  every lane of warps 8 to 13 (`RefAll`); it replaces `Mma.good_migrated`. Axioms: `propext`,
  `Classical.choice`, `Quot.sound`.
- **Premise `CorrWarp.DataSrc`** (a hypothesis of `good` and `good_migrated`, not an
  assumption): at a correction state that holds `Correction.Ref`, a statistics read returns a
  real `f32` payload (a positive one at a row-sum read) and a Tensor Memory load returns real
  `f32` payloads (`Correction.ExpectD` at the data sites). Their sources are the softmax warps'
  statistics writes (a row with a finite maximum has a row sum of at least 1) and the kernel's
  `TcLdDataflow` assumption; the softmax fragment and the Tensor Memory protocol discharge it.
- Thread ledger: `Cls.corr c` counts the Correction lane's classes (`Correction.cls`), so the
  role's counts are `rc n = fun c => n (.corr c)` and the counted thread machine bumps them as
  `Correction.MC` does; `Common/Frame.lean` `corr_nb_ne` (the named barriers 3 to 10 are not the
  startup's barrier 0) keeps them zero through the startup.
- `Ref` (thread level): `StartAt L w` with zero correction counts at a startup state; at a role
  state, unless an event so far was undefined behaviour, `Correction.Ref` on `rc n` and the
  reference values `CFits` (`Fits.lean`): the output warp's `Fits` of `toE d` (the scan state with
  the output warp's site of the correction site, `Sim.lean`), with the ballot count shifted by
  the rescale ballots before the state (`RvAt`: two per round done plus those of the current round,
  `rvN` of the block count from the final stage to the LSE, the picked tile's in the second pass),
  and the used-K word equal to the launch's from its read to the second pass.
- `Sim.lean` `succ_scan`: at the scheduler sites the correction step is the output warp's step of
  the scan state once `ctaR = ctaW` (`ctaR_eq`). `cfits_next` covers the rest: the rounds and the
  final stage through the Correction lane's `succ_cases` and one evaluated table (`RtP`, `rt_ok`:
  every listed move stays in the rounds or the final stage, at the output warp's first stage poll,
  and passes the rescale ballot it fires), the entry and the end of a round by the counter
  (`neg32_eq`, `i32_addi`, `ne_m1`), the end of the final stage by `Epilogue.fits_pass2` and
  `bs_ref` (the rounds' block count is the picked tile's).
- Positions (`Pos.lean`): a scheduler or end state is the output warp's state of its pass with the
  picked tile's rescale ballots `rvC` in the second pass, the same on every lane of the CTA
  (`rvC_cta`); a state of the rounds or the final stage is after the CTA's choice with fewer than
  `rvC` rescale ballots at a rescale ballot (`rt_band`). `cshfl_lt_vote`, `cshfl_lt_exit`,
  `cvote_exit`, `cshfl_same`, `cvote_same` follow from the output warp's lemmas on `toE`.
- Sources (`Src.lean`): `cshfl_recv`, `cvote_bits` are `Epilogue.shfl_recv`, `vote_bits` for a
  correction lane; the reads' launch words use a second shape table with the read addresses
  (`Read.lean`, `EvR` by `site_shape`: the Correction lane's table states the scheduler reads
  without addresses), `Epilogue.expect_word`, `expect_q` and `inputReadValue` for the used-K word.
- Site predicates added to the namespace `Correction.Site` (for dot notation): `sched`, `late`,
  `hasUk`, `isRvote`, `quiet`, `fin`, `isVote`, `data`.
- Size: `Proof2/CorrWarp` 1,902 lines.

### Lane T1 status and remaining (2026-11-21)

- Lane L round 6 (edc9fd0d7) is merged. The startup's tensor-map prefetch is the library's
  `Seg.prefetchTensorMap` (the kernel keeps only the map facts from `Pre.maps`), and `st_close`
  is gone: `sym_close` closes values read under `explicitParams … = L` itself.
- `Common/Frame.lean` `start_step_of`: the startup step of every warp with the warp index, the
  role's counts that stay zero and the role's first facts as hypotheses; the output, MMA and
  correction warps' `start_step` are instances.
- Lane L round 6 changed `RetKind.accepts` to range over `Flow.recvAll` (a Tensor Memory load's
  elements); `Mma.accepts_of` reads it so. Sizes after this step: Epilogue 5,068, Mma 5,064,
  Common 1,025, Startup 1,112, CorrWarp 1,839 lines.
- T3 (`MbarRing.UnitHandoff` for the output stages' ready and free barriers): not done. The
  library's route (`Unit.Gate`) needs `Obj.src`, that every record of the barrier object is a
  declared producer's arrival, an initialization or a poll: a write frame over every thread.
  The loader and softmax warps are still stubs whose events after their first are not followed,
  so no fact about their arrivals exists yet. The count side is ready (`Epilogue.stage_budget`,
  the correction warps' arrival closed forms in `Correction.RefQ`); the instance waits for the
  loader and softmax fragments.
- Task 3 (glue of the loader and softmax fragments): neither exports a complete fragment yet.
  The loader (branch `tmlfa4-loader-proof2`) proves `StepAt` at every state but the first
  block's V arrival; the softmax (branch `tmlfa4-softmax-proof2`) lacks the numeric sites and
  the shape table. The interface stays the one of "Fragment interface for the other tml-fa4
  lanes"; with the correction warps the thread ledger also has `Cls.corr`.
- Remaining trims (Epilogue toward 4.0k): the collective source is now in three copies
  (`Epilogue.votes_le`/`shfls_le`/`shfl_recv`/`vote_bits`, `Mma.mshfl_src`/`mvote_bits`,
  `CorrWarp.votes_le`/`shfls_le`/`cshfl_recv`/`cvote_bits`) that differ only in their position
  lemmas: one generic lemma over a position interface (plan L3) removes about 250 lines from each
  of the output and MMA warps; `isColl_vote` can use lane L's `voteWith`
  (`Lemmas/Kernel/FullVote.lean`); `Select.lean` (808 lines of number facts) is not measured.

### Lane T1 round 7 (2026-11-21)

- Base: `ps-merge17` (main acf2c9865 with lane T4's `Proof2/Progress`, `Proof2/Lib/PollsOn.lean`
  and `WaitReg.lean`, merged with d826f6cf4).
- One collective source for every warp (`Common/Coll.lean`): `shfl_src` finds the source lane's
  shuffle of the instance and `vote_src` every lane's ballot of the instance, each at a followed
  position with the instance's counts, from the order `μ` (`GoodUpTo`) and three position facts the
  role gives as "cannot happen" at a followed position of a lane of its warp in the CTA (a ballot
  past at most the shuffles and exactly the ballots of a shuffle state, a shuffle past at most the
  ballots and exactly the shuffles of a ballot state, a return past at most both counts).
  `vote_src` takes the role's fact `P` about each lane's predicate (`hB`) and builds the mask
  instance itself. The output warp's `votes_le`/`shfls_le`, the MMA warp's inline copies and the
  correction warps' `votes_le`/`shfls_le` are deleted; `shfl_recv`, `vote_bits`, `mshfl_src`,
  `mvote_bits`, `cshfl_recv`, `cvote_bits` are instances (the output warp's three position facts
  are named lemmas, `no_vote`, `no_shfl`, `no_exit`). Library candidate for lane L: the two
  lemmas are generic over the kernel except for `thread p L` and `lane_facts`.
- `isColl_vote` matches the full mask through lane L's `voteWith` (`isFullVote_eq :
  isFullVote = voteWith (2 ^ 32 - 1)`, `rfl`) and no longer takes the mask as a hypothesis.
- Sizes: Epilogue 4,984 (from 5,068), Mma 4,997 (from 5,064), CorrWarp 1,757 (from 1,839), Common
  1,171 (from 1,025).
- Loader glued (branch `tmlfa4-loader-proof2` merged at 4ce0771c2): `Role.loader (b : Bool)`
  (warp 15 for `true`, 14 for `false`, `Loader.wOf`), `frag … (.loader b) := Loader.F p L g b`,
  the gate `x1 = sharedBase ∧ (x3 = 14 ∨ x3 = 15)`; `roleOf` takes the startup state, since the
  loader's fragment is chosen by the warp word the dispatch compared (`.loader (x3 == 15)`).
  `Common/Sound.lean`: `frag_steps … (.loader b) := Loader.steps hp hg b d` and the hand-off case
  (`Loader.handoff` after rewriting the gate's warp word to `wOf (x3 == 15)`). Closure check:
  `loader_sites` (the event instructions of `loaderDecl`'s region, 543 pcs, are `loaderSites`)
  and `Loader.site_mem` (every constructor of `Loader.Site`). The role constructors' matches in
  the output, MMA and correction warps' `Ref` and the positional `rcases` patterns gain the loader
  case (`False` at a loader state: no lane of warps 8 to 13 passes the loader's gate); the same
  one-line additions are made in lane T4's `Progress/OutputColl.lean` and `Progress/Time.lean`
  (the loader's time is the untimed roles' `scanBase`), which do not build otherwise.
- Not done for the loader: following warps 14 and 15 (`good`, `good_migrated` for them). The
  loader's shape table (`Loader/Shape.lean`) covers only the scheduler, the request's reads, the
  drain and the exit; following needs every site's shape (the local loads and stores of the
  page-table and pointer loops, the copies, the TMA groups, the slot waits) and the sources of its
  returned words: the page-table words from the launch (read-only input), the pointer loops'
  `ld.local` words from the lane's own earlier `st.local` (a protected-read source over local
  memory, plan G5, not in the library yet), the scan's collectives by `Common/Coll.lean`. This
  waits for the loader lane's shape table.
- For lane T4 (interface requests of "Remaining, by the fragment it waits for"):
  - First-pass collective bound: `Epilogue.fits_coll_le` (`Select.lean`): a state with `Fits` at a
    site of the first pass (`Epilogue.Site.late = false`, the same function as `Progress.Out.late`
    and `Mma.lateE`) is past at most `7 * (p.batch + 3) + 6 = cmax p` collectives; from it
    `CorrWarp.ccoll_le`: a correction state with `CFits` outside the rescale rounds and the final
    stage (`inRound = false`, `tailR = false`) and not late has `ns + nv ≤ cmax p`. With
    `CorrWarp.good` (every state of a lane of warp `w` in 8 to 11 is followed and holds `Ref`:
    `StartAt` at a startup state, `Correction.Ref` and `CFits` at a role state when no event so far
    was undefined behaviour) this is the correction lane's site and bound at the end of a trace.
  - `CorrPre` as stated asks `collCount n ≤ cmax p` at every correction state with `preReady`,
    which includes the rescale rounds and the final stage. There the full-mask ballots include
    the rescale ballots (two per round, `RvAt`), so the bound fails for tiles with many K/V blocks;
    `corr_before` uses the bound only in its `passTime` branch (the scheduler's first pass).
    Suggested restatement: ask the bound only at states with `Cr.round = false` and no
    `Cr.tailOff`, which `ccoll_le` gives.
  - Warp 0's startup (`StartAt` for the elections and initializations): not done. `StartAt`'s
    fence and barrier cases fix the count of all events (3 and 4), which the output, MMA and
    correction warps' position facts read (a startup state is before the fifth event); warp 0's
    path through the elections has a lane-dependent number of events. It needs a second invariant
    (`StartAt0`: shared base, `x3 = 0`, three shuffles, no ballot, at most the elections' and
    initializations' events) with its own step lemma and a copy of `start_recv` over it, about 250
    lines; next round.
- Trim: the output warp's `expect` takes its induction hypothesis only for collectives (as the
  correction warps' `cexpect`), so `expect_local` is gone.
- Sizes at the end of round 7: Common 1,251, Startup 1,112, Epilogue 5,031, Mma 5,001, CorrWarp
  1,779 lines (Common grew by the collective source, the loader's site list and its closure
  check; Epilogue by the first-pass bound, 64 lines).
- Remaining (lane T1), in order:
  1. Epilogue toward 4.0k: not reached. What is left is not duplication between warps: the
     largest files are `Select.lean` (870 lines of word arithmetic for the scan, the ballot and
     the coordinates, each step a different code term), `Next.lean` (the per-site preservation of
     `Fits`, the `ref_cases` shape of plan L2), `Warp.lean` and `Machine.lean` (value tables,
     plan L5's generator). The 4.0k target needs lane L's `ref_cases` and the generated tables.
  2. Follow the loader warps once their shape table covers every site (see above), then extend
     `good_migrated` to warps 14 and 15.
  3. Glue the softmax warps when their fragment is complete (numeric sites, `stop_iff`, steps
     of the count conjuncts are open on `tmlfa4-softmax-proof2`); it discharges
     `CorrWarp.DataSrc`.
  4. T3 `MbarRing.UnitHandoff` for the output stages' ready and free barriers: needs every
     writer of those barrier objects followed (loader and softmax included), as recorded before.
  5. `StartAt0` for warp 0 (lane T4's request).

### Lane T1 round 8 (2026-11-21)

- Base: f00b5f224 (round 7) with the loader lane's shape table and packet-row invariant merged
  (`tmlfa4-loader-proof2` at 5077a1623, no conflict).
- Warp 0's startup (`Common/Start0.lean`). `StartAt0 L s n`: before the third shuffle it is
  `StartAt L 0`; at an election, an initialization, the fence and the barrier it states the three
  shuffles, the shared base as `x1` and the warp index 0 as `x3`, and no count of all events (an
  elected lane makes two or three more events per election). `start0_next` is the startup step
  of a lane of warp 0 up to the barrier, `start0_step_of` the step obligation for any reference
  invariant whose startup states are `StartAt0` (the softmax warps' lanes of warp 0 will use it),
  `Start0Cls` the classes a startup event of warp 0 counts (with the elections won and lost and,
  for an undefined-behaviour event, the output warp's store class, which counts faults).
- The startup's shape table now has entries for the elections (a full-warp election at the site's
  pc, or undefined behaviour) and the initializations (an initialization of some mbarrier, or
  undefined behaviour). The initializations take their count from a register, so the library's
  `shape_mbInit` (immediate count, address read from the facts) does not apply; the inversion
  `shape_mbInitAny` is in `Proof2/Lib/ShapeInit.lean` (library candidate for lane L, registered
  with `site_shape`'s hook `shape_inv`). `Startup.elect_ev` is the MMA warp's `elect_ev` at the
  startup; the MMA warp keeps its own copy until lane L promotes one.
- `start_recv_of` (`Common/Frame.lean`) is `start_recv` over any startup invariant `S` that fires
  no ballot and no return and is `StartAt` before the third shuffle, and it takes the induction
  hypothesis only for events with fewer collectives up to them (`upTo_of_lt`); `start_recv` and
  `upTo_of_prev` are its instances, so no caller changed. The strict hypothesis is what lets warp
  0's following stop at the barrier: a lane past its barrier has three collectives, so it is
  never needed for an event of the startup.
- Every lane of warp 0 is followed through its startup (`Start0Ref`: `StartAt0` and no ballot at a
  startup state, three shuffles at a role state): no lane is bad at a position with at most two
  collectives (`start0_noBad2`, induction on `lexOrder μ`), hence none at a startup state
  (`start0_noBad`: such an event has at most three collectives up to it), and before its first
  event on CTA barrier 0 a lane is followed and at a startup state (`start0_state`; the step at
  the barrier's site is a barrier-0 event by the shape table). `warp0_before_bar` states it for a
  lane with no barrier-0 event: no exit, every followed state a startup state with `StartAt0` and
  a pc at most 173.
- `Progress/Warp0.lean` (new file next to lane T4's `StartAll.lean`, no edit of T4's files):
  `warp0Lag : Pre p L m → Warp0Lag p L m`, so `Warp0Lag` is no longer an open premise.
- Sizes: Common 1,868 (from 1,251; `Start0.lean` 587), Startup 1,145 (from 1,112), Lib 242 (with
  the loader lane's `ShapeAsync.lean`), Progress 1,743 (`Warp0.lean` 50).
- `CorrPre` restated (lane T4's `Progress/Ready.lean`, minimal edit): the first-pass bound
  `collCount n ≤ cmax p` is asked only at correction states with `Cr.round = false` and
  `Cr.tailOff = none`, the states whose time `corr_before` computes from the collectives
  (`passTime`); in the rescale rounds the full-mask ballots include the rescale ballots, so the
  old bound failed for tiles with many K/V blocks, and there the time does not read the count.
  `corr_before` takes the guarded bound; `readyLag_of` is unchanged. `Progress/CorrPre.lean`
  (new, lane T1): `cr_out` (a site outside `Cr.round` and `Cr.tailOff` is outside the reference's
  `inRound` and `tailR` pc ranges, by evaluation per site) and `corr_coll`: at a correction state
  holding `CorrWarp.Ref` with no undefined behaviour so far, the guard and `Cr.late = false`
  (which `preReady` gives outside the final stage) give `collCount n ≤ cmax p` (from
  `CorrWarp.ccoll_le`). So lane T4 discharges `CorrPre`'s bound from `CorrWarp.good` at the end of
  the trace; what remains of `ReadyArrive` is the hand-off (a correction lane that has not arrived
  while the phase is even) and the site being `preReady`.
- Lane L round 7 merged (`lane-L` at 76f288d60). Its promotions replace kernel copies:
  `Proof2/Lib/PollsOn.lean` and `Proof2/Lib/WaitReg.lean` (lane T4's) are deleted, and
  `Progress/OutputPoll.lean` and `Progress/MmaPoll.lean` import `Lemmas.Kernel.Progress.PollsOn`
  and `Lemmas.Flow.Step.ShapeRegs` instead (import lines only); `Mma/Warp.lean`'s `AllocT`,
  `allocT` are deleted for `Lemmas/Flow/Step/Alloc.lean`'s; `Common/Frame.lean`
  `exists_of_count` is the library's `Frame.exists_of_count` instantiated to the thread machine.
- The local-memory source the loader's pointer loops need is lane L's
  `Lemmas/Kernel/Source/Local.lean` (lane-L 7bdc0a125, merged): an `ld.local` byte is the byte of
  the thread's last earlier covering `st.local`, under `LocalOwned X`; for tml-fa4 that premise is
  the kernel's `localWriteOwner` (`Proof/GlobalWrites.lean`: every write of a local byte is an
  ordinary store of the thread that owns it, from the decoded program's static checks and
  `Consistent`, no completion). No kernel-local copy is written; `localWriteOwner` and its static
  checks move into Proof2 at the switch.
- Not done this round: following the loader warps (their `good` and `good_migrated` for warps
  14 and 15). It needs the loader fragment's `ref_next` (the loader lane's round 4: the quiet
  page and pointer steps, the slot waits, the copy arrivals and round ends, warp 14's TMA groups,
  the drain), and on lane T1's side, as for the MMA and correction warps, the scan's reference
  values on the output warp's (`Sim`: the loader's scheduler step is the output warp's step of its
  recorded `Epilogue.D`; `Fits`, positions, the collective sources by `Common/Coll.lean`), the
  page-table words by `inputReadValue` and the pointer loops' local words by
  `Frame.local_read_of_last_store` with `localWriteOwner`. The softmax fragment
  (`tmlfa4-softmax-proof2`, last commit cd19594bc) has no `ref_next`, hand-off or numeric sites
  yet, so it is not glued, and the T3 unit hand-offs for the ready and free barriers still need
  the loader and softmax warps followed (every writer of those barrier objects).

### The switch: remaining premises (lane T1, 2026-11-21)

(Round 9 replaced the safety fields of this table by one field per class of `Unsafe`, see "Safety
by class" below; the old fields are now `Bridge.OldPremises`.)

`Proof2/Top/Correct.lean` proves `correct2 : Pre p l m → SafePremises p l m → ProgressPremise l m →
ResultPremise p l m → Correct kernel Assumptions.all l m (Post p m)`, the statement of
`Theorem.lean`'s `correct` with the open facts as named premises. `Proof2/Top/Safety.lean` proves
`SafeGoal` from `SafePremises` with no `Maximal`, `Complete` or extension: it is the old assembly
of `Proof/Correct.lean` with each completion-derived fact replaced by a field, and
`Safety.unsafeCases` restated with warp convergence as a hypothesis instead of completion (the
only use of completion inside it). The gap to the switch is this list.

| Premise | Statement (every consistent execution) | Discharge in Proof2 | Waits for |
|---|---|---|---|
| `SafePremises.noFault` | no `Thread.DecodedFault` | `ref_safe` at every followed state (plan G9), all roles followed | loader `ref_next`, softmax fragment |
| `loaderFallback` | `Thread.LoaderFallbackAddresses` | the loader's scan `Fits` at its CuQ reads, as `Epilogue.Reads` | loader following (above) |
| `softmaxFallback` | `Thread.SoftmaxFallbackAddresses` | the softmax warps' scan `Fits` | softmax fragment |
| `correctionFallback` | `Thread.CorrectionFallbackAddresses` | `CFits` at the correction reads (`CorrWarp.good`, `Read.lean`) | `CorrWarp.DataSrc` (softmax `RowSumPos`, `TcLdDataflow`) |
| `noWarpDivergence` | `¬ WarpDivergent` | the collective source on two lanes at the poll branches, with `pollAgree` | every role followed |
| `noAlignedWork` | `¬ Thread.AlignedWorkBarrierMismatch l X 8` | softmax lanes' common sequence (collective source) | softmax fragment |
| `softmaxTensor` | `Thread.SoftmaxTensorAlignment` | the same | softmax fragment |
| `ProgressRest` (replaces `ProgressPremise`, round 40) | nine fields (`mmaQ` removed, round 41): `mmaSoft`, `loader`, `softmax`, `correction`, `mma` (non-poll states), `epilogue` (non-ready states), `start`, `blocked`, `async` | `Top/Assembly.lean` proves `ProgressGoal` from them, `SafePremises` and safety; proved inside: the MMA warp's K/V polls (`kv_lag`), the output warp's ready polls (`readyArrive`), stopped machines (`dead_steps_inOrder`) | T1 (mmaQ, loader), ex-Inkling (mmaSoft), others by role |
| `ProgressRest` (replaces `ProgressPremise`, round 40) | ten fields: `mmaQ`, `mmaSoft`, `loader`, `softmax`, `correction`, `mma` (non-poll states), `epilogue` (non-ready states), `start`, `blocked`, `async` | `Top/Assembly.lean` proves `ProgressGoal` from them, `SafePremises` and safety; proved inside: the MMA warp's K/V polls (`kv_lag`), the output warp's ready polls (`readyArrive`), stopped machines (`dead_steps_inOrder`) | T1 (mmaQ, loader), ex-Inkling (mmaSoft), others by role |
| `ResultPremise` | `Complete → Result.OutputValues ∧ Correction.LseWriteValues` | the output and correction warps' `Ref` at their store sites, with the softmax values | softmax numerics |
| bound | `BoundGoal` | `terminates` (`Proof/Termination.lean`, no completion premise) | moves at the switch |

**Lane T1 round 22 (2026-11-22): the coordinator's order for the result, bound and progress
premises, and what each needs.** Step 1 (the safety field in progress) is `noBarMismatch`, done in
round 21. Findings for steps 2 to 4, from the Proof2 sources:

- `ResultPremise` (step 2). `Result.OutputValues` is the value `attention p b h row d` at every
  output byte, and `Correction.LseWriteValues` the log-sum-exp from the final row maximum and sum.
  The Proof2 reference invariants do not carry these values: `Correction.V` records the
  accumulator elements it loads (`xs`, `ys`) and the row statistics it reads (`rs0`, `rm0`, `rs1`,
  `rm1`) as arbitrary reals, and `CorrWarp.DataSrc` asks only that a Tensor Memory load returns
  `f32` reals and a row-sum read a nonnegative one. Relating them to the inputs needs which write
  each of these reads observes (the statistics stores of the softmax warps, the MMA warp's
  accumulator writes, the correction warps' own rescale stores), that is the shared-memory and
  Tensor Memory hand-offs and the write frames of step 5, and the softmax warps' numeric values
  (`SmWarp.NumAll`). The old tree's proof of these values (`Proof/Result`, 8 files, 814 lines) sits
  on its protocol and history files (`RepeatedNormalizedRows`, `RepeatedProbabilityHistory`,
  `RescalePublicationValues`). Decision: step 2 comes after the hand-offs and frames. The move of
  `postOfValues` off `Proof/Result/Post.lean` does not depend on the values; it needs
  `outputIntentFootprint`, `outputHasWriter`, `lseOutputByte` and `usedKProtected` on Proof2,
  which are write-frame facts (step 5).
- `terminates` (step 3). The old bound is a per-role budget of counted events
  (`Proof/RoleCounts.lean`, `LoaderRoleCounts.lean`, each a closure into the old role proofs). On
  Proof2 it is a potential per role machine state that every counted event lowers: the scans'
  rounds (at most `batch + 2`), the K/V blocks (`bmax`), the softmax rounds (`nB + nP`), the
  loader's pages. The progress lane's time table (`Progress/Time.lean`) does not time the softmax
  and loader warps and its time is not strictly increasing, so it is not that potential.
- `ProgressPremise` (step 4). `MmaFullLag`, `ReadyArrive` and the loader's waits relate an
  mbarrier's phase to its producers' arrivals: the unit hand-off declarations
  (`MbarRing.UnitHandoff`, `Sched.Lag`) over the producers' arrival counts and the consumers'
  successful polls in the thread ledger. The same declarations give the credit chain of
  `noCtaBar` (a softmax warp's next `bar.arrive` on its named barrier after its correction warp's
  `bar.sync` of the same ordinal) and the phases of `noTma`.
- Order taken: the unit hand-off declarations first (they unblock step 4, `noCtaBar` and `noTma`),
  then the write and access frames (step 5's classes and the moves for step 2), then the values
  (step 2), then the bound (step 3).

**Lane T1 round 23 (2026-11-22): `ReadyLag` and `ReadyArrive` were false as stated.** Both
asked, for every lane of warp 13 and stage `st`, that while the ready barrier's phase is even some
lane of the CTA has not exited. A CTA without a tile (the launch grid
`(totalQ + 255 · batch) / 256 · heads` can exceed the number of tiles) never arrives on its ready
barriers, and all its lanes exit, so no lane qualifies once they have. Its output lane never
polls them either, and `ready_pollBlocked`, the only user, has the lane at its ready poll. Both
premises now take that lane's state at the end of its trace at the ready poll of stage `st`
(`Progress/OutputPoll.lean`, `Progress/Ready.lean`). `correct2`'s statement is unchanged
(`ProgressPremise` is abstract).

**Lane T1 round 24 (2026-11-22): the object histories, first the ready barriers.** The 34
objects and their counts, read from the PTX's `mbarrier.init` instructions (offset from the shared
base: count): 0, 8: 1; 16, 24: 1; 32, 40, 48: 64; 56, 64, 72: 1; 80, 88: 1; 96, 104: 256;
112, 120: 4; 128, 136: 1; 144, 152: 1; 160, 168: 128; 176, 184: 128; 192, 200: 128;
208, 216: 128; 224, 232: 32; 320, 328: 1; 336, 344: 4. The kernel has no `mbarrier.inval`.
`Top/MbarUse.lean` now gives the offsets each role names (`SoftOff`, `MmaOff`, `LdOff`; the
output warp's ready and free barriers by site, `epi_site`). The ready barriers (208, 216) are
named only by the output warp's ready polls and the correction warps' `fdone st 1` arrivals.
The pieces of a ready barrier's history (`MbarRing.Unit.History`), in order: the publication of
the startup's initialization to every other use (from `noUninit`'s hand-off, as a lemma); the
initialization's uniqueness and count (the startup's init sites by the elected lane, the count
register's value at the site); `InitFirst` from the two (the FA4 proof's
`initFirst_of_published`, generic over the kernel: a lane-L candidate in `Proof2/Lib`); the
record sources (`record_source` with the role classification); then `ReadyArrive` from the
arrival count (a phase-0 history has a correction lane of the CTA without its arrival record,
so before its `fdone st 1` site: not exited, `preReady`, and `corr_coll`'s bound).
Check times: `Correction/Shape` 837 s, `ShapeFinal` 793 s, `ShapeRound` 621 s, each one `lean`
process alone, but on a machine at load 390 on 224 cores; all three are defects to cut.

**Lane T1 round 25 (2026-11-22): the correction shape files cut, and what a site costs.**
`Correction/Shape.lean` keeps the table and the tactics; its five `site_shape` theorems and those
of `ShapeRound.lean` and `ShapeFinal.lean` (deleted) are 33 files of at most ten sites
(`Correction/ShapeSet/`, from a generator kept outside the tree), each substituting its sites from
a membership hypothesis and calling the step on each (`corr_step`, `site_shape`'s step without its
enumeration of every site); `Shapes.lean` dispatches (30 s). Times under the build at load ~390
on 224 cores: `Shape` 6 s; the Tensor Memory groups `Fld*`, `Rld*`, `Rst*`, `Rldw*` 100 to 250 s
(8 sites each), the others 3 to 41 s. A Tensor Memory site costs about 26 s alone
(`.fld 0 3`, profiled): 15 s of it are twelve `contradiction` calls of about 1.3 s each on the
site's large context, inside the library's step (`site_shape_step`'s side-goal closers, through
`split_ifs`), 4.6 s `simp`, 2.8 s `assumption`. Cutting files further does not lower that; the
lever is the library step (a lane-L item: avoid `contradiction`/`split_ifs` on the full context,
or clear the register table before the closers). Recorded as a defect still open.
Also this round: `Lib/InitFirst.lean` (`initFirst_of_published`, the FA4 proof generic over the
kernel, a lane-L candidate), `Top/MbarStart.lean`'s `init_cnt` (each initialization's object
and count, from the count register's value) with `Lib/MbarInit.lean`'s `fires_mbInit_cnt`,
`Top/Mbar.lean`'s `use_pub` (the publication of the startup's initialization to every other use,
as a lemma; `noUninit` uses it), and `Top/MbarInitOne.lean`: no role fires an initialization, a
startup state at an initialization site is of warp 0 (`jr_init`), a lane there has won an
election (`init_won`), and a startup state has no barrier-0 event before it (`start_nobar0`).

**Lane T1 round 26 (2026-11-22): every object is initialized first.** `Top/MbarInitOne.lean`:
every `mbarrier.init` event is the startup's, at initialization site `q` of a lane of warp 0 that
won an election, initializing `obj (initOff q)` with `initCnt q` (`init_event`); that lane
initializes each object at position `initPos q` only (`init_pos`, by `lead_path` and
`start_nobar0`); the winners of one warp are one lane (`elect_winner`), so each object has one
initialization event with one count (`init_unique`); every other use has it published
(`pub_of_use`, from `use_pub`); so `obj_initFirst`: `PairTmaRing.InitFirst X (obj L g (initOff q))
(initCnt q)` for every object of every CTA, under the softmax premises `Top.correct2` already
takes. This is the `init` field of every object's history (`MbarRing.Unit.History`) and the
`hfirst` premise of `noTmaUnsafe_of_first`. 5.4 s.

**Lane T1 round 27 (2026-11-22): `ReadyArrive` is proved.** `Top/ReadyObj.lean`: no event
invalidates an mbarrier (`no_inval`); a ready barrier is named only by the output warp's ready
polls (parity 0, its first successful poll) and the correction lanes' `fdone st 1` arrivals
(`ready_use`), so it is a unit object of the CTA's 128 correction lanes with offset 0
(`readyObj`: `MbarRing.Unit.Obj`); each correction lane arrives on it once (`ready_arr_zero`).
`Top/ReadyArrive.lean`, `readyArrive`: under the softmax premises, `Progress.ReadyArrive p L m`.
For a lane of warp 13 at its ready poll: the history is not empty (the startup's
initialization), its phase is at most 1 (`Obj.phase_le` with the reuse premise vacuous, no lane
arriving twice), so at an even phase it is 0 and some correction lane has no arrival on it
(`Obj.blocked`, the history fault-free by `Obj.fault_free` with a vacuous gate); that lane has not
exited (an exit on the tile's path comes after the arrival; the CTA has a tile, which the output
lane's `Fits` at its ready site says, and a correction state on the path without one would say
otherwise, `corr_noTile_noPicked`), its machine is live (`corr_live`, `CorrWarp.next_none`), and
its state is at or before its arrival (`corr_sites_ready`) with the first pass's collective bound
(`Progress.corr_coll`). Times: `ReadyObj` 9.8 s, `ReadyArrive` 5.6 s. `ProgressPremise` is still
abstract in `Top.correct2`; with `readyLag_of` this discharges the `ReadyLag` premise of lane
T4's output-poll step. Remaining progress premises: `MmaFullLag` and the loader's and softmax
warps' waits.

**Lane T1 round 28 (2026-11-22): `MmaFullLag` split by producer.** `Progress/MmaPoll.lean`:
`MmaLagFrom b` is `MmaFullLag` at the polls whose producer is the loader (`b = true`, offsets
below 96: the Q stages at 0 and 8, the K/V ring at 32 to 48) or a softmax warp (`b = false`,
96 to 120); `mmaFullLag_of` assembles them. The softmax side stays a named premise (the softmax
warps' times are not in the time table). For the loader side, the library's `PairTmaRing` does not
fit: it is the `cta_group::2` pair ring of FA4. The K/V ring's full barriers (count 64) take only
the loader lanes' `cp.async.mbarrier.arrive.noinc` (six in the PTX), which is
`MbarRing.NoIncObject` (`Lemmas/Protocol/CpAsyncPhase.lean`); the Q stages' full barriers
(count 1) take one `mbarrier.arrive.expect_tx` and the tensor copies' completions, a one-CTA TMA
unit for which the library has no structure yet. A blocker at a failed MMA poll on these is a
loader lane that has not arrived (the loader lanes are not timed, so their time is the first
scan's base, below every MMA pipeline time) or a pending tensor copy (`Descent.Obl .tensor`).
Old tree: `Kernels/TmlFa4Fwd/Proof/` is 2,033 files, 366,902 lines, all reachable through
`Theorem.lean`'s import of `Proof.Correct`; nothing can go before `Proof/Correct.lean` points at
`correct2`.

**Lane T1 round 29 (2026-11-22): the pending `cp.async` arrive-on as a blocker.** Core runs the
arrive-on of `cp.async.mbarrier.arrive{.noinc}` as its own asynchronous stage
(`.async j .arriveOn`, after the tracked copies' writes), so a loader lane may exit with it still
pending, and an MMA poll on a K/V full barrier then has no blocker of `Sched.Blk`'s kinds (commit,
MMA, tensor, store obligations, or an earlier pending thread). The old tree excluded the case by
maximality (`pending_cpAsyncArrive_extendsInOrder`, `Proof/Progress/Async.lean`); the new descent
has no maximality, so the open arrive-on is the blocker. `Sched.Blk` and the one lemma that
carries an obligation over a failed poll (`obl_failedPoll`) are in `Lemmas/Kernel/Progress/Poll.lean`;
the obligation kind exists (`Obligation.arriveOn`, `Lemmas/Kernel/Obligation.lean`). The fix is
to add `.arriveOn` to `Blk`'s list and its case to `obl_failedPoll` (an `AsyncArrive` event and
`X.async.arrived` are unchanged by an appended failed poll). That is a `Lemmas` edit, which is
lane L's: requested; `MmaLagFrom true` is stated against `Sched.Blk` and picks the fix up
unchanged.

**Lane T1 round 30 (2026-11-22): the loader's objects.** `Top/KvObj.lean`: a K/V full barrier
(offsets 32, 40, 48) is named only by polls (the MMA warp's `wt` sites, `mma_kv`; the loader's)
and the loader lanes' `cp.async.mbarrier.arrive.noinc` (`ld_kv`), with no CLC request anywhere
(`no_clc`), so it is `MbarRing.NoIncObject X (obj L g o) 64` (`kvObj`, 7.7 s).
`Lib/TmaUnit.lean`: `MbarRing.TmaUnitObject`, a one-CTA TMA unit (records: initialization,
polls, a producer's unit arrival expecting the use's bytes, tensor copy completions; initialized
first with count 1) and its `of_issues` classification (a lane-L candidate). What the loader half
of `MmaFullLag` needs beyond these: per object, a blocker at a failed poll from the history's
counts. For the K/V ring: the arrive-ons of each use are the 64 loader lanes', so a phase short of
the MMA lane's use has a loader lane that has not issued its arrive (a pending thread, the
loader's time being the first scan's base) or whose arrive-on is open (`.arriveOn`, lane L's
`Sched.Blk` change); the library has no lemma counting a no-increment object's arrive-ons per
issuing thread (as `Unit.Obj.blocked` does for thread arrivals): a lane-L candidate. For the
Q stages (offsets 0 and 8): the classification needs the softmax warps' objects by kind (as
`corr_mbar`; `soft_obj`'s offsets include 0 and 8, the table's values at sites without a
barrier), then the arrival-or-bytes blocker (a pending loader lane or a `.tensor` obligation).

**Lane T1 round 31 (2026-11-22): the Q stages are `SingleTmaRing` slots.** The library's
`Lemmas/Protocol/SingleTmaRing` (generalized from the Inkling KV ring) is a one-CTA TMA ring
slot: a full barrier (count 1, one arrival expecting the use's bytes, the copies' completions)
and an empty barrier (count 1, one commit of the consumer). A Q stage is one: full at offset 0 or
8 (`qObj`'s classification: the loader lane's expect-tx arrival and tensor copies), empty at 16 or
24 (the MMA warp's commits `cmO 7`, `cmO 8`, polled by the loader's `tw` sites). So the plan for
the Q side of `MmaLagFrom true` uses `SingleTmaRing.Hyp` (its blocker and ring lemmas) instead of
`Lib/TmaUnit.lean`, which stays as the record classification only. `Hyp`'s guards are the roles'
count closed forms: the loader's arrival count below its empty polls at its `ta` sites (the loader
ledger), the MMA commit count below its full polls at `cm 7`/`cm 8` (`Mma.RefQ.com`, `.acq`:
`commitAt`, `acqAt`). For the K/V ring (`kvObj`): the 64 loader lanes' arrive-ons per use and the
MMA's empty commits (`cmO 4, 6, 9`: 56 to 72) form a ring of no-increment arrive-ons; the library
has `UnitRing`/`UnitRingGate` for thread-arrival rings, not for arrive-on rings: the counting of a
`NoIncObject`'s arrive-ons per issuing lane is the missing lemma (to be written in `Proof2/Lib`).

**Lane T1 round 32 (2026-11-22): the blocker argument for the loader half of `MmaFullLag`.**
Done: `Lib/NoIncBlocker.lean` (`NoIncObject.blocked`: some loader lane has no more recorded
arrive-ons than the phase), `Lib/TmaUnit.lean` (`TmaUnitObject.blocked`: with no outstanding
bytes, the arrival units are at most the phase). The argument at a failed MMA poll on a loader
object: any loader lane of the CTA that has not exited is a blocker (the loader lanes are not
timed, so their time is at most the first scan's base, below every MMA pipeline time). If all of
them have exited, their exit counts (`Loader.RefCounts` at `.exit`: `arrAt`, `acqAt` of the
tile's `A` packets) say every arrive-on, expect-tx arrival and copy was issued; then an open
arrive-on is the `.arriveOn` obligation (lane L's `Sched.Blk` change), an issued tensor copy not
yet notified the `.tensor` obligation, and otherwise the object's history is complete, which
contradicts the poll's parity only with the ring bound: a K/V full barrier's phase is at most one
past the MMA lane's polls of it. The bound comes through the empty barriers (offsets 56 to 72,
count 1, completed by the MMA warp's commits alone, `MbarRing.Blocker.commitObj_unitTx`): a
loader lane's successful empty polls of slot `j` are at most the empty object's phase plus the
fresh first use, its phase at most its commit notifications, those at most the MMA lane's commits
to it, which its closed form (`Mma.RefQ.com`, `commitAt`) bounds by its polls of the full slot.
The pieces in order: the empty barriers' users and their commit-object history; the loader's
exit counts; the bound; the byte count of each expect-tx arrival against its group's copies;
then `MmaLagFrom true`.

**Lane T1 round 33 (2026-11-22): the empty barriers, and a lane-lag question for
`MmaFullLag`.** `Top/EmptyObj.lean`: the K/V empty barriers (56, 64, 72) are named only by the
loader's polls and the MMA warp's commits (`empty_use`), so each is a commit-only unit-transaction
history (`emptyObj`, through `MbarRing.Blocker.commitObj_unitTx`; its arrival units are its phase,
`commitObj_blocked`). Writing the ring bound exposed a question about `MmaFullLag`'s form: it is
stated per lane of warp 12 against that lane's own successful-poll count, but the empty
barriers' commits are the elected lane's alone (`Mma.RefQ.com`: `if w then commitAt … else 0`),
so the ring bound ties the K/V phase to the elected lane's polls, not lane `g`'s. A lane `g` that
lags the elected lane by a use would poll a phase two ahead of its count, with the same parity,
and have no blocker. Ruling the lag out needs the MMA lanes' agreement at their polls (the
`pollAgree` sites with `WarpDivergent` excluded, or the warp collectives between rounds), which is
the warp-uniformity fact `noWarpDivergence` is about (now the ex-Inkling agent's). Decision: the
loader half of `MmaFullLag` is stated against the elected lane's count where the ring bound is
needed, and the per-lane form waits for the warp-agreement lemma; recorded for the coordinator.

**Lane T1 round 34 (2026-11-22): the ring bound's loader input.** The bound (a loader lane's
successful polls of empty slot `j` are at most the empty object's phase plus one) is the library's
`okPolls_le` argument (`MbarRing.Poll.record`, `selected_poll_phase_ge`, `phase_mono`) on the
commit-only history of `emptyObj`, given that the lane's successful empty polls alternate with
parity `okPolls + 1` (`SelectedAlternates … 1`, a fresh barrier passes the first parity-1 poll).
That parity is the loader's ring encoding: `SlotIs v j` (`slot = j % 3`, `par = (j / 3 + 1) % 2`)
in the warm and steady rounds and the drain, with the empty polls' count `ringCnt (acqAt s k A)`
(`Loader.RefCounts`), so at a `slot` site of packet `k` the count is `k / 3` and the parity
`(k / 3 + 1) % 2`. The first block's polls (`ringCls = primeK, primeV`) have no `SlotIs` in
`RefRing`; their parity registers (`waitRegs (.slot .prime v)`: 1849, 1926) need their values from
the loader's register table. Next: the parity lemma per poll site (from `RefRing`, `RefCounts` and
the table), then `okPolls_le` for the empty slots, then the bound against the elected MMA lane's
commits (`commitObj_blocked`, `Mma.RefQ.com`).

**Lane T1 round 35 (2026-11-22): the loader side of the ring bound.** `Lib/PollLe.lean`:
`MbarRing.okPolls_le_phase` (any object with fault-free polls, no invalidation and a thread's
successful polls alternating with offset `δ`: that thread's successful polls are at most the final
phase plus `δ`). `Top/LdParity.lean`: the parity of the loader's empty-slot polls (`slot_par`,
`dw_par`: `(j / 3 + 1) % 2` for packet `j`; the first block's are the constant 1, the later ones
the ring's parity word or its successors, `SlotIs`) and `ringCnt_mod`. `Top/EmptyPoll.lean`:
a loader lane's successful empty poll has the parity of its count plus one (`ld_empty_par`, with
the count `ringCnt j (j % 3) = j / 3` from `Loader.RefCounts`), so its successful polls of an empty
barrier are at most the empty object's phase plus one (`ld_empty_okPolls`). Times: 2.8 s, 4.1 s.
Remaining for the bound: the empty object's phase equals its commit notifications
(`commitObj_blocked`), those are the elected MMA lane's commits to it (one notification per
commit; the other lanes commit nothing, `Mma.RefQ.com`), which its closed form bounds by its
successful polls of the full slot; a loader lane's arrive-ons of a slot are at most its empty polls
of it (`Loader.RefCounts`: `arrAt ≤ acqAt`, the first block's polls passing on the fresh barriers);
and a full slot's completed phases hold 64 arrive-ons each (`NoIncObject.completed_count`).

**Lane T1 round 36 (2026-11-22): what the rest of the ring bound reuses.** The library's
`PairTmaRing/CommitBound.lean` is this bound for FA4's pair ring (`full_phase_le_commits`:
the full phase is at most one more than a consumer's commits, through `units_le_arrivals`,
`arrivals_le_okPolls`, `okPolls_le_commits` with `producer_poll` and `notified_commits`), stated
on `PairTmaRing.Hyp` (thread arrivals on the full barrier, one commit per consumer per use).
The K/V ring is the same shape with the full barrier's arrivals replaced by 64 no-increment
arrive-ons per use: the missing library piece is a `NoIncRing` counterpart of `CommitBound`
(arrive-on units ≤ the producers' arrive-ons, each after the producer's empty poll of its use,
`okPolls_le_commits` on the commit-only empty barrier, `notified_commits` for single-CTA commits).
Request to lane L, recorded here; the kernel's inputs are ready: `kvObj`, `emptyObj`,
`ld_empty_okPolls`, `Loader.RefCounts` (`arrAt`, `acqAt`), `Mma.RefQ` (`commitAt`, `acqAt`).

**Lane T1 round 37 (2026-11-22): the library pieces are in; what closes the K/V bound.** Merged
`origin/main` with lane L's `Lemmas/Protocol/NoIncRing.lean` (`full_phase_le_commits`,
`commitObj_phase_le_commits`), `PollLe.lean` and `TmaUnit.lean`; the kernel's copies
`Lib/PollLe.lean` and `Lib/TmaUnit.lean` are deleted (`Lib/TmaUnitBlock.lean` keeps the two
facts the library lacks). `Top/CreditObj.lean`: `credit_use` (the credit barriers 192, 200 are
named only by the softmax warps' polls and the correction lanes' unit arrivals). The K/V bound
from `full_phase_le_commits` needs, per instance: the 64 loader lanes as producers (`hsrc`: an
arrive-on's thread is a loader lane, the loader branch of `kv_use`); `hlane` with `d = 0` (at the
end of a loader lane's trace, `ringCnt (arrAt …) j ≤ ringCnt (acqAt …) j` since `arrAt ≤ acqAt` at
every site; needs the lane's live end state, the loader's counterpart of `corr_live`); `hpoll` from
`ld_empty_okPolls`; `hE` from `commitObj_phase_le_commits` with `c` the elected MMA lane (every
commit to an empty barrier is its: the other lanes commit nothing, `Mma.RefQ.com`, and the
winners of the MMA warp's elections are one lane, `elect_winner`). Then the elected lane's commits
to the empty slot are at most its successful polls of the full slot (`commitAt … (56 + 8 j) ≤
acqAt … (32 + 8 j)`: each release point follows its acquisition point, `ringRel ≤ ringAcq`), so the
full phase is at most its polls plus one. The loader half of `MmaFullLag` for the elected lane
then needs the tile agreement between the MMA warp's blocks (`Bs`) and the loader's packets (`A`)
so that a polled use exists on the loader side (`c_F < ringCnt A j`).


**Lane T1 round 38 (2026-11-22): the K/V ring bound (roadmap B1, first half).**
`Top/KvBound.lean`: `kv_phase`: a K/V full barrier's final phase is at most one MMA lane's
commits to its empty barrier plus one, the lane being of the CTA's MMA warp (warp 12). Inputs of
lane L's `full_phase_le_commits`: `kv_src` (`hsrc`: `kv_use` now also returns that an arrive-on's
thread is a loader lane of the CTA, `ldProd` enumerates the 64), `ld_arr_le_polls` (`hlane`,
`d = 0`: at a loader lane's last followed state the reference invariant gives
`ringCnt (arrAt …) j ≤ ringCnt (acqAt …) j`; the last followed state comes from
`Proof2/Lib/EndState.lean`, `Frame.end_state`/`end_countP`, a lane-L candidate), `ld_empty_okPolls`
(`hpoll`), and `empty_phase` (`hE`: `empty_use` now also returns that a commit to an empty
barrier is by an MMA lane that won an election before it, with `s.mbar` the barrier; two such
lanes are one by `elect_winner`, `empty_one`; a commit's rank is 0, `commit_rank`). An empty
barrier without records has no successful poll (`MbarRing.Poll.record`), so its loader lanes made
no arrive-on and the bound holds with phase 0. Next: the MMA lane's commits to empty slot `j` are
at most its successful polls of full slot `j` (`Mma.commit_le_acq` at its last state), then the
tile agreement and the loader half of `MmaFullLag` (E1). The old-tree wrappers for the safety
fields were tried and reverted: `Top/Safety.lean` imports no old safety case by design, and those
fields belong to other lanes. `kv_bound` (same file) closes the K/V bound: the
final phase of full slot `j` is at most the electing MMA lane's successful polls of it plus one
(`mma_com_le_polls`: at the MMA lane's last followed state, `commitAt … (56 + 8 j) ≤ acqAt …
(32 + 8 j)`).

What the loader half of `MmaFullLag` (E1) still needs, measured: (1) the polls of the lane `g`
at the poll equal the electing lane's (`kv_bound` is for the electing lane; `MmaLagFrom` quantifies
over every lane of warp 12): the warp-12 agreement lemma of roadmap B2 (ex-Inkling lane); until
then E1 is written with that equality as a hypothesis. (2) The tile agreement: at the drain a loader
lane has made `pkts r28` packets (`LFits` `.p2`/`.drain`, `r28 = r28Ref`, the loader's setup of the
picked tile), the MMA lane's ring uses are `2 · max(Bs, 1)` with `Bs` from `Mma.blocks` of its
`sc`/`ukw`; `pkts b = 2 · max(sv b, 1)` by the definitions, so the agreement is `r28Ref = blocks`
on the picked tile. (3) With every loader lane exited and no open arrive-on obligation, the full
phase reaches the packets of slot `j` (the units of the complete history). The loader role's time
is still the placeholder `scanBase`, below every MMA pipeline time, so a pending loader lane is a
blocker as `Sched.Blk` asks.


**Lane T1 round 39 (2026-11-22): the tile agreement and the K/V half of E1.** Merged
`origin/main` 4c2e0d5cb (batch 47; the K/V files there were my 6617f90e3 versions, so mine were
kept). `Top/TileAgree.lean` (B1): `tile_agree`, the loader's setup block word of the picked
tile (`r28Ref`) is the MMA warp's (`Mma.blocks` of `Mma.refV`) on lanes of one CTA: the two
compute one minimum of one pair of ceilings; the row terms differ in how the code forms the floor
quotient (`row_agree`) and the sums only in their order (`sum_agree`), both proved on 32-bit words
through their values modulo `2 ^ 32`. `Top/MmaLagLd.lean` (E1, K/V polls): `kv_lag` is the body
of `MmaLagFrom true` at the K/V polls. Pieces: `elect_le` (a lane of a warp has made no more
elections than another lane at the end of that lane's trace, by `ElectOrd.partner` and
`elect_ordinal`, the ex-Inkling agent's `Top/MmaAgree.lean`, which replaces the agreement
hypothesis); `rel_le_acq` (a place table over the 101 places against the four K/V poll places:
with no more elections, no more ring releases than the other lane's acquisitions); `com_le_lane`,
`kv_bound_lane` (the full phase is at most any warp-12 lane's polls plus one); `kv_poll`,
`idx_lt`, `pkts_ge` (the poll's ring index is below `2 · max(Bs, 1)`, at most the tile's packets);
`ld_end` (an exited loader lane made `ringCnt A j` arrive-ons, `A = pkts r28Ref` with a tile,
`A = 0` and no tile otherwise); `arr_recorded` (with no open arrive-on, a lane's arrive-ons are
fault-free records of the object); `ld_time` (a loader lane's time is at most `scanBase + 1`,
below every pipeline time). At a blocked poll: an open arrive-on blocks; else
`NoIncObject.blocked` gives a short loader lane, pending (a blocker) or exited (excluded by the
tile). `kv_lag` takes the safety premises' data fields (`dataSrc`, `numAll`, `dataStore`, `smSrc`)
and fault-free object records (`¬ TmaUnsafe`, the `noTma` field): progress is proved given safety
(`ProgressPremise` is `SafeGoal → ProgressGoal`), so both are available where the descent uses it.

`ProgressPremise` does not shrink yet: it is still the opaque `SafeGoal → ProgressGoal`, and no
theorem builds `ProgressGoal` from `MmaFullLag`, `ReadyLag` and the waits (the descent assembly);
until it exists, a proved part of `MmaFullLag` cannot be removed from `correct2`. The Q polls
(offsets 0, 8, one poll each before the loop) remain: phase 0 needs the elected warp-14 lane's
expect-tx arrival or its copies' bytes (a `.tensor` obligation or the byte balance), and offset 8
has a second arrival from the drain whose exclusion needs the loader's drain wait on offset 24.

**Lane T1 round 40 (2026-11-22): the progress assembly.** `Top/Assembly.lean`: `Top.progress`,
`ProgressGoal` by `Descent.progress_of_steps` with `Sched.rank (timed p L)`, given safety, the
safety premises (`SafePremises`: the data fields for the role table's following and `kv_lag`,
`noTma` for fault-free records) and `ProgressRest`. `correct2` now takes `ProgressRest` in place of
the opaque `ProgressPremise` (deleted). Every open obligation splits (`obl_steps`): a pending thread
that is blocked (`blocked`); released with a stopped machine (`Descent.dead_steps_inOrder`, with
`wfStep_all`, the assumptions' well-formedness for in-order extensions from `Assumptions.wfStep`);
at `some none` (excluded by `goodR`); at a state, by role: warp 12 at a poll through
`Progress.mma_mbarAt` and `Sched.mbar_at_steps` with `MmaFullLag` from `mmaLagLoader` (the K/V
polls by `kv_lag`, the Q polls the field `mmaQ`) and `mmaSoft`; warp 13 at a ready poll through
`Progress.ready_mbarAt` with `readyArrive`; a stub state excluded by its JR; every other role state
a field (`loader`, `softmax`, `correction`, `mma`, `epilogue`, `start`). The asynchronous
obligations are the field `async`. The fields are stated with `RelSteps` (a released pending lane
whose end state satisfies the role's predicate steps), so each class proved removes its field.

**Lane T1 round 41 plan (2026-11-22): the field `mmaQ`.** A lane of warp 12 at a Q poll (place 1,
offset 0; place 9, offset 8; round 0, no earlier poll, so blocked means an even phase) with
`qObj` (count 1, expect-tx arrival by a loader lane, completions by tensor copies). Pieces:
(1) a pending loader lane blocks (time at most `scanBase + 1`, as in `kv_lag`); (2) every loader
lane exited: the winner of the warp's election at `tePc t 0` exists (an exited lane of warp 14
made that election; its leader lane won it, `elect_winner`), and the winner's exit counts give its
expect-tx arrival (`RefCounts`: arrivals plus the pending one equal the won elections at
`tmaArrPts o`) and its two copies (`n .copy`); (3) with tx zero, `TmaUnitObject.blocked` bounds
the arrival units by the phase, contradicting the recorded arrival; with tx nonzero, a copy is
not notified (an open `.tensor` obligation) or the bytes disagree, excluded by the byte facts:
the arrival's tx word is 32768 (the site value) and each copy's descriptor is `p.qMap`, a box of
64 x 128 `bf16`, 16384 bytes (`Spec.maps`); (4) offset 8 also receives the drain's arrival
(`da`, pc 1896): it follows the loader's successful drain poll of offset 24 (Q empty), whose
phase is at most the electing MMA lane's commits to 24 (place 63), none while a lane of warp 12
is at place 9 (`elect_le`), so phase at most 1 there.

**Lane T1 round 41 (2026-11-22): the field `mmaQ` removed.** `Top/MmaLagQ.lean`: `q_lag` proves
`MmaLagFrom true` at the Q polls without the byte facts the plan above expected. A lane of warp
12 at a Q poll (place 1 or 9, round 0, at most two elections) bounds every warp-12 lane to no ring
release (`rel_zero`, a place table; `com_rel`, the electing lane's commits to an empty barrier are
at most `ringCount (ringRel …)` at a place with no more elections), so empty slot 0's phase is 0
(`empty_phase`); an exited loader lane polled empty slot 0 successfully `ringCnt (A + 3) 0 ≥ 2`
times (`ld_end` now also gives the empty-slot poll counts at the exit) for a tile of `A ≥ 2`
packets (`pkts_ge`), which needs phase 1 (`ld_empty_okPolls`). So the first loader lane is pending,
and it is earlier than the waiting lane: a blocker whatever the Q barrier's phase. `ProgressRest`
has nine fields.

**Lane T1 round 41: what E3 (the loader's waits) needs first.** The loader role's time is still
the placeholder `scanBase` (`Progress.roleTime`), below every pipeline time. A loader lane at its
empty-slot poll for packet `k` waits for the MMA warp's release of packet `k - 3` (or its commit
obligation), and a lane of warp 12 is never earlier than `scanBase`, so no wait of the loader can
step until the loader has pipeline times: packet `k` of block `b` at slot `b`, offset 0 (K) or 1
(V), the drain after the tail. The inequalities to keep: the MMA warp's release of packet `k - 3`
(places 16, 43, 49, 81) is earlier than the loader's wait for packet `k`, and a loader lane short of
packet `i` is earlier than the MMA warp's poll for ring index `i` (`kv_lag`, `q_lag` use
`ld_time`; with pipeline times they use the packet's slot instead). The split of the field `loader`
into the waits (T1) and the other events (lane L, E5a) goes with that change.

**Lane T1 round 42 (2026-11-22): the loader's time table, designed (Time.lean is now T1's).**
Times of the MMA warp (`Mm.pipeT q r = clk (slot) (2 q)`): its poll of ring index `i` is at
`P(0) = clk 0 4`, `P(2r+1) = clk (r+1) 40` (loop) or `clk (r+1) 128` (tail), `P(2r+2) = clk (r+1)
58`; its release of index `j` at `R(0) = clk 0 32`, `R(2r+1) = clk (r+1) 86` or `clk (r+1) 162`
(tail), `R(2r+2) = clk (r+1) 98`; its Q polls at `clk 0 2` and `clk 0 18`. The loader's packet `k`
(its next packet: the sum of its arrive-on counts) at `T(k) = clk (k / 2) (k % 2)` satisfies both
inequalities the descent uses: `R(k - 3) < T(k)` (the empty-slot wait's blocker is earlier) and
`T(k) < P(i)` for `k ≤ i` (a short loader lane is earlier than the MMA warp's poll; `kv_lag`
keeps its shape with `T(k)` in place of `ld_time`). The scans keep `passTime` (first pass at
`scanBase`, second at `endBase`), the drain goes to the tail (`tailBase` plus its site, after
every release `R`).

The Q polls do not survive the change as proved: an empty-slot wait for packet 3 must be later
than `R(0) = clk 0 32`, which is later than the Q polls, and a loader lane can be waiting there
while a lane of warp 12 is at its Q poll only if warp 14 already passed its TMA groups 0 to 3. So
`q_lag` then needs what round 41's plan listed: the TMA group's winner and its two copies, an open
`.tensor` obligation, or the byte balance (the expect-tx word 32768 against two `p.qMap` boxes of
16384 bytes); the TMA groups 0 to 3 get times below `clk 0 2`. Until that proof exists the time
table keeps the placeholder (the change would put `mmaQ` back as a field), and E3 (the loader's
waits, the empty-slot wait through an MMA-side counterpart of `kv_lag`: the loader's poll count
of empty slot `j` against the electing lane's commits, the commit obligation or an earlier MMA
lane as the blocker) is written against the designed table. The `loader` field's split into waits
(T1) and other events (lane L, E5a) is recorded in `machine-plan-status.md`.

**Lane T1 round 43 plan (2026-11-22): `q_lag` by the byte balance (coordinator: before the time
switch; `mmaQ` must not return).** Facts measured on the loader's tables: the TMA groups' arrival
sites `ta t` arrive at `(2535, 0)` for `t = 0` (Q stage 0) and `(2535, 8)` for `t = 2` (Q stage
1), the drain's `da` at `(2535, 8)`, each with the transaction word of register 1892, 1910 or 2307;
the drain's word is `i32 32768` (`Loader/Machine.lean`, the drain's values); the copies `tc t c`
complete on `tcBar t`, the same barrier as `ta t`. The pieces:
1. Event shapes on a Q barrier: every thread arrival is a loader lane's `ta 0`, `ta 2` or `da`
   with transaction bytes `32768` (the site values, by `rfl` on the value table), every tensor
   issue a `tc 0 c` or `tc 2 c` whose descriptor is `p.qMap` (`Spec.maps`, map 9), so
   `TensorTransfer.bytes = 16384`; `32768 = 2 * 16384` by `rfl` on the stated box `![64, 128, 1]`
   of `bf16`.
2. Counts: at most one TMA-group arrival per Q barrier (the ledger: a lane's arrivals at offset `o`
   are its won elections at `tmaArrPts o`; one winner per election instance, `elect_winner`), at
   most two copies; on stage 1 at most one drain arrival, after the loader's drain wait on offset
   24, which needs the electing MMA lane's commit at place 63 (none while a lane of warp 12 is at
   place 9, `com_rel`-style with a place table); so one arrival.
3. Existence: a lane of warp 14 at a state past TMA group 0 (resp. 2) means the group's winner
   exists (an election event of the group, `ElectOrd.partner`); the winner past its `ta t` and
   both `tc t c` has made the arrival and issued both copies (path facts of the loader machine:
   after a won `te t e` the next site is `ta t` or `tc t (e - 1)`).
4. The blocked poll: a lane of warp 14 pending before the group's end (times below `clk 0 2` in the
   new table) blocks; else an un-notified copy is an open `.tensor` obligation; else the history
   holds one arrival of 32768 bytes and two completions of 16384, and `MbarRing.Blocker.tx_short`
   with `n = 2`, `B = 16384` gives phase 1, an odd phase: the poll is not blocked.
Piece 3's path facts and piece 2's drain exclusion are the long parts; nothing in Core, the
assumptions or the statements changes.

**Lane T1 round 44 (2026-11-22): C1, the shared-memory write map, measured.** From the write
frame's per-role lemmas (`Top/WFrame*.lean`) and the decoded TMA sites (`Loader.inputSite`), the
writers of shared memory and their byte ranges (offsets from `sb = L.sharedBase`):

| Writer | Event | Range |
|---|---|---|
| MMA warp, lane 0 | allocation address store | below `sb + 316` (`wr_low`) |
| softmax warps | statistics stores (`stat`, `fin`) | `[sb + 368, sb + 2424]` (`stat_wr`) |
| correction warps | final O stores (`fst`) | `[sb + 2848, sb + 134252]` (`fst_wr`) |
| loader, warp 14 | Q stage 0 (TMA, sites 0, 1) | `sb + 3072`, `sb + 19456`, two boxes of 16384 bytes |
| loader, warp 14 | Q stage 1 (sites 4, 5) | `sb + 35840`, `sb + 52224` |
| loader, warps 14, 15 | K/V packets (`cp.async`) | `[sb + 68496, sb + 232544]` (`cp_lo`; the slots' rows) |
| loader, warp 14 | Bias stages (sites 2, 3, 6, 7, 8 to 11) | `sb + 166912`, `183296`, `199680`, `216064` |

The correction warps' final O staging overlaps the Q stages and the K/V slots: the kernel reuses
those buffers for the output once the pipeline is over. So the region frame C1 asks for is not a
partition by writer: `noRace` and `noMixed` on these bytes need a cross-role order, the
correction's final stores after the MMA warp's last reads of Q and K/V (its tail commits, the
correction's O-full poll) and after the loader's last writes there (their completions, observed
by the MMA warp's full polls before its last commit). The ranges of the K/V slots (32768 bytes
each from `sb + 68496`? `cp_lo`'s bound is the union) and of the Bias stages need exact per-slot
bounds before the frame can be stated per region; the K/V upper bound `sb + 232544` also covers
the Bias stages, so the loader's two writers there need their own separation (Bias from 166912,
the K/V rows below it per `cp_lo`'s inner bound `sb + 169056`, which is the next thing to tighten:
the packet rows end at `sb + 68496 + 3 · 32768 = sb + 166800`). C1's next step: per-writer exact
intervals (`cp_lo` per slot, the TMA sites per stage), then the frame theorem "every shared write
is one of these classes, at these bytes", then the order facts for the two reused areas.

**Lane T1 round 45 (2026-11-22): C1 steps 1 and 2.** `Top/KvSlot.lean`: `cp_slot`, a row copy of
packet `k` writes inside ring slot `k mod 3`, `[sb + 68608 + 32768 (k mod 3), +32768)`: the row
bases are 16-byte-aligned words in the first 1008 bytes (`blk_rowBase`, `blk_rowsAt`,
`blk_r1008`), the swizzle keeps a word in its 128-byte line at most 112 bytes in (`swz_line`, on
the values modulo `2 ^ 32` and `Nat.xor_div_two_pow`), and the offsets `2048 (i / 2) + 16384 c`
fill the slot (`slot_addr`). So the K/V ring is `[sb + 68608, sb + 166912)`, between the Q stages
(ending at `sb + 68608`) and the Bias stages (from `sb + 166912`). `Top/ShFrame.lean`: the class
table `ShWr` (allocation store, statistics stores, final O stores, row copies with their slot) and
`wr_class` (every thread write or linear copy to shared memory is of one class), and `tload_box`
(a tensor load writes inside the 16384 bytes at its decoded site's offset). Step 3 (the two
cross-role orders for the reused areas: the correction's final O stores against the loader's Q
and K/V writes and the MMA warp's reads there) is next; per (region, writer pair) one lemma.

**Lane T1 round 46 plan (2026-11-22): the K/V slot orders (D12/D13, region K/V).** Template:
Inkling's `Safety/Regions.lean` with the library's `SingleTmaRing.copy_read_order` (RAW
`copy_before_read`, WAR `read_before_copy`, `Lemmas/Protocol/SingleTmaRing/Order.lean`). The
library ring is for tensor copies; tml-fa4's K/V packets are `cp.async` copies completed by
no-increment arrive-ons, so the region needs its two lemmas in that form, one per writer pair:
(1) row copy before MMA read (RAW): the copy of packet `k` is tracked by the lane's arrive-on of
packet `k` (`TracksCpAsync`), the MMA lane's successful full poll of use `k / 3` observes it
(`NoIncObject.observes_copy`, with the K/V bound `kv_bound_lane` fixing the phase the poll
observes), then program order from the poll to the MMA issue (`po_of_source_not_access`) gives
`AsyncBefore` at every byte both cover (`cp_slot` places both in slot `k mod 3`); (2) MMA read
before the next row copy of the slot (WAR): the read completes before the electing lane's commit
of the use (`TracksMma`), the commit's arrival on the empty slot is observed by the loader lane's
empty poll of use `k / 3 + 1` (`commitObj` phase facts, `ld_empty_okPolls`), then program order
to the copy; SingleTmaRing's `read_before_copy` is that chain with a tensor copy at its end and
transfers once its copy event is generalized. Then the pair (row copy, row copy) of two packets
of one slot goes through (2) and (1). The Q and Bias stages fit `SingleTmaRing` as tensor copies
directly (Q: one use per tile; Bias: the warm rounds' ring of two).

**Lane T1 round 47 (2026-11-22): the Q ring's pieces.** `Top/QRing.lean`: `won_unique` (two lanes
of a warp that each won a full-mask election are one thread) and `ld_arr_won` (a loader lane that
arrives on a Q stage won an election before: the arrival's site is `ta t` or the drain's `da`,
whose count conjunct equals the lane's won elections at `tmaArrPts o`). `Top/QEmptyObj.lean`:
`qemptyObj`, the Q stages' empty barriers (16, 24) are commit objects (`qempty_use`, as
`empty_use`). With `qObj` (offsets 0, 8) the four Q barriers are classified. What the
`SingleTmaRing.Hyp` instantiation for a Q stage still needs, field by field: the arrival bound
(`arrivals full + 1 ≤ okPolls empty` at the arrival: the TMA group's wait on 16/24 before its
arrival, and on stage 1 the drain's wait on 24 before `da`); `full_parity` (the MMA lanes' Q
polls, `Progress.par_eq`); `empty_parity` (the loader's `tw 0`, `tw 2` and `dq` waits, as
`ld_empty_par`, `δ = 0`); `spins`; `full_acq`, `empty_acq` (the waits' `acq` and scope from the
shape tables); `issue` (the copies `tc t c` by the arrival lane, two per use, after the group's
wait); `cta`. One question to settle first: whether the drain's `da` on stage 1 is warp 14's only
(its arrival thread must be the ring's single `ap`).

**Lane T1 round 47, continued: the drain's arriving warp, and the Q ring's missing count.** The
loader's machine (`Loader/Machine.lean`, the step after `dw 2`: `D.ite (not14 w) exit dq`) sends
warp 15 to its exit after the drain's slot waits; only warp 14 runs `dq`, `de`, `da`. So the
drain's arrival on Q stage 1 is warp 14's winner of the election at `de`, the same thread as the
winner of TMA group 2 (`won_unique`), and stage 1 fits `SingleTmaRing` with one arrival thread:
its second arrival is the ring's use 1, after the drain's successful wait on 24 (use 1 of the
empty barrier). The obstacle to `Hyp` for both stages: `FullSource.arrive` and `Hyp.issue` bound
the arrival and the copies by the arriving lane's successful polls of the empty barrier (16 or
24), and the loader's reference invariant counts successful polls only of the K/V empty barriers
(`RefCounts` conjunct 1, offsets 56 to 72). The ledger counts every barrier (`Loader.cls
(.acquire l)`), so the fix is a `RefCounts` conjunct for offsets 16 and 24 (closed form: one per
passed `tw 0` / `tw 2`, plus the drain's `dq`), proved through the loader's step files (lane T2's
`Loader/Steps*`, where every site's count transition is already checked for the other
offsets).
Old-tree reuse, measured by import closure (a scan of the `import` lines): Proof2 without `Top/` reaches 145 files (30.3k lines) of `Proof/` (2,033 files, 366.9k
lines); with `Top/Safety.lean`, which reuses every non-completion unsafe case of the old assembly,
1,449 files (283.3k lines). So deleting `Proof/` at the switch needs either these 1,449 files
moved under the new tree as they are (the switch then deletes 584 files, 83.6k lines: the visit
induction, the completion transports and the progress walks), or the remaining safety cases
(memory conflicts, Tensor Memory access and lifetime, named barriers, TMA, metadata reads)
restated on the roles' shape tables and reference invariants, as plan §4 step 5 intends. The
second is the size reduction; it is not started.

Axioms of `Top.correct2`, `Progress.warp0Lag`, `Progress.corr_coll`: `propext`,
`Classical.choice`, `Quot.sound`. Sizes: `Proof2/Top` 239 lines (`Safety.lean` 188, `Correct.lean`
51).

### Safety by class (lane T1, round 9, 2026-11-21)

- Base: d173a2acb with lane L round 8 (`lane-L` at 2b5d67625) merged. Lane L's
  `Lemmas/Flow/Step/ShapeAsync.lean` replaces `Proof2/Lib/ShapeAsync.lean` (deleted; the loader's
  `Shape.lean` imports the library); `Common/Frame.lean`'s `good_state`, `isShfl_not_vote`,
  `countColl`, `lane_facts`, `upTo_of_lt` and `Common/Coll.lean`'s `shfl_src`, `vote_src` are now
  one-line instances of `Lemmas/Kernel/Source/WarpColl.lean` (statements unchanged; `Coll.lean`
  155 → 86 lines, `Frame.lean` 503 → 479). `Common/Roles.lean` keeps its `Role` inductive (lane L's
  `Code.roleThread` would rename the role states every upper-layer file matches on).
- Softmax glue (coordinator note, softmax head 536005e24): not glued this round. `frag_steps`
  needs `Softmax.stepAt` at every state; with the 63 numeric sites as a named premise,
  `thread_sound` and every theorem above it (`good_migrated`, the progress files, `correct2`)
  would take that premise, and no safety field gains from it until the softmax warps are
  followed (`ref_next`). Decision: glue when `stepAt` covers every site.
- **`Top/Safety.lean` is split by the classes of Core's `Unsafe`.** `SafePremises` has one field
  per class the Proof2 tree does not prove yet, stated for every consistent execution exactly as
  Core states it (`¬ HasUb X`, `¬ Race l X`, …, `¬ MbarUninit l X`; the assumption class as its
  condition, no input write). `Top.safe` is a case split over `Unsafe` (no old safety case). The
  classes proved in `Top` from the decoded program: `ClcUnsafe`, `ClusterFault`, `MatrixUnsafe`,
  `TcCommitUnsafe`, `PollShapeUnsafe`, the uniform CTA group, the assumption list, and
  `TensorStoreUnsafe` (`Top.noTensorStore`: every tensor store of the code is a plain tile write,
  every ordinary copy a whole vector). Their files (`Proof/StaticSafety.lean`,
  `Proof/PollSafety.lean`, `Proof/Thread/TensorForms.lean`, 3 files, 495 lines) are static code
  checks that move with the switch by `git mv`; moving them now would edit the import lines of 56
  old files and rebuild the old tree.
- **First class on the role table: `TensorUnsafe`** (`Common/Kinds.lean`, `Top.noTensor`). Every
  event of a lane of warps 8 to 13 that is no undefined behaviour is fired from a followed state
  (`good_migrated`) at that state's pc by the instruction there (`migrated_fires`); a state holding
  `RefAll` sits at a site of the startup, output, MMA or correction fragment (`pc_mem`, from the
  roles' `site_mem`; `Epilogue.site_mem` is new), and `migrated_noTensorOp` checks by evaluation
  that no instruction at those 541 pcs is a tensor load. So no lane of warps 8 to 13 issues one
  (`migrated_noTensor`), and the field is narrowed to `noTensorRest`: the fill values of the
  loader and softmax warps' tensor loads. `TensorAllocationUnsafe` the same way
  (`Top.noTensorAllocation`): the store case by the output warp's `store_issue` and the launch's O
  map, the prefetch case by the static check, the load case narrowed to `noTensorAllocationRest`.
  `good_migrated` needs `CorrWarp.DataSrc`, so
  `SafePremises` gains the field `dataSrc` (the softmax warps' statistics and `TcLdDataflow`; the
  same premise `good_migrated` already had), and `Bridge.OldPremises` gains it too, since the old
  tree does not state it. The pattern applies to every class that names an instruction kind
  (`SetMaxNReg` requests outside the start sites,
  CTA-barrier and mbarrier operands by site): `migrated_fires` plus one evaluated check over
  `migratedSites`. Library candidate for lane L: `migrated_fires` for any role table (a family of
  site lists, one `site_mem` per fragment, and the reference invariant that excludes stubs).
- `Bridge/OldSafety.lean` is the previous `Top/Safety.lean` (the old assembly with the
  completion facts as `OldPremises`) plus `Bridge.ofOld : Pre → OldPremises → SafePremises`, each
  field by injecting the class into `Unsafe`. So `correct2` with `ofOld` has the premises it had
  before the split, and `Top` no longer imports an old safety case.
- Measured by import closure (`.lake/own/t1/reach2.py`, the old tree is 2,033 files, 366.9k
  lines): Proof2 without `Top` and `Bridge` reaches 145 old files (30.3k lines). Before: `Top`
  reached 1,449 (283.3k). After: `Top/Safety.lean` adds 3 files (0.5k), `Top/Correct.lean` (with
  `Proof/Result/Post.lean` and `Proof/Termination.lean`, which are the result and bound goals, not
  safety) 190 more (43.5k), so Proof2 without the bridge reaches 338 old files (74.3k); `Bridge/OldSafety.lean` alone reaches 1,300 (252.6k). The bridge's
  closure is the old work still standing in for open fields; it is deleted when its last field is
  migrated.
- **Each field, the old proof that stands in for it (its file's closure beyond the Proof2 base),
  and its discharge on the role table.** "Roles" means: the startup (every warp), the output warp
  (13), the MMA warp (12), the correction warps (8–11) from `good_migrated`, and the loader
  (14, 15) and softmax warps (0–7) as per-warp premises until they are followed.

  | Field | Old proof (closure) | Discharge on the new tree |
  |---|---|---|
  | `noUb` | completion premise `noFault`, `DecodedFaults` (75 files, 18.8k) | per role, `ref_safe` (the shape table's `ub` alternatives excluded under `Ref`: aligned load and store addresses, Tensor Memory operands, MMA descriptors) and no death before the exit (`ref_next`'s death clause, open for the correction and loader fragments); generic lemma: an event of a followed thread whose every state is ub-free and never dead is no `ub` |
  | `noInputWrite` | `OutputProtection` (134, 33.4k) | write frame: every write is to shared memory, Tensor Memory, the output or LSE region (shape tables of every role) |
  | `noUnalloc` | `Allocation`, `Metadata`, `GlobalConflicts` (470–689, up to 146.3k) | the roles' read and write addresses from `Ref` against the launch's allocation (`Pre`) |
  | `noRace`, `noMixed` | `MemoryOwnership`, `OutputWriteAgreement` (1,004, 202.2k) | write frame plus T3 hand-offs (each shared region's writer and readers ordered by its barrier family) |
  | `noBarMismatch`, `noCtaBar` | `NamedBarrierConflicts`, `Protocol/NamedBarriers` (263–290, up to 71.9k) | the named-barrier declaration (plan G7) over the roles' `bar` sites and counts |
  | `noTma`, `noMbarUninit` | `Safety/Mbar` (576, 135.7k), `MbarSafety` (59, 15.5k) | the roles' mbarrier operands from the shape tables are the startup's initialized objects (`Start0`), published by the startup barrier; object lifetime by the ring declarations |
  | `noTmemSource`, `noTmemInstruction` | `TmemRescaleStoreValues`, `MmaOperandCoverage`, `RepeatedProbabilityHistory`, `RescalePublicationValues` (up to 1,176, 231.4k) | Tensor Memory hand-offs (T3) and the softmax values (P in BF16, rescale factors in FP32: softmax premises until its numeric sites) |
  | `noAligned`, `noWarpDivergence` | `Alignment`, `CorrectionTensorSchedule`, `MmaAlignedTensor`, completion premises `noAlignedWork`, `softmaxTensor`, `noWarpDivergence` (up to 281, 68.7k) | the collective source on two lanes of a followed warp (`Common/Coll.lean`), with `pollAgree` at the poll branches |
  | `noSharedLifetime` | `Safety/SharedLifetime` (569, 132.3k) | every role's last shared access before its exit (exit sites from the shape tables) |
  | `noTensorRest`, `noTensorAllocationRest` (the loader and softmax warps' tensor loads only) | `TensorSafety` (44, 9.9k) | the loader's TMA groups read the Q and Bias maps (loader shape table, premise until followed). Done: warps 8 to 13 issue no tensor load (`migrated_noTensor`), every tensor store is the output warp's through the O map (`Epilogue.store_issue`, base), no tensor prefetch (`Top.noTensorAllocation`) |
  | `noTmemResource`, `noTmemRelease`, `noTmemAccess`, `noTmemWrites`, `noTmemReads` | `MmaResourceOrder`, `TmemAccess`, `TmemOutputRescaleConflicts`, `TmemReadConflicts` (243–562, up to 131.8k) | the MMA warp's allocation and release (`Mma.Startup`, `Mma.Ref`) and the Tensor Memory hand-offs (T3) |
  | `noRegister` | `RegisterSafety` (18, 4.0k) | each role's single request at its start site (shape tables, with the request's direction and count added to the `setmax`/`start` entries), per warpgroup |

- The old proofs overlap: 1,265 of the bridge's 1,300 files are reached from
  `Proof/Safety/Assembly.lean` alone, so the bridge's closure shrinks only as whole groups of
  fields migrate (the Tensor Memory group and the memory-conflict group are the two largest).
- Not done this round, in order: (1) `noUb` for the migrated roles (`ref_safe` and the death
  clause per role; the library's `shape_ld` loses the misalignment condition, so an aligned
  variant is a library candidate); (2) the loader warps' following (the loader's `ref_next`
  landed at 77cd63c93; following needs the scan's values on the output warp's `Sim`, the
  page-table words by `inputReadValue`, the pointer loops' local words by
  `Frame.local_read_of_last_store` with `localWriteOwner`); (3) the write frame and T3 hand-offs,
  which unlock the race, Tensor Memory and lifetime groups.

### Lane T1 round 10: the loader warps' reference values (2026-11-21)

- Merged: the loader lane (`tmlfa4-loader-proof2` at 39505f2b3: `ref_next`, local-store counts;
  then b2356fffa: split step files) and lane L (`lane-L` at 731ce134d: `LocalOwned` derived from
  consistency, `shape_mbInitAny` promoted; `Proof2/Lib/ShapeInit.lean` deleted, the startup's
  shape table imports `Lemmas.Flow.Step.ShapeClasses`). Full strict build after the merges passes.
- **Why following the loader warps needs more than `Loader.Ref`.** `Loader.Expect` asks only for
  the kind of a returned value, so the sources a loader lane needs are kinds: the launch words,
  the local words (lane L's local source), and the shuffles. A shuffle receives the source lane's
  operand at the same instance, or anything when the source lane has exited before it (Core
  `ShflOk`, `ShflExited`). Excluding that case (the `hE` premise of `shfl_src`), and a source lane
  at a ballot (`hV`), is a fact about two lanes: their shuffle counts at the second pass's ballot
  and at the exit must agree. The count there is the first pass's plus 32 per packet, so every
  lane of a warp must load the same number of packets. `Loader.Ref` keeps the packet count `A`
  existential (fixed when the rounds end) and states no round arithmetic, so it does not give
  that. Decision: the agreement is stated on lane T1's side, as the MMA warp's `MFits` does for
  its pipeline, in `Proof2/LdWarp/` (no edit of the loader lane's files).
- `LdWarp/Sim.lean`: at every scheduler site but the two tile choices the loader steps as the
  output warp on its scan state (`succ_scan`); `ofE` reads an output-warp state back, with the
  loader's drain values at a pass's end (`vOf`).
- `LdWarp/Frame.lean`: the tile's blocks (`bc`: first block, warm round, steady round, warp 14's
  last Bias group), the block's commits before a site (`inBlk`) and the packet's shuffles
  (`pktSh`); `blk_step`: a step inside a block keeps the scan state, the setup and the round
  counter, and moves `inBlk` by its commit and `pktSh` by its shuffle (by unfolding `succ` per
  site family, 9 s).
- `LdWarp/Round.lean`: the packets of a tile as a function of its block word `b = %r28` alone,
  `pkts b = 2 + 2 w0 b + 2 (sv (b - 1) - wRn b)` (signed 32-bit values; `wRn b = min (max (b-1)
  0) 9` warm rounds, none when `b < 2`), with no bound on `b`; `Rounds` (the round counter and the
  commits so far per block class) and its transitions at the block ends (`after_prime`,
  `warm_end`, `steady_end`, `after_warm`, `after_tail`): the next block's `Rounds`, or the second
  pass with `nc = pkts b`.
- `LdWarp/Fits.lean`: `LFits p L g d ns nv nc`, the reference values at a loader state with the
  thread's shuffles, ballots and commits: the output warp's `Epilogue.Fits` on `toE d` at the
  count shifted by `32 nc + pktSh` (by `32 nc` in the second pass and the drain), the picked
  tile's block word (`SuRef`, `r28Ref`, a function of the picked tile and the CTA), `Rounds` in
  the blocks and `nc = pkts` in the second pass. `lfits_next`: every step on an event that
  returns what `LExpect` says (the output warp's reference at the scheduler sites, the launch's
  used-K length at its read) keeps `LFits`. So the second pass's positions are the same on every
  lane of a CTA, which is what the loader's position facts need.
- Lean notes: (1) give `omega` hypotheses whose atoms are syntactically the goal's (`show` the
  clean form first); otherwise the elaborator accepts it up to defeq and the kernel spends minutes
  or overflows (`deep recursion`) re-checking; (2) `decide_eq_true h` as the argument of a lemma
  whose condition is a metavariable picks a default `Decidable` instance; state the condition
  first (`have hc' : scmp … = true := by rw […]; exact decide_eq_true h`).
- Sizes: `Proof2/LdWarp` 1,345 lines; check times 2 to 6 s per file.
- Closure of `Bridge/OldSafety.lean` beyond the Proof2 base (`reach2.py`): 1,300 old files,
  252.6k lines, unchanged this round (no safety class moved).
- Remaining (lane T1), in order:
  1. Following warps 14 and 15: (a) the thread ledger gains the loader's classes (`Cls.load`,
     with `deriving instance DecidableEq for Loader.Cnt`; `start_kind` and `Start0Cls` gain the
     loader's election class); (b) `LdWarp/Warp.lean`: `Ref` (startup, then `Loader.Ref` and
     `LFits` with the loader counts), `start_step` through `start_step_of`, `role_step` from
     `Loader.ref_next` and `lfits_next`; (c) position facts as the MMA warp's (`Mma.eband` applies
     to `Epilogue.Fits` unchanged; the packet phase is between the first pass's choice and the
     second pass by `32 nc + pktSh < 32 pkts`); (d) sources: the scheduler's words as the
     correction warps' (`Epilogue.expect_word`, `expect_q`, collectives by `Common/Coll.lean`),
     the used-K word by `inputReadValue`, the page-table words' kind by `inputReadValue` with
     `Pre.pageBytes` (the row is below the used length at a `pgLd`), the local words' kind by
     `Frame.local_read_of_last_store` with lane L's `LocalOwned` and `Loader/Local.lean`, the
     packets' shuffles' kind from the source lane's operand (every loader shuffle sends a word);
     (e) `good_migrated` for warps 8 to 15 and `migratedSites` with `loaderSites`.
  2. `noUb` for the migrated roles (unchanged from round 9: per role the ub alternatives of the
     shape table excluded under `Ref`, and the death clause; the aligned `shape_ld` variant).
  3. Write frame and T3 hand-offs; then the race, Tensor Memory and lifetime groups.
  4. Softmax glue when its steps cover every site.
- Process note: one scratch `lean` process of this lane was stopped with `pkill -f` on its own
  file pattern, against the lane rule (kill by explicit PID only); no other process matched.

### Lane T1 round 11: the loader warps followed (2026-11-21)

- Merged `origin/main` (ee2e83055) into the lane T1 branch: the library from main; the loader files
  and this file from the branch (main carried an older loader `Ref` without the local-store
  class). Full strict build passed after the merge.
- **Thread ledger.** `Cls.load (c : Loader.Cnt)` counts the loader's classes on every thread
  (`deriving instance DecidableEq for Loader.Cnt`). The fence-path startup fires none of them
  (`start_kind`); warp 0's startup elections are in the class `won pc`, so `Start0Cls` gains
  `∃ pc, c = .load (.won pc)`.
- **`LdWarp/Pos.lean` (positions).** `lband`: a scheduler, request or drain state of the first
  pass stands before the CTA's choice with no packet committed; one of the second pass after the
  choice and all `pkts` packets of the picked tile (`r28Ref_cta`: the same on every lane of the
  CTA). `bband`: a block state stands at the choice plus `32 nc + pktSh`, and a row shuffle before
  `32 pkts` (`nc_lt_pkts`, from `Rounds`). From them, by `shift` and the output warp's position
  facts on the shifted counts: `lshfl_lt_vote`, `lshfl_lt_exit`, `lvote_exit`, `lshfl_same`,
  `lvote_same`, the three facts `Common/Coll.lean` asks for.
- **`LdWarp/Warp.lean`.** `Ref` (startup: `StartAt` and zero loader counts; role: the fragment
  index's warp is `w`, and unless an event so far was undefined behaviour, `Loader.Ref` on the
  loader classes and `LFits` with the thread's shuffles, ballots and commits), `start_step`
  (`start_step_of`, the gate enters `.loader (x3 == 15)`), `role_step` (`Loader.ref_next` with the
  fragment's invariant from `Frame.fired_site`, and `lfits_next`), the collective sources
  (`sent_word`: every loader shuffle sends a word; `lshfl_src`, `lvote_bits`), `ev_q` (the request
  reads address the output warp's words) and `expect_uk`.
- **`LdWarp/Mem.lean` (local words).** Every loader store writes the bytes of a 32-bit word at a
  page round's offset or of a 64-bit address at a pointer round's offset (`wr_ev`); the startup
  writes nothing. At a local load the count `lst o` of the loaded offset is positive
  (`Loader/Local.lean`), so an earlier store covers the loaded bytes; by `Frame.local_read_src`
  (`Proof2/Lib/LocalSrc.lean`, library candidate: the initial memory is excluded by `Hidden`, other
  threads by `localOwned`, later stores by `NoFuture`) each byte is a byte of an earlier store of
  the lane, and four such bytes rebuild to a 32-bit word or not at all (`rebuild_word4`). This
  needs no "last store" argument: every earlier store has the property.
- **`LdWarp/Src.lean`.** `lexpect` (the references' expectations and the return kinds at every
  loader site), `step`, `good`: every lane of warp 14 or 15 is followed with `Ref`, given
  `PgSrc`. `Common/Migrated.lean`: `RefAll` has the loader branch, `good_all` covers warps 8 to 15
  (premises `CorrWarp.DataSrc` and `LdWarp.PgSrc`); `good_migrated` (8 to 13) is unchanged, so
  the classes proved from it (`Top.noTensor`, which checks that no migrated site is a tensor load,
  false for the loader's TMA groups) keep their premises. `Kinds.pc_mem` takes the warp bound.
- **Open: `PgSrc`** (a page-table load returns a word). Its source is the launch's page table
  (read-only input, `inputReadValue` with `Pre.pageBytes`) at `pageTableBase + 4 (i stride + row
  / 16)`; that address is in the table only when the round's row is in `[0, kLength i)`. The
  machine reaches `pgLd` only when `rowCond` is false (`row < ukw`, signed in the first block),
  but `LFits` does not keep that branch, the request's used-K word `ukw`, the setup words beyond
  `r28` (`rd11`, `r35`) or the round's first block `r56`, and a negative row (`r56 < rnd`) would
  address outside the table. Discharge: `LFits` in the blocks gains `v.su = setup p L g (refVL
  p L g R bal)`, `v.ukw = ukv …`, `r56 = r28 - 1` and, at `pgLd`, `rowCond = false`; then `0 ≤
  row < kLength i`, `pgIdx row = row / 16` (multiply-high form) and `Pre.pageTable`.
- Sizes: `Proof2/LdWarp` 2,657 lines (round 10: 1,345), `Proof2/Lib/LocalSrc.lean` 108. Closure
  of `Bridge/OldSafety.lean` beyond the Proof2 base (`reach2.py`): 1,300 old files, 252.6k lines,
  unchanged (no safety class moved).

### Lane T1 round 11: lane L's safety tables not merged yet; `noUb` per role (plan, not done)

- **Lane L merge deferred.** Merging `lane-L` at dbf17d809 (round 9: `Lemmas/Kernel/Safety/
  {Table,Classes,Roles,Handoff,Schedule}.lean`, aligned `shape_ldM`/`shape_stM`) into this
  branch, with the library taken from lane L, failed the strict build outside tml-fa4:
  `Lemmas/Flow/Step/StopReason.lean:162` (missing cases `StepClass.shflValid`, `.nc`, `.alloc`)
  and `Kernels/FlashAttn4Fwd/Proof/Thread/FactsSchedWarpPos.lean:40` (`allocT` ambiguous with
  `Progress.Time.allocT`). Merging lane L's next head 6b1a427f0 instead made the tml-fa4 step
  files about 10 times slower (`Proof2/Epilogue/StepsTiles.lean`: 141 s with main's library,
  262 s with dbf17d809, still running after 2,500 s of CPU time with 6b1a427f0; every
  `Steps*.lean` of the four migrated roles alike), so that build was stopped. Decision: the
  branch stays on main's library (its head is the round-11 loader commit plus this note); no
  lane L lemma is used yet. Reported to lane L: the two errors, and a `site_cases` slowdown on
  the tml-fa4 step files at 6b1a427f0.
- **How `noUb` reaches the role table.** `RoleTable.Ok` asks, at every state satisfying the
  table's invariant `J`, that no shape is undefined behaviour (`safe`) and that the machine dies
  only at an exit (`death`). Every role's `Ref` here is guarded by `n .ub = 0 →` (a reference
  invariant holds only while no event so far was undefined behaviour), so `J := RefAll` gives
  nothing at a state after a `ub` event and `safe` cannot be shown there. Decision: per role,
  `role_step` proves the event is not `ub` from `ref_safe` (the role's shapes without their `ub`
  alternatives under `Ref`), then the guard is dropped (`ub_zero` becomes a consequence), and the
  role enters a `RoleTable` with `J := RefAll`. `Frame.RoleTable.noUb` then gives the class for
  the migrated threads; `noHasUb`, `noUnalloc` and the frames need every thread (`hall`), so they
  wait for the softmax warps.
- **The `ub` alternatives per role and the fact each needs** (shape tables as of this round):

  | Role | Sites with a `ub` alternative | Excluded by |
  |---|---|---|
  | startup | elections (`elect j`), `mbarrier.init` (`init n`) | the election's own fault condition (`fires_elect_mask`: the mask and the convergence of the warp, the collective source on two lanes); `shape_mbInit` (aligned address from `Pre.shared`, immediate count) instead of `shape_mbInitAny` |
  | output warp | scan, request reads (`word`, `q0`, `q1`); the tensor stores (`store st b`: `isStore` counts undefined behaviour too) | reads: `shape_ldM`, the cuQ word addresses are 4-aligned (`Pre.alignment`, the address forms of `Reads.lean`); stores: the tensor store's own fault conditions under the O map (`store_issue`) |
  | MMA warp | allocation read, request reads, waits, elections, `tcgen05.mma`, commit, alloc/relinquish | reads by `shape_ldM`; elections as the startup's; the MMA descriptors' validity (`MatrixUnsafe` side, the instruction and shared descriptors from `Mma.Ref`) |
  | correction warps | `barEnd`, Tensor Memory loads/stores/wait, final stores and LSE | Tensor Memory addresses and shapes from `Correction.Ref`; final stores by `shape_stM` (aligned output/LSE addresses) |
  | loader warps | request and page-table reads, local stores, copies, elections, tensor copies | reads and stores by `shape_ldM`/`shape_stM` (local offsets from `lacc_loc`, request words 4-aligned); `cp.async` sizes and addresses; elections as above; the tensor maps from `Pre.maps` |

  The death clause per role: the output, MMA and startup machines die only at their returns
  (`ref_next` already has the form); the correction and loader machines also die at a read whose
  bytes do not rebuild and at the scheduler's division without a rule (`afterTiles`); the local
  words rebuild (`LdWarp/Mem.lean` shows each byte is a store's byte; with the store's byte index
  below its size, `littleEndianBits` is defined), the launch words rebuild by `inputReadValue`.
- Tried this round (not committed): an output-warp table `EvA` with the misalignment condition
  at the reads, proved by `site_shape` with the role's `ep_shape` options. `site_shape` fails at
  the first scan read with "internal exception #5" when the goal's undefined-behaviour alternative
  carries the condition (after `shape_ld` fails, the fall-through to `shape_ldM`); the alignment
  lemma (`rd_aligned`, from the address forms of `expect_word`/`expect_q`) checks. Library
  request for lane L: a `site_shape` test on a load whose table keeps the misalignment condition
  (the tml-fa4 output warp's `word .first`, pc 2776). Draft kept at
  `.lake/own/t1/draft/Safe.lean` in this worktree (scratch, untracked).
- Not done this round: the `ref_safe` lemmas above and the guard removal (task 2), the frame and
  unit hand-offs (task 3), the softmax glue (task 4: the softmax fragment still lacks its numeric
  sites on its branch), and `LdWarp.PgSrc` (round 11 above). Order for the next round:
  `PgSrc`; the output warp's and the loader's reads by `shape_ldM` (one `ref_safe` per role with
  `J` unguarded, the pattern for the others); the startup's `mbarrier.init`.
- **Task 3 (frames and unit hand-offs): which groups wait for the softmax warps.** A write frame
  (`RoleTable.write_frame`) and the hand-off's source fact (`Obj.src`: every record of a barrier
  object is a declared producer's arrival, an initialization or a poll) quantify over every
  thread. The softmax warps' threads are stubs after their first event, so no frame or source
  fact over a shared region or barrier object holds yet, whichever roles the group names: every
  group waits for the softmax warps to be followed. What does not wait, and exists: the count
  side of each hand-off on the followed roles (`Epilogue.stage_budget`, the correction warps'
  arrival closed forms in `Correction.RefQ`, the MMA warp's ledger, the loader's `RefCounts` per
  slot barrier), and the per-role write sets (`wr_ev` for the loader's local stores; the output
  warp's `store_issue`).

### Lane T1 round 12: the page-table premise discharged (2026-11-21)

- **`LdWarp.PgSrc` is proved, not assumed** (`Proof2/LdWarp/Page.lean`, `pg_word`): a page-table
  load of a loader lane at a state with the reference values returns the launch's page-table word.
  The premise is deleted from `LdWarp.lexpect`, `step`, `good` and `Common.good_all`, whose only
  remaining premise is `CorrWarp.DataSrc`.
- `LFits` in the blocks gains `PgOk`: the setup words are `setup` of a state with the same scan
  state and used-K word; the used-K word is the chosen request's (`ukv`); outside the first block
  `%r56 = %r28 - 2`; at `pgLd` the round's condition `rowCond` is false (`RowOk`). These are kept
  by every block step (`BlkKeeps` gains the used-K word, `%r56` and `RowOk`; `pgEnter_row`: the page
  loop's entry reaches a load only with the condition false) and by the block ends (`AfterBlk`).
  This is the record proposed in round 11 with `%r56 = %r28 - 2` (the code's value; round 11's note
  said `- 1`) and with the setup kept as "a setup of the same request" rather than a closed form.
- Arithmetic: the tile's blocks are in `[-2^24, kLength i / 128 + 1]` (`r28_ge`, `r28_le`, from the
  code's signed shifts), so a round's row is nonnegative and at most `kLength i + 127`
  (`row_prime_le`, `row_later_le`; the lane's row bits and the block offset are disjoint, an `or`
  of a word below `2^7` with a multiple of `2^7` is the sum); with `rowCond` false it is below
  `kLength i`; `pgIdx` is `row / 16` (`pgIdx_eq`); the address is
  `pageTableBase + 4 (i stride + row / 16)` (`ptAddr_toNat`) inside the page-table region
  (`Pre.pageTable`, `Pre.ranges`), and `inputReadValue` with `Pre.pageBytes` gives the word.
- Generic word bounds (`toNat_add32_le`, `toNat_andi_le`, `toNat_shl`, `toNat_or32_add`,
  `toSigned_addi`, `toSigned_sub32`) are in `Proof2/Lib/WordBound.lean` (lane L candidate).
- Sizes: `Page.lean` 505 lines, `Lib/WordBound.lean` 98.

### Lane T1 round 12: lane L merged; `noUb` per role started (2026-11-21)

- Merged `origin/main` 945ab1917 (batch 24) and lane L's safe tip be1d8c350 (coordinator: being
  merged into main as batch 25). After the merges every file under `Lemmas/`, `Tests/`, `Tools/`,
  `tests/` equals lane L's; the kernel files are this branch's. Full strict build of the merged tree
  (`Tools/build.sh`, 9921 jobs) at the end of the round, with the statement and axiom checks.
- **Why `RoleTable.Ok` does not fit the migrated roles as they stand.** Its `safe` and `death`
  obligations are stated at every state satisfying `J`, with no execution in context. (1) Every
  tml-fa4 `Ref` is guarded by `n .ub = 0` (it is discharged at every state that fires an event,
  `ub_zero`, since an undefined-behaviour event is a thread's last), so at a state after such an
  event `J` holds vacuously and `safe` cannot be shown. (2) The correction, loader and output
  machines die (`next = none`) at a read whose bytes do not rebuild; that they rebuild is an
  execution fact (the launch's words by `inputReadValue`, the softmax statistics by
  `CorrWarp.DataSrc`, the loader's local words by the lane's stores). Decision: a generic lemma
  with the two obligations at the followed states of the thread's own events,
  `Frame.noUb_of_followed` (`Proof2/Lib/NoUb.lean`, lane L candidate): no event fired from a
  followed state is undefined behaviour (`safe`), and the machine dies at such an event only if
  it is an exit (`live`); then no event of the thread is undefined behaviour (a dead machine's
  events are undefined behaviour by `Frame.fired`, and it died at an earlier exit, the thread's
  last event). With it no `Ref` changes: `safe` reads the unguarded `Ref` through `ub_zero`.
- **First role class: the output warp's reads** (`Proof2/Epilogue/Safe.lean`). `EvA` keeps Core's
  misalignment condition at the scan's and the request's reads (`shape_ldM`), `rd_aligned`: under
  `Fits` the address is `cuQBase + 4 i` with `cuQBase` 4-aligned, so `ref_safe` (every site but
  the tensor stores) holds.
- **The pc 2776 `site_shape` failure, for lane L.** Minimal case: the output warp's
  `word .first` (pc 2776, `ld.global.b32` from a 64-bit register) against a table whose
  undefined-behaviour alternative carries the misalignment condition. `site_shape` applies
  `shape_ld` first; its `hub : ∀ f, P ⟨pc, .ub f⟩` goal is unprovable there, and the failure
  reported is that attempt's (`internal exception #5`, since `site_shape_step` rethrows the first
  lemma's error). `shape_ldM` itself fails too: its condition is `w / 8 = 0 ∨ loc.addr % (w / 8 *
  ds.length) ≠ 0`, where `ds` is the literal instruction's `MemAccess.regs` (`dsts.filterMap id`),
  which `shape_close`'s simp set does not reduce, so the hypothesis never matches the table's
  `addr % 4 ≠ 0`. The site checks by hand (`epa_read`: `shape_ldM`, the location by `site_read` /
  `site_acc`, then `simpa [PTX.MemAccess.regs]`). Library fix: add `PTX.MemAccess.regs` (and
  `List.filterMap`) to the simp set that introduces `shape_ldM`'s / `shape_stM`'s condition, and
  report the last lemma's error instead of the first when every class lemma fails.
- **What `noUb` for warps 8 to 15 still needs, per role** (each a `safe` case of
  `noUb_of_followed`, plus `live`):

  | Role | Undefined-behaviour shapes not yet excluded | `live` (death only at the exit) |
  |---|---|---|
  | startup (every warp) | elections (`elect.sync` with the immediate mask `-1` is never undefined behaviour: `fires_ub` with `elect_imm_ok`, no state fact needed; the same for the MMA and loader elections), `mbarrier.init` (the address is the shuffled shared base `x1` plus a constant, 8-aligned once the startup's `Ref` gives `x1`; the count is a register (`%r615`, `%r617`, … from the startup's table), so lane L's `shape_mbInit`, which takes an immediate count, does not apply: a register-count variant of `tma_mbarInit` is a lane L candidate) | no death before the gate |
  | output warp | none: the reads (`Epilogue/Safe.lean`) and the tensor stores (`Epilogue/StoreSafe.lean`, `store_safe`: under `Fits` the operands are the work item's, so `tensorStoreSpec` returns a specification); `fired_safe` covers every site | reads rebuild (`expect_word`, `expect_q`) |
  | MMA warp | done (`Mma/Safe.lean`, `sync_safe`, no state fact needed): the polls (every barrier address is the shared base plus a multiple of 8, the ring slot's too), the elections, the relinquish. The request reads (`Mma/SafeRd.lean`, `read_safe`: `fires_load_reg_al`, `Proof2/Lib/LoadAl.lean`, with the cuQ and used-K addresses under `MFits`). The allocation read (`alloc_read_safe`: `fires_load_al`, the general form in `Lib/LoadAl.lean`). The commits (`Mma/SafeCm.lean`, `commit_safe`: 8-aligned barrier words, and the one-CTA resolution in a one-dimensional launch). Open: `tcgen05.mma` (descriptors; Inkling's kernel-local `qk_ok` is the model), the deallocation (its address operand is the recorded word `ta`, a 32-bit word only by `Mma.Ref`) | reads rebuild (`expect_uk`, the allocation word) |
  | correction warps | done (`Correction/Safe.lean`, `misc_safe`): the closing `bar.arrive 2, 416`, the `tcgen05.wait::st` waits. The Tensor Memory loads (`Correction/SafeTm.lean`, `ld_safe`: every load address is the warp's quarter in the lane field, `tm0`/`tm1` plus a column, so its lane field is the warp's lane base; no state fact). The Tensor Memory stores (`st_safe`: the same addresses, sixteen four-byte float operands, `tcSt_word_ok`). Open: final shared stores and LSE (`shape_stM`) | statistics reads rebuild (`DataSrc`) and the scheduler's division |
  | loader warps | done (`Loader/Safe.lean`, `elect_safe`): the elections; the request reads (`Loader/SafeRd.lean`, `read_safe`, at sub-step 0). The page-table reads (`LdWarp/Page.lean`, `pg_safe`: the address of `pg_addr` is 4-aligned). Open: the pointer rounds' local stores (`ptS`), `cp.async`, tensor copies | local words rebuild (needs the last covering store: `LdWarp/Mem.lean` shows only that every byte is some store's) |

  Route for the non-memory classes: Lemmas' `fires_ub` with the templates' "not undefined
  behaviour" lemmas (`Lemmas/Flow/UbFree.lean`, `UbStop.lean`: `elect_imm_ok`, `barArrive_imm_ok`,
  `tcLd_word_ok`, `ld_ok`, …) at each site's register facts, one walk per role like
  `site_shape` (a `site_safe` tactic is a lane L candidate). `noUb` is not assembled in
  `Top/Safety.lean` this round: with every role's classes above open it would only restate the
  field as premises.
- Remaining (lane T1), in order: (1) the zero-sum fix above once `seg_sym` steps the two zero
  cases (or a hand-stepped segment); (2) per role the `safe` and `live` cases of
  `noUb_of_followed` by the table above, elections first (no state fact), then the reads by
  `shape_ldM`, then the instruction classes with `fires_ub`; (3) `noUb` for warps 8 to 15 in
  `Top/Safety.lean` with the softmax warps as the named premise; (4) the softmax glue: not started,
  since the softmax fragment's `stepAt` still takes `NumSteps` (52 states) as a premise (its
  branch, `tmlfa4-softmax-proof2`, "What lane T1 needs"); the glue waits until it does not, as
  decided in round 9.
- Item (a) done: `Epilogue/StoreSafe.lean` (`store_safe`, `fired_safe`), by the old tree's
  `storeOrigin` and the same evaluation of `tensorStoreSpec` as `Proof/OutputStore.lean`'s
  `storeTemplate`, with `storeVals_eq` for the operand words.
- Closure of `Bridge/OldSafety.lean` beyond the Proof2 base: 1,300 old files, 252.6k lines,
  unchanged (no field moved). The bridge's `noUb` is the old `noFault` (75 files, 18.8k lines),
  all inside the 1,265 files `Proof/Safety/Assembly.lean` reaches, so discharging `noUb` alone
  would not shrink the closure.

### Lane T1 round 12: zero row sums (2026-11-21; open)

- **Finding (softmax lane, branch `tmlfa4-softmax-proof2` 3c53b5753):** `RowSumPos` is false for
  padding rows. Past the query length the Spec allows every bias value to be `-inf`, and on a tile
  with no plain rounds such a row's sum is 0. `CorrWarp.DataSrc` asks a positive sum at the
  row-sum reads (`ExpectD` at `fsum`), so it cannot be discharged for such launches, and
  `Top.correct2`, whose `SafePremises.dataSrc` (and `Bridge.OldPremises.dataSrc`) is that premise,
  is vacuous for them. No other premise of `Top.correct2` asks for a positive sum (searched:
  `Correction/`, `CorrWarp/`, `Top/`, `Progress/`).
- **Fix (designed, not committed):** the correction fragment follows the zero-sum path. The code
  computes `lg2.approx.ftz.f32` of each sum at pcs 9061 and 9075 before its `selp` on `sum != 0`
  (`%p737`, `%p740`) picks the LSE or `0fFF800000`. On `+0` the kernel's `lg2` assumption has no
  rule (it covers positive finite operands) and Core's table gives `-inf` (`lg2Table`:
  `posZero ↦ -inf`); the following `fma.rn.f32` and `mul.f32` read the infinity as such under
  `idealArith` (no `inf - inf`: the other operand is `scale * rm` with `rm` finite or `-inf`), and
  the `selp` stores `-inf` (`lseSel` already gives that value). Changes: the machine continues at
  the final stage's last arrival when both sums are nonnegative and at the first LSE store when
  the second is (`Correction/Machine.lean`); `Ref.pos` becomes `0 ≤ rsOf` and `ExpectD` at `fsum`
  asks `0 ≤ x` (`RefNext.lean`; `ns_close` gains a `linarith` close for the stop branches);
  `stepAt_lse` steps the four sign cases (`StepsLse.lean`); `CorrWarp.DataSrc` asks a nonnegative
  sum. The final chunks are already total in the sum (`fRecip 0 = 1`). The softmax side proves
  `0 ≤ rs`, and `0 < rs` when the row maximum is finite (the Result part needs it for the stored
  rows).
- **What blocks it:** with these changes `RefNext.lean` and the positive case of `StepsLse.lean`
  check, but the zero cases do not: `corr_sites` fails at `fdone 1 1` with `try_rt: internal
  exception #5` whenever a sum is the literal `0` (the walk through pc 9061 or 9075 would need
  `seg_sym` to evaluate Core's approximate-function table on `+0` and the ideal arithmetic on a
  `-inf` operand), and at `lse 0` with "the rule for the instruction at 9075 depends on the
  condition `0 < v.rs1`" when only `0 ≤ v.rs1` is known (that case splits like `fdone 1 1`).
  Request for lane L: `seg_sym` steps of an `.approx` instruction on a table row (`lg2(+0)`) and of
  `fma`/`mul` under `idealArith` with an infinite operand. The patch is kept untracked at
  `.lake/own/t1/zero-sum.patch` in the lane T1 worktree (176 lines); applying it and closing the
  two zero cases of `stepAt_lse` completes the fix.
- Second attempt (same day, after the coordinator's priority note): the patch applies and builds
  up to `StepsLse.lean`; the zero cases still fail in `corr_sites` at `fdone 1 1` (pc 9056, its
  segment runs to the LSE store at 9073 through `lg2` at 9061, `fma` 9062, `mul` 9063, `selp`).
  A hand proof needs that segment cut at 9061, a step of `lg2.approx.ftz.f32` on `+0` by Core's
  table (`Core/Float/Approx.lean`, `lg2Table`: "(.posZero, .inf true)", the kernel rule declining
  because its operand is not positive) with an outcome lemma in the form of
  `Lemmas/Flow/Ex2Core.lean`, and steps of the `fma.rn.f32` and `mul.f32` on that `-inf` under
  `idealArith`, before `seg_sym` resumes; the same at 9075 for the second sum. That is the step
  support requested from lane L, which the coordinator has scheduled; the patch stays unapplied
  so that every commit builds. Until it lands `Top.correct2`'s `dataSrc` premise is false for
  launches with a zero-sum padding row.
- Third attempt (after merging main 693bc5a5b, lane L round 11 with `Lg2Core.lean` and
  `rule_step`'s condition deciding): the `lg2` step at 9075 now declines on a zero sum and takes
  Core's table. Two steps still fail: (1) at 9077 (`mul.f32` by `ln 2` after the `fma`), `rule_step`
  evaluates `mulEReal (↑(scale · rm₁) + ⊥) ↑c` and stops, because the `fma`'s sum is left as EReal
  `↑x + ⊥` (the addend on the right), which its simp set does not reduce (`addEReal_bot_coe` is
  `addEReal ⊥ ↑y`; `EReal.add_bot` is missing), so `mulEReal_bot_pos` never applies; the kernel's
  `using [EReal.add_bot, …]` list does not reach `rule_step`'s own simp set. (2) the three zero cases
  at `fdone 1 1` still end in `try_rt: internal exception #5` (not located). Requests for lane L:
  `EReal.add_bot`/`EReal.bot_add` in `rule_step`'s simp set, and the location of (2). The patch with
  the four-way case split and the `lse 0` split is kept untracked at
  `.lake/own/t1/zero-sum2.patch`.

### Lane T1 round 12: lane L merged; `noUb` per role started (2026-11-21)

- Merged `origin/main` 945ab1917 (batch 24) and lane L's safe tip be1d8c350 (coordinator: being
  merged into main as batch 25). After the merges every file under `Lemmas/`, `Tests/`, `Tools/`,
  `tests/` equals lane L's; the kernel files are this branch's. Full strict build of the merged tree
  (`Tools/build.sh`, 9921 jobs) at the end of the round, with the statement and axiom checks.
- **Why `RoleTable.Ok` does not fit the migrated roles as they stand.** Its `safe` and `death`
  obligations are stated at every state satisfying `J`, with no execution in context. (1) Every
  tml-fa4 `Ref` is guarded by `n .ub = 0` (it is discharged at every state that fires an event,
  `ub_zero`, since an undefined-behaviour event is a thread's last), so at a state after such an
  event `J` holds vacuously and `safe` cannot be shown. (2) The correction, loader and output
  machines die (`next = none`) at a read whose bytes do not rebuild; that they rebuild is an
  execution fact (the launch's words by `inputReadValue`, the softmax statistics by
  `CorrWarp.DataSrc`, the loader's local words by the lane's stores). Decision: a generic lemma
  with the two obligations at the followed states of the thread's own events,
  `Frame.noUb_of_followed` (`Proof2/Lib/NoUb.lean`, lane L candidate): no event fired from a
  followed state is undefined behaviour (`safe`), and the machine dies at such an event only if
  it is an exit (`live`); then no event of the thread is undefined behaviour (a dead machine's
  events are undefined behaviour by `Frame.fired`, and it died at an earlier exit, the thread's
  last event). With it no `Ref` changes: `safe` reads the unguarded `Ref` through `ub_zero`.
- **First role class: the output warp's reads** (`Proof2/Epilogue/Safe.lean`). `EvA` keeps Core's
  misalignment condition at the scan's and the request's reads (`shape_ldM`), `rd_aligned`: under
  `Fits` the address is `cuQBase + 4 i` with `cuQBase` 4-aligned, so `ref_safe` (every site but
  the tensor stores) holds.
- **The pc 2776 `site_shape` failure, for lane L.** Minimal case: the output warp's
  `word .first` (pc 2776, `ld.global.b32` from a 64-bit register) against a table whose
  undefined-behaviour alternative carries the misalignment condition. `site_shape` applies
  `shape_ld` first; its `hub : ∀ f, P ⟨pc, .ub f⟩` goal is unprovable there, and the failure
  reported is that attempt's (`internal exception #5`, since `site_shape_step` rethrows the first
  lemma's error). `shape_ldM` itself fails too: its condition is `w / 8 = 0 ∨ loc.addr % (w / 8 *
  ds.length) ≠ 0`, where `ds` is the literal instruction's `MemAccess.regs` (`dsts.filterMap id`),
  which `shape_close`'s simp set does not reduce, so the hypothesis never matches the table's
  `addr % 4 ≠ 0`. The site checks by hand (`epa_read`: `shape_ldM`, the location by `site_read` /
  `site_acc`, then `simpa [PTX.MemAccess.regs]`). Library fix: add `PTX.MemAccess.regs` (and
  `List.filterMap`) to the simp set that introduces `shape_ldM`'s / `shape_stM`'s condition, and
  report the last lemma's error instead of the first when every class lemma fails.
- **What `noUb` for warps 8 to 15 still needs, per role** (each a `safe` case of
  `noUb_of_followed`, plus `live`):

  | Role | Undefined-behaviour shapes not yet excluded | `live` (death only at the exit) |
  |---|---|---|
  | startup (every warp) | elections (`elect.sync` with the immediate mask `-1` is never undefined behaviour: `fires_ub` with `elect_imm_ok`, no state fact needed; the same for the MMA and loader elections), `mbarrier.init` (the address is the shuffled shared base `x1` plus a constant, 8-aligned once the startup's `Ref` gives `x1`; the count is a register (`%r615`, `%r617`, … from the startup's table), so lane L's `shape_mbInit`, which takes an immediate count, does not apply: a register-count variant of `tma_mbarInit` is a lane L candidate) | no death before the gate |
  | output warp | none: the reads (`Epilogue/Safe.lean`) and the tensor stores (`Epilogue/StoreSafe.lean`, `store_safe`: under `Fits` the operands are the work item's, so `tensorStoreSpec` returns a specification); `fired_safe` covers every site | reads rebuild (`expect_word`, `expect_q`) |
  | MMA warp | done (`Mma/Safe.lean`, `sync_safe`, no state fact needed): the polls (every barrier address is the shared base plus a multiple of 8, the ring slot's too), the elections, the relinquish. The request reads (`Mma/SafeRd.lean`, `read_safe`: `fires_load_reg_al`, `Proof2/Lib/LoadAl.lean`, with the cuQ and used-K addresses under `MFits`). The allocation read (`alloc_read_safe`: `fires_load_al`, the general form in `Lib/LoadAl.lean`). The commits (`Mma/SafeCm.lean`, `commit_safe`: 8-aligned barrier words, and the one-CTA resolution in a one-dimensional launch). Open: `tcgen05.mma` (descriptors; Inkling's kernel-local `qk_ok` is the model), the deallocation (its address operand is the recorded word `ta`, a 32-bit word only by `Mma.Ref`) | reads rebuild (`expect_uk`, the allocation word) |
  | correction warps | done (`Correction/Safe.lean`, `misc_safe`): the closing `bar.arrive 2, 416`, the `tcgen05.wait::st` waits. The Tensor Memory loads (`Correction/SafeTm.lean`, `ld_safe`: every load address is the warp's quarter in the lane field, `tm0`/`tm1` plus a column, so its lane field is the warp's lane base; no state fact). The Tensor Memory stores (`st_safe`: the same addresses, sixteen four-byte float operands, `tcSt_word_ok`). Open: final shared stores and LSE (`shape_stM`) | statistics reads rebuild (`DataSrc`) and the scheduler's division |
  | loader warps | done (`Loader/Safe.lean`, `elect_safe`): the elections; the request reads (`Loader/SafeRd.lean`, `read_safe`, at sub-step 0). The page-table reads (`LdWarp/Page.lean`, `pg_safe`: the address of `pg_addr` is 4-aligned). Open: the pointer rounds' local stores (`ptS`), `cp.async`, tensor copies | local words rebuild (needs the last covering store: `LdWarp/Mem.lean` shows only that every byte is some store's) |

  Route for the non-memory classes: Lemmas' `fires_ub` with the templates' "not undefined
  behaviour" lemmas (`Lemmas/Flow/UbFree.lean`, `UbStop.lean`: `elect_imm_ok`, `barArrive_imm_ok`,
  `tcLd_word_ok`, `ld_ok`, …) at each site's register facts, one walk per role like
  `site_shape` (a `site_safe` tactic is a lane L candidate). `noUb` is not assembled in
  `Top/Safety.lean` this round: with every role's classes above open it would only restate the
  field as premises.
- Remaining (lane T1), in order: (1) the zero-sum fix above once `seg_sym` steps the two zero
  cases (or a hand-stepped segment); (2) per role the `safe` and `live` cases of
  `noUb_of_followed` by the table above, elections first (no state fact), then the reads by
  `shape_ldM`, then the instruction classes with `fires_ub`; (3) `noUb` for warps 8 to 15 in
  `Top/Safety.lean` with the softmax warps as the named premise; (4) the softmax glue: not started,
  since the softmax fragment's `stepAt` still takes `NumSteps` (52 states) as a premise (its
  branch, `tmlfa4-softmax-proof2`, "What lane T1 needs"); the glue waits until it does not, as
  decided in round 9.
- Concrete start for the output warp's tensor stores (next session): `Epilogue/Store.lean`'s
  `store_kind` already has the store site's register facts (`hreg` from `valueOf` over
  `Flow.live`); the old tree's `Proof/OutputStore.lean` `storeTemplate` evaluates the template to a
  `tensorStore` event given the O map pointer (7868), the policy word (7869), the coordinate
  words, the 128-aligned staging slot (`storeSource`), nonnegative origins and an aligned box, and
  `tileStore` gives all of them from the base, row, column, head and end registers with
  `batch < p.batch`, `head < p.heads`, `256 * tile < p.qLength batch`. Those three bounds are the
  chosen work item's (`Epilogue.store_issue` derives the same item from `Fits`), so `safe` at a
  store site is `fires_ub` against `tileStore`'s event. `Proof/OutputStore.lean` is already in the
  Proof2 base closure (`Store.lean` imports it).
- Session note: this round ended on the context limit before items (a) to (d) of the
  coordinator's task-2 list (output tensor stores, MMA `tcgen05` operations, correction Tensor
  Memory operations, stores and read-rebuild death clause, loader copies and local-load last
  store); none of them is started beyond the note above.
- **Warp 13 has no undefined behaviour** (`Epilogue/NoUb.lean`, `noUb`, by
  `Frame.noUb_of_followed`; `live` assumes the event is no undefined behaviour, which `safe`
  gives). `safe`: the startup states of warps 8 to 15 are on the fence path (`StartAt`: shuffles,
  fence, barrier), whose shapes have no undefined-behaviour alternative; the role states by
  `fired_safe`. `live`: the startup machine dies only on another event kind than its site's; the
  output warp's (`next_none`) only at its exit, given `Expect` (re-derived after the fact with
  `GoodUpTo` from `good_all`): the reads rebuild, and the first pass's tile count step has its
  coordinate divisions' rules (`tiles_next`).
- `Top/Safety.lean`: the field `noUb` is narrowed to `noUbRest` (no undefined-behaviour event of
  a lane outside warp 13), and `Top.noUb` closes the class with `Epilogue.noUb`; `Bridge.ofOld`
  gives `noUbRest` from the old safety proof. The bridge's closure is unchanged by this (the old
  `noFault` is inside the files `Proof/Safety/Assembly.lean` reaches).
- The division question (whether the tile-count step can reach the code's divisions with no rule
  at a CTA without a work item) is settled by the scan, as in the old tree
  (`Proof/EpilogueBatchChoice.lean`: a CTA whose scan runs out of requests leaves at pc 2878 with
  `batch ≤ first`, before the ballot; the coordinate segment `Proof/EpilogueCoordinates.lean`,
  `computeSelectedTile`, is reached only with `batch < p.batch`). In the new tree: `Fits` at
  `tiles false` keeps the scan's end with its group inside the batch (`EndVals`) and the ballot
  (`BalOf`); `PickedPre` is these three facts, `picked_group`, `predv_iff`, `ballot` and `pvv_W`
  now take `PickedPre` (their proofs used only these), and `picked_of_pre` shows the chosen request
  is below the batch, so `Picked` holds and `chosen_divOk` gives both divisions' rules. No
  unproved fact is involved.
- Closure of `Bridge/OldSafety.lean` beyond the Proof2 base: 1,300 old files, 252.6k lines,
  unchanged (no field moved). The bridge's `noUb` is the old `noFault` (75 files, 18.8k lines),
  all inside the 1,265 files `Proof/Safety/Assembly.lean` reaches, so discharging `noUb` alone
  would not shrink the closure.

### Lane T1 round 13: the correction warps have no undefined behaviour (2026-11-22)

- A section "zero row sums are followed" stood here; it described `.lake/own/t1/zero-sum2.patch`
  as applied. It is not applied (the correction machine still stops unless both row sums are
  positive, `Correction/Machine.lean`, `fdone 1 1`); the state of that fix is "zero row sums
  (open)" above. The section is removed.
- **Warps 8 to 11 have no undefined behaviour** (`CorrWarp/NoUb.lean`, `noUb`, by
  `Frame.noUb_of_followed_live`, given `DataSrc`). `Top.noUb` uses it, and the premise `noUbRest`
  now excludes warps 8 to 11 as well as 13 (`Bridge.ofOld` unchanged but for one binder).
- `safe` (`fired_safe`), by site class:
  - the scheduler's and the request's reads: `Epilogue.rd_aligned` on the output-warp state of
    the reference values (`CFits` carries `Epilogue.Fits` on `toE d`, and the correction's address
    registers are the output warp's `rdAddr` terms); the used-K read by `Mma.addrK_toNat` on the
    chosen request;
  - the statistics reads (`rscale`, `fsum`, `fmax`, `ld.shared.b32 [%r567 + c]`): `%r567` is
    `sb + 4 row` and every offset a multiple of 4 (`al_statW`);
  - the rescale loads' implicit waits (`rldw`, sub-step 1 by `RefQ.sub`): selected by the
    kernel's `tcLdDataflow` assumption (`tcLd_wait_ok`);
  - the final shared stores (`fst`, `st.shared.v4.b32`, 64 sites): Core's only condition is a
    16-aligned address (`elemAcc`), and a shared address is truncated to 32 bits, so a sum of
    16-aligned words is aligned whether or not it wraps. Every term of the base register is
    16-aligned: the shared base (`Pre.shared`), the row times 128, the swizzle's `and` with 112,
    the lane offsets `±16`, `±32`, `±64`; the offsets are multiples of 16384 (`fst_safe`, by
    `al_tac`). The round-12 plan (an exact swizzled address with no wrap, for `stv_off_ok`) is not
    needed for this class: `stv_off_ok` is replaced by the alignment-only `stShared_ok`. The exact
    address is still what the write frame and the race classes will need.
  - the LSE stores (`lse`, `st.global.b32 [%rd203 + 0 / 512]`): `lseAddr` is the LSE base
    (4-aligned, `Pre.alignment`) plus two words shifted left by 2, modulo `2 ^ 64`
    (`lseAddr_al`); the source is the LSE or the `-inf` pattern, four bytes either way
    (`lse_safe`; sub-step 0 by `RefQ.sub`).
  - the rest as before (`misc_safe`, `ld_safe`, `st_safe`); every other shape has no
    undefined-behaviour alternative.
- `live` (`next_none`): the role machine dies only on an event of another kind than its site's
  (excluded by the shapes), at the exit, at a read whose bytes do not rebuild (excluded by
  `ExpectD`: the launch words by the scheduler's sources, the statistics words by `DataSrc`: this
  is the statistics-read death clause), and at the first pass's tile count when the coordinate
  divisions have no rule: `succ_scan` turns that step into the output warp's, and
  `Epilogue.tiles_next` on the reference values' output-warp state excludes it.
- New kernel-local lemmas (lane L candidates): `Proof2/Lib/MemAl.lean` (`storeAl_ok`, `stShared_ok`,
  `stGlobal_ok`, `ldShared_ok`, `ldGlobal_ok'`: a weak access at an aligned effective address
  of a register of the element's size is no undefined behaviour; replaces `Lib/StoreOff.lean`),
  `Proof2/Lib/WordAlign.lean` (`Al k x`, closure of alignment under the code's 32-bit operations,
  `al_tac`). `Common/NoUb.lean`: the startup cases of warps 8 to 15 (`start_safe`, `start_live`,
  `role_next_none`), now shared by `Epilogue/NoUb.lean` and `CorrWarp/NoUb.lean`.
- Check times: `CorrWarp/NoUb.lean` 18 s, `Correction/SafeSt.lean` 19 s.

### Lane T1 round 13: the softmax warps glued and followed (2026-11-22)

- Coordinator's change of plan: glue the softmax fragment now with its open numeric steps as a
  named premise. Merged the softmax branch's committed head (`tmlfa4-softmax-proof2` at
  dd5f73824; its uncommitted work in its own worktree is not taken).
- **The role's machine in the glue is `SmWarp.codeT`, not `Softmax.codeD`.** `frag_steps` needs
  the step obligation at every state of every role, and `codeD`'s numeric states (51,
  `D.numeric`) are the premise `Softmax.NumSteps`. Carrying it into `thread_sound` would put it on
  every theorem of the tree (`thread_sound` has 18 uses in 12 files, and everything above them).
  `codeT` is `codeD` with the invariant strengthened by the warp bound (warps 0 to 7) and, unless
  every softmax lane's numeric steps hold (`NumAll`, a Prop decided classically in `nextT`), with
  the numeric states excluded from the invariant and a transition into one replaced by a stop
  (`some none`, which `StepAt` admits with no obligation). So `thread_sound` keeps no premise
  (`SmWarp.stepAt`: the non-numeric states by `stepAt_ctl`, the numeric ones by `NumSteps` when
  `NumAll` holds), and under `NumAll` the role's successor is the data machine's (`next_eq`); the
  following theorems take `NumAll` as a premise. Its type of states is `Softmax.D` itself, so no
  cast appears.
- `Common/Roles.lean`: `Role.softmax` (last constructor), `frag .softmax := SmWarp.codeT`, the gate
  (shared base, warp word `g % L.block / 32`, warp below 8), `roleOf`. No ledger class yet: the
  fragment's classes `shfl` and `won pc` also count the startup's shuffles and warp 0's
  elections, so a class `soft c` needs `StartCls`/`Start0Cls` extended and the named barrier word
  `nbW` shown nonzero for every lane (the startup's `bar 0`); the role's `Ref` takes the fragment's
  counts existentially until the hand-offs read them. `Common/Sound.lean`: `frag_steps` and the hand-off from
  `Softmax.handoff`. Every role's `Ref` gains the softmax case as `False`.
- **The softmax warps are followed** (`SmWarp/Warp.lean`, `good`), given `NumAll`,
  `DataStoreSafe` of every lane, and `SmSrc`: the fragment's `ExpectD` at every state holding its
  invariant (the scheduler's words and shuffles, the tile count's division rules, bias bytes that
  rebuild, `f32` score payloads), as one premise on the execution like `CorrWarp.DataSrc`. Its
  scheduler part has the correction warps' sources (launch words, the scan collectives); the
  bias bytes are a protected read of the loader's copies; the scores are `TcLdDataflow`.
  `Ref`: at a startup state `StartAt0` on warp 0 (whose startup makes the elections and
  initializations, `start0_step_of`) and `StartAt` on the others, zero softmax counts; at a role
  state the startup's three shuffles and, unless an event so far was undefined behaviour,
  `Softmax.Ref` on the softmax classes. `role_step` is `Softmax.ok`'s `ref_next`.
- **Warps 0 to 7 have no undefined behaviour** (`SmWarp/NoUb.lean`): the startup's sites
  (`start0_safe`, `Common/NoUb0.lean`: the elections by the immediate mask, the
  `mbarrier.init`s at the shared base plus constants, 8-aligned, with constant register counts,
  `mbarInit_bits_ok`; this is task 4 of the round), the role's shape table without undefined
  behaviour (`Softmax.shapeS`), and the death clause of `ref_next`. `Top.SafePremises` gains
  `numAll`, `dataStore`, `smSrc` (and `Bridge.OldPremises` the same, which the old tree does not
  state), and `noUbRest` is narrowed to warps 12, 14 and 15.
- **No lane of warps 0 to 7 issues a tensor load** (`SmWarp/Kinds.lean`, `soft_noTensor`: every
  event of a softmax lane that is no undefined behaviour is fired at a startup or softmax site,
  and no instruction at a softmax site is a tensor load, by evaluation). `noTensorRest` and
  `noTensorAllocationRest` are narrowed to the loader warps (warp index above 13).
- Check times (strict build): `SmWarp/Warp.lean` 2.2 s, `SmWarp/NoUb.lean` 1.9 s,
  `SmWarp/Kinds.lean` 42 s (the evaluation over the softmax sites), `Common/NoUb0.lean` 2.6 s.
  Sizes: `Proof2/SmWarp` 4 files, `Common/NoUb0.lean`; 565 lines. Closure of
  `Bridge/OldSafety.lean` beyond the Proof2 base unchanged (1,300 old files): no group moved yet.
  Every role's `rcases` over `Role` gained the softmax alternative (`on_goal 7 => exact hR.elim`).

### Lane T1 round 13: ERR-SETMAXNREG on the role table (2026-11-22)

- **`noRegister` is proved** (`Top/Register.lean`) and the field is removed from
  `Top.SafePremises`; it uses the premises the following already carries (`dataSrc`, `numAll`,
  `dataStore`, `smSrc`). By the library's `Frame.noSetMaxNReg_of_first`:
  - every lane is followed with its role's invariant (`JR`: `SmWarp.Ref` below warp 8, `RefAll`
    above; `goodR`);
  - a request is fired at its role's entry (`IsEntry`, `req_entry`: the shape tables admit a
    request only at the entry site; the MMA warp's startup machine by its code at pc 1909 and its
    invariant), and the startup fires none;
  - the entry's instruction gives the request (`fires_setMaxReg_op`, the code at pcs 3102, 7746,
    2769, 179, 1907), and the role is the warp's (`role_warp`), so it is `req w`: `inc 184` below
    warp 8, `dec 64` for warps 8 to 11, `dec 80` above, constant on a warpgroup;
  - no role machine moves to its entry (`next_not_entry`: the softmax machine by its listed
    successors, `Softmax.succ_cases` and an evaluated check that no list holds `setmax`; the
    correction, output and loader machines by unfolding their successors; the MMA warp's startup
    machine by its own), and after a role state every state is a role state that is no entry
    (`no_reentry`), so every request is the thread's first.
  Check time 10 s.
- **The bridge's closure is unchanged by moving a field** (1,300 old files beyond the Proof2
  base). `Bridge.ofOld` derives every remaining field from the old assembly's `SafeGoal`
  (`Proof/Safety/Assembly.lean`, which alone reaches 1,265 of the 1,300 files), so the closure
  falls only when the last field leaves and the bridge is deleted. The measure of progress is the
  list of fields left in `Top.SafePremises`: after this round `noUbRest` (warps 12, 14, 15),
  `noUnalloc`, `noRace`, `noMixed`, `noBarMismatch`, `noTma`, `noTmemSource`, `noInputWrite`,
  `noAligned`, `noSharedLifetime`, the two tensor-load fields (loader warps), the five Tensor
  Memory fields, `noCtaBar`, `noWarpDivergence`, `noMbarUninit`.

### Lane T1 round 14: the role table and ERR-MBAR-UNINITIALIZED (2026-11-22)

- **The thread machine's role table** (`Top/Table.lean`, `table`): the library's
  `Frame.RoleTable` with `J := JR` (every lane's reference invariant) and, per state, its
  fragment's shape table (`TEv`: the startup's; the output warp's; the MMA warp's allocation prefix
  `Mma.PreEv` and role table; both correction tables `Ev ∧ EvR`; the loader's; the softmax warps'
  `EvS`; nothing at a stub). `table_shape` (each fragment's `Shape`, for every thread) and
  `table_followed` (`goodR`) give the library's per-class skeletons for every thread of the launch.
  The remaining classes use the same table.
- **`noMbarUninit` is proved** (`Top/Mbar.lean`, `noUninit`; the field is removed from
  `Top.SafePremises`), by `Frame.RoleTable.noMbarUninit` and `Frame.Handoff.of_bar_upTo`:
  - the objects (`Top/MbarStart.lean`): warp 0's startup initializes 34 mbarriers at the shared
    base plus `initOff n` (0 to 232 by 8, and 320 to 344), read off the startup's value table at
    each `mbarrier.init` (`init_ev`, with `Proof2/Lib/MbarInit.lean`'s `fires_mbInit_reg`);
  - every use names one of them from a role state (`Top/MbarUse.lean`, `use_obj`): the output
    warp's ready and free barriers, the correction and softmax warps' constant offsets (the softmax
    warps' shifted by the stage), the MMA warp's polls and commits (ring slots from `RefQ.regs`; a
    commit's target is the issuer's CTA by `noTcCommitUnsafe` in a one-CTA-cluster launch,
    `commit_target`), the loader's polls, arrivals and tensor copies (the existing `slot_loc`,
    `arrive_loc`, `dw_loc`, `tw_loc`, `ta_loc`, ring slots from `RefRing`); the startup names objects
    only by its initializations;
  - a role state follows the lane's CTA barrier (`role_bar0`: the startup enters a role only from
    its barrier site, `succ_exit_bar`);
  - the initializations exist before the elected lane's barrier (`init_exists`): the user's first
    barrier-0 event is passed, so every lane of warp 0 arrives (`member_arrival_any`); lane 0 walks
    the startup to its first election (`lead_path` with `K = 3`) and learns the leader `ld`; lane
    `ld`'s elections all return `ld` (`elect_leader`), so it walks the fixed 55-site path
    (`pathSite`, `succ_lead`), reaches its barrier at position 54 and initializes object `n` at
    position `initPos n` before it;
  - barrier 0 is the startup's alone (`bar0_ev`: every other `bar` of the shape tables names
    barrier 2, 11, 12, or a register word that is never 0: `corr_nbW_ne`, `soft_nbW_ne`, the
    latter by evaluation over the sixteen warp words), which gives `NamedBar.Sources` and the
    hand-off; a returned lane passed its barrier (`exit_bar0`).
- **Why `RoleTable.noMbarUninit` and not `noMbarUninit_of_handoff`.** The hand-off form's object
  frame obligation (`hO`) sees only the state, the invariant and the shape, not the execution; the
  MMA and loader warps' invariants hold their ring facts only while no event so far was undefined
  behaviour (`n .ub = 0 →`), which needs the event (`ub_zero`). The per-state form `hpub` has the
  event, and the hand-off is applied there (the same five lines as the library's form).
- Lane L candidates: `fires_mbInit_reg` (`Proof2/Lib/MbarInit.lean`); `commit_target` (a commit's
  targets in a one-CTA-cluster launch); the thread machine's role table pattern (`TEv`, shape and
  following from the fragments).
- Check times (strict build): `Top/Table.lean` 1.6 s, `Top/MbarStart.lean` 5.8 s,
  `Top/MbarUse.lean` 9.8 s, `Top/Mbar.lean` 6.4 s, `Lib/MbarInit.lean` 1.4 s.
- Fields left in `Top.SafePremises`: `noUbRest` (warps 12, 14, 15), `noUnalloc`, `noRace`,
  `noMixed`, `noBarMismatch`, `noTma`, `noTmemSource`, `noInputWrite`, `noAligned`,
  `noSharedLifetime`, the two tensor-load fields, the five Tensor Memory fields, `noCtaBar`,
  `noWarpDivergence`, plus the softmax premises `dataSrc`, `numAll`, `dataStore`, `smSrc`.

### Lane T1 round 14: the tensor-load fields and the input-write condition (2026-11-22)

- **Order.** The step list puts the softmax ledger classes and the race/mixed and Tensor Memory
  groups before these fields. Decision: take first the fields whose discharge is a static check or
  an existing in-closure lemma, since the memory-conflict groups need the softmax ledger, the write
  frame of every role and the T3 hand-offs, and gain nothing from waiting on these.
- **`noTensorRest`, `noTensorAllocationRest` removed** from `Top.SafePremises`. Every tensor load
  is one of the loader's Q and Bias copies through its ABI map (`Loader.actualInputDescriptor`,
  a check of the decoded copies against the ABI's map parameters), which zero-fills `bf16`
  elements (`noActualTensorUnsafe`) and whose large backing the ABI supplies
  (`actualInputBacking`). `Top.noTensor` and `Top.noTensorAllocation` now take no premise.
  Closure cost: `Proof/TensorSafety.lean` and `Proof/LoaderInputDescriptors.lean`, 2 old files
  (841 lines) beyond the Proof2 tree's closure; both are static checks that move with the switch.
  The role-table proofs `migrated_noTensor` and `SmWarp.soft_noTensor` stay (no longer used here).
- **`noInputWrite` removed** (`Top.noInputWrite`): every global write intent is an LSE store or a
  tensor-store box byte (`globalWriteIntentSources`, static), the LSE stores address their row's
  word (`Thread.lseWriteShape`) and the tensor stores a scheduled work item's box
  (`OutputWarp.issuedBox`, from `Epilogue.store_issue`), so `outputIntentFootprint_of_sites` gives
  the O/LSE write frame and `OutputIntentFootprint.noInputWrite` the condition. All four lemmas are
  already in the Proof2 tree's closure (no old file added).
- Measured (import scan): Proof2 without the bridge reaches 340 old files (74.8k lines), before
  338 (74.3k). The old proofs of the remaining fields each add 97 to 404 old files
  (`Safety/Mbar` 404, `Safety/SharedLifetime` 399, `Thread/PollUniformity` 399,
  `TmemReadConflicts` 392, `TmemOutputRescaleConflicts` 383, `Safety/Allocation` 300,
  `TmemAccess` 272, `Protocol/NamedBarriers` 127, `NamedBarrierConflicts` 110, `Alignment` 105,
  `MmaResourceOrder` 97), so they are rebuilt on the role table, not reused.

### Lane T1 round 14: the loader warps' local stores (2026-11-22)

- `Loader/SafeSt.lean`, `lst_safe`: the page-table rounds' `st.local.b32` and the pointer rounds'
  `st.local.b64` are no undefined behaviour (the parked draft, fixed). The unification failure was
  the order of elaboration: `accessAcc_local64` was elaborated before the access `a` was known.
  `lst_ok` takes the template's `ub` equation first, which fixes `a`, so the address register and
  the alignment goal are concrete. Check time 4.8 s. Remaining for the loader's `noUb`: the
  `cp.async` copies (source alignment from the page pointers), the tensor copies (the old
  `loaderInputOut`, in the closure, needs the coordinate words below `2 ^ 31` and box-aligned from
  `LFits`), and the death clause.

### Lane T1 round 14: zero row sums followed (2026-11-22)

- Merged `origin/main` 0fc855655 (batch 31: lane L's zero row-sum steps). Applied
  `zero-sum2.patch`: the correction machine continues on nonnegative row sums (`0 ≤ rs0 ∧
  0 ≤ rs1`, `Correction/Machine.lean`, `fdone 1 1`), `stepAt_lse` splits each sum into positive and
  zero, and on a zero sum the segment steps take `lg2.approx` of `+0` by Core's rule (`-inf`) and
  the code's `selp` picks the `-inf` pattern; `CorrWarp.Warp`, `Correction.Ref` and `RefNext`
  follow the weaker guard. The EReal lemmas the patch passed through `using`
  (`EReal.add_bot`, `mulEReal_bot_pos`) are dropped: `rule_step` has them. So the correction
  warps' reference invariant no longer excludes a CTA whose rows include padding, and `Top.correct2`
  is not vacuous on such launches. Checked: no positivity condition on `rs0`, `rs1` remains in
  `Proof2/Correction`, `Proof2/CorrWarp` or `Proof2/Top`; `DataSrc` asks a nonnegative payload at a
  row-sum read. Full strict build of the merged tree (10044 jobs) with the statement and axiom
  checks passes; `Top.correct2`, `noUninit`, `Top.noInputWrite`, `Bridge.ofOld` use `propext`,
  `Classical.choice`, `Quot.sound` only.
- Check-time defect: `Correction/StepsLse.lean` takes 501 s (it was 123 to 309 s with one case);
  each of its seven branches walks every site of the role with `corr_sites`. Fix (not done): one
  file per branch, or a site walk restricted to the final stage's sites.

### Lane T1 round 14: what the remaining fields need (2026-11-22)

Fields left in `Top.SafePremises` after this round: `noUbRest` (warps 12, 14, 15), `noUnalloc`,
`noRace`, `noMixed`, `noBarMismatch`, `noTma`, `noTmemSource`, `noAligned`,
`noSharedLifetime`, the five Tensor Memory fields, `noCtaBar`, `noWarpDivergence` (and the softmax
premises `dataSrc`, `numAll`, `dataStore`, `smSrc`). What each needs on the new tree, as found
this round:

- **`noUbRest`.** MMA warp: the prefix is done (`Mma/SafePre.lean`); open are the 64
  `tcgen05.mma` sites (the old `qkIssueOut`, in the closure, and `pvIssueOut`, one old file of 172
  lines, evaluate the templates from register facts; the MMA table's descriptor words `v.qd`,
  `qkStart`, `pvlo` must first be pinned in `Mma.Ref` to the old forms `sharedDescriptorWord ...`),
  the deallocation (its operand is the recorded word `ta`, which `Mma.Ref` does not yet state is a
  32-bit word), and the death clause. Loader warps: local stores done (`Loader/SafeSt.lean`); open
  are the `cp.async` copies, the tensor copies (`loaderInputOut` needs the coordinate words below
  `2 ^ 31`; the Bias row `1152 - 128 · max(r29, 0)` needs the range of `r29` from `LFits`) and the
  death clause.
- **`noTmemResource`, `noTmemRelease`.** Lane L's `RoleTable.tmem1Facts` / `tmem1_safe`
  (lane-L 680855e73, batch 31) fit the MMA warp (`cta_group::1`, 512 columns). They need, per
  resource event, the thread's count of resource events so far (0 at the allocation, 1 at the
  relinquish, 2 at the deallocation, 3 at the exit of warp 12): a ghost class for resource events
  in the thread ledger, or a closed form in `Mma.Ref`; and the deallocated column is 0, which
  needs the allocation read's word as a protected read of the allocation's store
  (`Consistent.alloc512_result`).
- **`noBarMismatch`, `noAligned`.** The library's schedule forms
  (`RoleTable.noBarMismatch`, `noAlignedMismatch_of_schedule`) need, per role, the `k`-th
  barrier (and aligned `tcgen05`) event's site and operands as a function of `k` and warp-uniform
  values: closed forms of the barrier counts at each site in the roles' `Ref`s (the correction and
  softmax warps' named-barrier rounds).
- **`noCtaBar`.** Count mismatches are excluded per barrier id (ids 0, 2, 3 to 10, 11 and 12 carry
  `none`, 416, 64 and 128: `bar0_ev`, `corr_nbW_ne`, `soft_nbW_ne` give the id classes); duplicate
  arrivals need the `bar.arrive` protocol between the softmax and correction warps (a warp's next
  arrival on a named barrier after the generation completed), a T3 hand-off.
- **`noRace`, `noMixed`, `noTmemSource`, the Tensor Memory access/read/write fields,
  `noSharedLifetime`, `noTma`, `noUnalloc`.** All need the write and access frames of every role
  (the softmax warps' shared stores are stated without addresses in its table; the MMA prefix's
  allocation store too) and the T3 hand-offs over the ring and unit barriers with the softmax
  classes in the thread ledger; `noTma` also the object histories' phases.
- **`noWarpDivergence`.** `not_warpDivergent_pollAgree` needs every lane-compared instruction's
  guard as a warp-uniform function at the role sites; this goes through `Walk`, which the role
  machines do not yet connect to.

### Lane T1 round 15: the MMA warp's Tensor Memory operations (2026-11-22)

- Coordinator's order for this round: the write frame, then the allocation word `ta = 0`, then
  the fields it unblocks. Finding: `ta = 0` needs `Tmem.One.Tmem1Ops` first, because the stored
  column is 0 by `Tmem.One.alloc_zero` (which needs only `Tmem1Ops`), not by
  `Consistent.alloc512_result` (which needs a fault-free allocator history, that is
  `¬ ResourceUnsafe`, the field being proved: circular). So `Tmem1Ops` comes first.
- **`Tmem1Ops L X 12` is proved** (`Top/TmemOps.lean`, `tmem1Ops`), and the exit part of
  `Tmem1Facts` (`tmem1_exit`):
  - `Top/TmemSite.lean`: `Mma.tsite` (resource operations before a role site: 1, then 2 after the
    relinquish, 3 after the deallocation) and `Mma.succ_tsite` (the role reaches its last sites only
    in the order relinquish, barrier, deallocate, exit);
  - `Top/TmemCount.lean`: `mma_count`, the thread's count of resource events before each event of
    a lane of warp 12 is `tcnt` of its state (the startup and the prefix's `setmaxnreg` count none,
    the allocation one); `Mma.rd_kind` gives the relinquish and the 512-column deallocation from
    the code (`Mma/SafePre.lean`'s `pre_kind` the prefix's request and store);
  - `tev_res`: no other role's table nor the startup admits a resource event.
- Remaining for the two Tensor Memory fields (`tmem1_safe`): the deallocation's column is 0, that
  is the word `ta` the MMA lanes read at `sb + 312` is the allocation store's `b32 0`. The order is
  Core's `AllocResultBefore` (no barrier needed); the value needs `alloc_zero`, `tmemPairResult`
  and a protected read whose write classification needs, per role, that no other write covers
  `sb + 312 … sb + 315`: the softmax statistics stores start at `sb + 368`, the correction warps'
  output staging stores at `sb + 2848` or above (the swizzle moves an address by at most 112), the
  loader's copies above `sb + 68496`, its tensor loads at `sb + 3072` or above. Those bounds are
  the next piece (an interval closure for the code's 32-bit address terms, like `WordAlign`'s `Al`).

### Lane T1 round 16: the write frame below `sb + 316` and the Tensor Memory resource classes (2026-11-22)

- **Interval closure** (`Proof2/Lib/Interval.lean`, lane-L candidate): `Iv lo hi x` for the code's
  32-bit words, with forward rules (sums without wrap, negative immediates, shifts, `and` with an
  immediate, `or`, choice, exclusive or with a bounded word) and the backward signed step
  `iv_pm` (`x ± n` by a choice of immediates). The swizzle `xor32 (andi (shru x 3) 112) x` moves
  `x` by at most 112 (`iv_swz`, from `x ^^^ m + 2 (x &&& m) = x + m`). `eff_le` reads a
  non-wrapping shared effective address. Bounds are stated as literals; side conditions are
  small linear facts closed by `omega`.
- **The write frame** (`Top/WFrame.lean`, `wr_low`): a thread write or linear copy that lands in
  shared memory below `sb + 316` is fired from the MMA warp's address-store state. Per role:
  the startup, the MMA role and the output warp write no memory (its tensor stores write global
  memory, `tstore_global`); the correction warps' final stores write at `sb + 2848` or above
  (`Top/WFrameCorr.lean`, `fst_wr`), their LSE stores global memory (`lse_wr`); the softmax warps'
  statistics stores at `sb + 368` or above (`Top/WFrameSoft.lean`, `stat_wr`); the loader warps'
  local stores local memory, their row copies at `sb + 68496` or above (`Top/WFrameLd.lean`,
  `cp_lo`, the slot below 3 from `RefRing`, the next slot at most 3), their tensor loads at
  `sb + 3072` or above (`tload_low`, from `Loader.actualInputBox`, already in the closure); no
  cluster launch control request (`noClcIssue`). Kernel-local store lemmas
  (`Proof2/Lib/StoreAt.lean`: `storeTmpl_wr`, `stShared_wr`, `stGlobal_wr`) are lane-L
  candidates.
- **The allocation word is 0** (`Top/TmemWord.lean`): `mma_trace` (`Top/TmemTrace.lean`) records
  along a lane of warp 12 that its allocation has no warp-collective `tcgen05` event before it,
  that lane 0's address store follows it, and that every role state past `ldAlloc` holds the word
  an earlier read returned (`Mma.succ_ta`, `Top/TmemTa.lean`: no step past the read changes
  `ta`). The read returns the store's bytes by `RoleTable.protected_read_of_followed`: the writer
  is lane 0's store (for another lane, the store its allocation waited for, from
  `allocResult_witnessed` and `DependencyOk.ready`; `alloc_writer`), ordered before the read by
  Core's `AllocResultBefore`; every other write of the word is excluded by `wr_low` and by
  `res_unique` (lane 0 allocates once). The store holds column 0 (`alloc_store_zero`: the
  allocation is the CTA's first record, `Tmem.One.first_recorded`, `alloc_zero`, and Core's
  `ResultOk`). Hence the deallocation frees column 0 (`Mma.dealloc_col`), `tmem1Facts` holds,
  and `noTmemResource`, `noTmemRelease` are removed from `Top.SafePremises` (`Frame.tmem1_safe`).
  No Core change, no new assumption; axioms of `Top.correct2`, `noTmemResource`,
  `noTmemRelease`, `Bridge.ofOld`: `propext`, `Classical.choice`, `Quot.sound`.
- **Check-time findings.** (1) A failing unification between two distinct 32-bit address terms
  (a leaf lemma for one stage's swizzled address tried against the other stage's) unfolds the
  `BitVec` arithmetic and took minutes per site (the 64 final stores ran past 60 CPU minutes);
  the closure therefore applies only the leaf lemma of the site's own stage. (2) `fin_cases` on
  the site's `Fin 16` index leaves `⟨j, _⟩` terms that make `code_lookup` and the value lookup
  about 3 s slower per site; the final stores are one theorem per site with literal indices
  (`fst_site`, a command macro) and a dispatcher. Strict build times: `Lib/Interval` 2.4 s,
  `Lib/StoreAt` 1.8 s, `Top/TmemTa` 3.6 s, `Top/TmemTrace` 2.9 s, `Top/WFrameSoft` 2.2 s,
  `Top/WFrameLd` 6.4 s, `Top/WFrameCorr` 10 s, `Top/WFrame` 4.7 s, `Top/TmemWord` 3.0 s.
- Lane-L candidates: `Lib/Interval.lean`, `Lib/StoreAt.lean`, `res_unique`, the
  `cta_group::1` address-store value (`alloc_store_zero`) and writer (`alloc_writer`) for a
  library `Tmem1` source, `tstore_global`, `tload_ge`.

### Lane T1 round 16: what the MMA warp's `noUbRest` part needs (2026-11-22)

- **Done this round**: the deallocation (`Mma.dealloc_safe`, `Top/TmemWord.lean`: with the word 0
  the request frees 512 columns at column 0 and has a rule). The read at `ldAlloc` returns
  four bytes that rebuild (`ld_word`), which is the death clause's case at that site.
- **The 64 `tcgen05.mma` sites** (`qk b j`, `pv b j`). Core's `mmaSmemTmpl` and `mmaTmemTmpl`
  fault when a shared descriptor does not decode (`TcShared.decode`: bits 15 and 31 of the low
  word must be 0, the fixed fields of the high word `dhi` hold) and, for PV, when the A operand's
  Tensor Memory column plus its offset leaves `[0, 2^16)` (`tmemOffset`); `makeOperands` only
  needs the one-CTA group (`singleCtaGroup`), and the accumulator column is not checked at issue.
  The low words are the received broadcast words (`s0`, `s4`, `s6`, `s10`, the Q descriptors
  `qd` from the broadcast at `bcast`) plus offsets of at most 1030, and the A columns the words
  `s3`, `s7`, `s9`, `s12`. `MExpect` asks a broadcast only for a 32-bit word, so `MFits` does not
  know them. Plan: `MExpect` at `sh k` asks the word to be lane 0's operand of the same broadcast
  for some state (`∃ v', x = shSrc L v' k`: an `and` with `16320` and a tag bit, or a constant),
  which `mexpect` gives from the source lane at the same site (the broadcast's index is a
  function of `ps`, `sh_band`); `MFits` keeps the property of each recorded word and of `qd`
  (the base `(sb + 35840) / 16` masked is at least 2048 by `Pre.shared`, so the alternating
  `∓2048` moves do not wrap); the site proofs then evaluate the templates as `qkIssueOut` did,
  with the bounds from `Lib/Interval.lean`. The death clause follows `CorrWarp.next_none`
  (tile count by `Epilogue.tiles_next`, reads by `MExpect`, `ldAlloc` by `ld_word`).
- **Old-file closure** (import scan): Proof2 without `Bridge` reaches 340 old files (74.8k
  lines), unchanged by this round (the tensor-load destinations and `noClcIssue` were already in
  it); `Bridge/OldSafety.lean` alone reaches 1,445 (282.8k).

### Lane T1 round 17: the MMA warp has no undefined behaviour (2026-11-22)

- **Broadcast words** (`Top/MmaRecv.lean`): a broadcast site receives lane 0's operand of a
  broadcast site (`recv_word`: the source lane at the same shuffle count is at a broadcast site;
  a scan shuffle or the `bcast` broadcast is at another count, by `mshfl_same`, `mband` and
  `four_of`). Every operand has the pattern `BW` (below `2 ^ 27`, low 16 bits at most 16320:
  an `and` with 16320 and a tag bit, or a small constant, `bw_shSrc`); `bcast` sends `qx L`.
  Decision: no closed form of each word is kept (the plan of round 16 asked lane 0's exact
  operand); the pattern is all the descriptor checks read, and it holds for every slot value.
- **Descriptor words along the trace** (`Top/MmaDesc.lean`, `mma_desc`): every role state keeps
  `DOk` (the recorded words have the pattern; past `bcast` the Q descriptors are `qv L (neg s)`,
  where `neg` marks the sites between a QK block's `-2048` move and the next block's `+2048`
  move, `Mma.succ_desc`; `qv_back`: the two moves cancel, the low word being above 2048).
- **The 64 MMA issues** (`Top/MmaSafe.lean`, `mma_safe`): `mmaSmem_ok`, `mmaTmem_ok` (the
  templates have a rule when the registers hold words, the descriptors decode, the enable is a
  predicate, the group is one CTA, and the A column plus `8 j` stays below `2 ^ 16`);
  `decode_join` (the high word `dhi` is fixed; the low word below `2 ^ 31` with bit 15 clear);
  `qv_decode` (`qx L` is `65536 + (sb + 35840) / 16`, between 67776 and 69632 by `Pre.shared`,
  so the moved descriptors keep bit 15 clear); `qlo_bw`, `pvlo_bw` (B low words within 1030 of
  their broadcast word). One theorem per issue with literal indices (`qk_site`, `pv_site`).
- **`Mma.mma_noUb`** (`Top/MmaNoUb.lean`): `noUb_of_followed_live` with the read, poll,
  election, commit, MMA and deallocation sites (`role_safe`) and the death clause (`role_live`:
  scan sites as the output warp's `Epilogue.next_none`, the tile count through `tiles_none` —
  the MMA warp's coordinate divisions are the output warp's terms, `afterTiles_none` —, the
  request reads by their reference, `ldAlloc` by `ld_word`). `Top.SafePremises.noUbRest` now
  covers the loader warps 14 and 15 only. Axioms of `Mma.mma_noUb`, `Top.correct2`: `propext`,
  `Classical.choice`, `Quot.sound`.
- Check-time findings: a hygienic macro that names a local hypothesis fails silently inside
  `first` and the fall-through alternatives then spent minutes; the B-word bounds are lemmas
  (`qlo_bw`, `pvlo_bw`) rather than a backward tactic, because unifying `iv_addi`'s `↑n` with an
  integer literal, or one nesting of `addi` with another, unfolds the 32-bit arithmetic. Strict
  build times: `Top/MmaRecv` 42 s (the step lemma `succ_desc` over every site), `Top/MmaDesc`,
  `Top/MmaSafe` 8.3 s, `Top/MmaNoUb` 3.9 s.

### Lane T1 round 17: what the loader warps' `noUbRest` needs (2026-11-22)

- Merged `origin/main` 582c598e9 (batch 34: `seg_fp` built as a term, stated values closed by
  reflexivity). Full strict build passes (10135 jobs). `Correction/StepsLse.lean` still takes
  565 s (the defect of round 14 stands; the split is not done).

- Done: the page-table and request reads (`Loader/SafeRd.lean`), the local stores
  (`Loader/SafeSt.lean`), the elections (`Loader/Safe.lean`); the shapes of the local reads,
  the pointer reads and the shuffles have no undefined-behaviour alternative.
- Open, per site class:
  - the scheduler's scan reads (`word`): as `Mma.word_safe`, from `LFits`' output-warp values;
  - the 192 row copies (`cp`, Core's `cpAsyncTmpl`): the shared destination is a multiple of
    16 (the swizzled row base, `Al`), the source size word is 16 or 0 (`valuesRows`), and the
    global source `x0 ||| x1 << 32` plus 0 or 128 must be a multiple of 16. The words `x0`,
    `x1` are received at `xl`, `xh` from the lane that loaded them from local memory at `lw`,
    which holds the pointer the page round stored (`ptS`: the KV base plus the page index
    times the page stride plus the row offset). Plan: as for the MMA warp, a pattern of the
    received words (a multiple of 16 below the KV region's end) kept along the trace, from
    the source lane's local word (`LdWarp/Mem.lean`, `PgOk`) and `Pre.alignment` of the KV
    base and strides; one theorem per site class with literal indices;
  - the 14 tensor copies (`tc`): the old `loaderInputOut` (in the closure) evaluates the
    template from the coordinate words, which must be below `2 ^ 31`, and the Bias row
    `1152 - 128 max(r29, 0)` needs the range of `r29` from `LFits`;
  - the death clause: the reads rebuild (launch words, local words), the scheduler's tile
    count as the output warp's (`Epilogue.next_none` through the loader's `succ_scan`).

### Lane T1 round 18: the loader warps have no undefined behaviour (2026-11-22)

- **The row-address pattern** (`Top/LdAddr.lean`, `Top/LdLocal.lean`, `Top/LdRecv.lean`,
  `Top/LdAddrTrace.lean`). Decision, as planned in round 17: a pattern of the recorded words, not
  their closed forms. `Loader.AOk`: the low words `l0` (address load, sub-step 0) and `x0` (row
  shuffle) are multiples of 16. Every other step keeps both words (`succ_aok`, by per-helper
  lemmas `keepA_*`, 8 s). A pointer round stores `rd12`/`rd13` plus twice a stride combination;
  the bases are multiples of 16 and the strides of 8 (`Pre.alignment`), so the stored address is a
  multiple of 16 modulo `2 ^ 64` for every page and row word (`pt_m16`); byte 0 of an address load
  comes from a pointer round's 8-byte store at the same offset (`wr_pt`), so the rebuilt word keeps
  the low bits (`rebuild_low`, `lw_low`). A row shuffle's source lane is at the same `xl` of its
  packet (`pkt_same`: equal shuffle counts in one CTA put both lanes at the same packet shuffle,
  `bband`), and sends its `l0` (`recv_low`). The induction (`aok_step`) is
  `Frame.inductive_lex (μ X)` on the state after each event: the source lane's state before its
  shuffle is the state after an event with one collective fewer. Not a conjunct of `LFits` or
  `Loader.Ref`, so no existing step proof changed.
- **The 192 row copies** (`Top/LdCpOk.lean`, `Top/LdCpSite.lean`, `Top/LdCpPrime/Warm/Steady`):
  `cp_ok` (Core's `cpAsyncTmpl` has a rule when both addresses are multiples of 16 and the size
  register is at most 16); destinations by the `Al` closure (the swizzle moves by multiples of 16;
  `al_rowsAt`, `al_shl1`), sources by `AOk` and the column offset (`wideU2_m16`, `and112_m16`),
  sizes `selp 16 0`. One theorem per site with literal indices (macro `cp_site`), 64 per file.
- **The 14 tensor copies** (`Top/LdTc.lean`, `tc_ok`): the map by `Loader.inputMapReady` (old
  file, already in the closure), destination the shared base plus a multiple of 128, barrier a
  multiple of 8, the column word a multiple of 8 by the `Al` closure with subtraction
  (`al_sub32`), so the `bf16` box start is 16-byte aligned for every value of `r29`, `rnd`: the
  round-17 plan's range of `r29` is not needed (a negative column is a box partly outside the
  tensor, which the map fills).
- **Assembly** (`Top/LdNoUb.lean`, `Loader.ld_noUb`): `noUb_of_followed_live` with the scheduler
  reads (`word_safe`), the request, page-table, local-store, election, copy and tensor-copy sites,
  and the death clause (`role_live`: scan sites as the output warp's through `succ_scan` and
  `tiles_none`; request and used-K reads by `LExpect`; page-table reads by `pg_rebuild`, split out
  of `pg_word` in `LdWarp/Page.lean`; local reads by `local_rebuild`).
  `Top.SafePremises.noUbRest` is removed: `Top.noUb` has no premise left for undefined behaviour.
- Lane-L candidates: `cp_ok`, `tc_ok` (generic template facts), `al_sub32`, `al_shl1`,
  `rebuild_low`, `LdWarp.not_bad_of_good` (an event of a thread followed everywhere is not bad),
  the carried-pattern induction (`aok_step`: a role-state predicate kept by every step, with the
  collective sources at lex predecessors).
- Check times (`lean`, transparent huge pages off, as `Tools/build.sh`): `LdAddr` 7 s, `LdLocal`
  5.5 s, `LdRecv` 2.6 s, `LdAddrTrace` 2.3 s, `LdCpOk` 2.4 s, `LdCpPrime`/`Warm`/`Steady` 8 s each
  (0.34 s per site), `LdTc` 10 s (2.5 s per site), `LdNoUb` 4.5 s.

### Lane T1 round 18: the old-safety bridge deleted (2026-11-22)

- **Order.** The brief lists, in order, the loader's `noUbRest` (done), the remaining safety
  fields, the bridge's deletion and the split of `Correction/StepsLse.lean`. The remaining fields
  (races and mixed sizes, `noUnalloc`, lifetimes, the Tensor Memory fields, barrier counts,
  `noCtaBar`, `noWarpDivergence`, `noTma`) each need the write and access frames of every role and
  the T3 hand-offs (round 14, "what the remaining fields need"); they are many rounds of work.
  Decision: delete the bridge and split `StepsLse` now (neither depends on the fields), then
  continue with the fields one class at a time.
- **`Bridge/OldSafety.lean` deleted.** Nothing imported it (`Bridge.ofOld` showed that the old
  tree discharges `Top.SafePremises`; `Theorem.lean` still goes through `Proof/Correct.lean`).
  Old-file closure (import scan of `Kernels.TmlFa4Fwd.Proof.*`): the Proof2 tree, now equal to
  `Top.Correct`'s closure, reaches 340 old files (74,781 lines); with the bridge it reached 1,449
  (283,295). The Proof2 tree without `Top` reaches 145 (30,252).

### Lane T1 round 18: `Correction/StepsLse.lean` split (2026-11-22)

- **Measured first** (`lean` with the profiler, transparent huge pages off): the old file took
  455 s (tactic execution 385 s); its seven sign branches each re-proved the three sites
  `fdone 1 1`, `lse 0`, `lse 1`. One theorem per site with only the branches it reads cut it to
  404 s in one file: the sites cost `fdone 1 1` 247 s (four sign cases of about 60 s each, of which
  one `seg_sym` of 18 to 22 s), `lse 0` 48 s (two cases), `lse 1` 13 s. The duplication was not the
  cost; the cost is the segments of the last final arrival through the two logarithms.
- **Split** (no generated runs): `LseBase.lean` (the scale, `stop_ok`), one file per sign case of
  the last final arrival (`StepsLsePP`, `StepsLsePZ`, `StepsLseZP`, `StepsLseZZ`), the first store
  (`StepsLseL0`), and the dispatcher `StepsLse.lean`. Strict build times (in parallel):
  `StepsLsePP`/`PZ`/`ZP`/`ZZ` 82 to 84 s each, `StepsLseL0` 43 s, `StepsLse` 12 s, `LseBase` 1.9 s;
  the critical path is 84 + 12 s instead of 565 s.
- **Defect left**: each sign case is still over 60 s and its `fdone 1 1 → lse 1` segment over
  15 s. The lever: cut that segment at pc 9074 (after the first row's logarithm and `selp`, before
  the second's) with the end state's table as the stated facts (`seg_cut`), so that each half reads
  one row sum's sign and is proved for two cases instead of four; or lane L's generated-value runs
  (`Tools/out_gen.py`, `SegD.outs_lit`) for the logarithm's straight-line run. Not done this round.

### The premises `Top.correct2` still takes (kept current by lane T1)

With `Bridge/OldSafety.lean` deleted, nothing discharges these; `Top.correct2` takes them as
hypotheses. Updated with every lane-T1 commit.

- `Top.SafePremises` (`Top/Safety.lean`), 17 fields:
  - softmax fragment premises: `dataSrc` (`CorrWarp.DataSrc`), `numAll` (`SmWarp.NumAll`),
    `dataStore` (`Softmax.DataStoreSafe`), `smSrc` (`SmWarp.SmSrc`);
  - safety classes: `noUnalloc`, `noRace`, `noMixed`, `noTma`, `noTmemSource`, `noAligned`,
    `noSharedLifetime`, `noTmemAccess`, `noTmemWrites`, `noTmemInstruction`, `noTmemReads`,
    `noCtaBar`, `noWarpDivergence`.
- Proved and removed from the premises: `noBarMismatch` (round 21, `Top/BarMatch.lean`).
- `Top.ProgressPremise` (lane T4's descent, given safety).
- `Top.ResultPremise` (the stored output and LSE values of a complete execution).

### Lane T1 round 19: the softmax counts in the thread ledger (2026-11-22)

- The barrier, hand-off and race classes need the softmax warps' counts as trace counts. The
  softmax fragment's counts were existential in `SmWarp.Ref` (`∃ c, Softmax.Ref (d, c)`), so no
  closed form reached the trace. Decision: the thread ledger gets the softmax classes
  (`Cls.soft c`, counting `Softmax.cls c` for the classes whose counts are closed forms in the
  places, `Softmax.Cnt.pointed`, on warps 0 to 7 only), and `SmWarp.Ref` links them:
  `∃ c, Softmax.Ref (d, c) ∧ ∀ c', c'.pointed → c c' = n (.soft c')`. The startup counts none of
  them (`ZeroS`, the startup invariant's third conjunct; a startup barrier is barrier 0, never a
  softmax lane's named barrier, `soft_nb_ne'`). The shuffle, ballot and election classes stay
  existential (their counts are not closed forms in the places).
- Changed: `Common/Roles.lean` (the class), `Common/Frame.lean` and `Common/Start0.lean` (the
  startup's class lemmas), `SmWarp/Warp.lean` (the link), `SmWarp/NoUb.lean`. No other proof
  changed.

### Lane T1 round 19: every lane's barrier ordinal from its role's classes (2026-11-22)

- Plan for `noBarMismatch` (and `noAligned`, `noCtaBar` later): a schedule per warp, the `k`-th
  barrier event's operands as a function of `k`, the warp and the CTA's tile (whether the first
  pass picked one, and its rescale rounds). The ordinal `k` is the thread's count of barrier
  events, `n (.mma .bar)` (the MMA ledger's class counts every barrier event of every lane).
- **`Top/BarCount.lean`, `bar_count`**: every state keeps `BarT`: no barrier event at a startup
  state; at a correction state one (the startup's barrier 0) plus the role's barrier classes
  (barrier 2 and the two named barriers, `Correction.cls .bar2`, `.nb 0`, `.nb 1`); at a softmax
  state one plus `Cls.soft .bar2`, `.nb`, `.sb`; at another role's state at least one. With the
  roles' closed forms of these classes (`Correction.RefQ`, `Softmax.RefQ`) the ordinal at a
  barrier site is a closed form in its site and rounds. By `Frame.RoleTable.stateInv`
  (`Proof2/Lib/StateInv.lean`, lane-L candidate: a state predicate kept by every step of a
  followed thread holds at all its states) on the thread machine's role table.
- Check time: `Top/BarCount.lean` 3.5 s, `Lib/StateInv.lean` under 2 s.
- Next: the correction warps' rounds at the second pass (the late sites leave `RefQ`'s round
  count free; a second state predicate fixes the named-barrier count there from the tail's), the
  CTA-uniformity of the tile's block count (`bs_ref` and the loader's `r28Ref_cta` pattern), the
  softmax warps' ordinals, then the schedule and `noBarMismatch`.

### Lane T1 round 19: the correction warps' barrier schedule (2026-11-22)

- **`Top/BarCorr.lean`**: `corrB L g T k`, the operands of a correction lane's `k`-th barrier
  event for the CTA's tile `T = tileC p L g` (none, or its rescale rounds), and `corr_sched`: every
  barrier event of a correction state has the operands of its ordinal (`n (.mma .bar)`, by
  `bar_count`) in the schedule. The ordinals at the barrier sites are closed forms of `RefQ`
  (`corr_ord`); the rounds of a round or the final stage are the tile's (`CorrWarp.bs_ref` from
  `CFits`); a lane without a tile is at the first pass's end (`noPicked_exit`, from `Mma.eband`);
  the second pass's rounds are the tile's by a second state predicate (`CLate`, `corr_late`: the
  named barrier 0's count is the tile's rounds plus two; it enters from the last final arrival or
  an LSE store, where `RefQ.tail` fixes the rounds, and no event of the second pass is at a named
  barrier). `tileC` is the same on two lanes of one CTA (`tileC_cta`). Check time 9.3 s.
- **What `noBarMismatch` still needs: the softmax warps' scheduler reference values.** The
  softmax fragment's invariant (`Softmax.Ref`) has the counts only; its scheduler words are not
  related to the CTA's picked tile (no `Epilogue.Fits` of the softmax scan state, unlike the
  correction warps' `CFits`, the loader's `LFits` and the MMA warp's `MFits`). The softmax
  warps' biased and plain round counts (`nB`, `nP` of the state's words) are therefore not known
  to agree on the lanes of a warp, and a softmax lane's `k`-th barrier cannot be compared with its
  warp's. Decision: build the softmax warps' scheduler reference next (`SFits`, the loader's
  `LFits` pattern: the output warp's `Fits` on the scan state with the shuffles shifted, followed
  with the collective sources), which `noBarMismatch`, `noAligned`, `noWarpDivergence` and the
  scheduler part of the `smSrc` premise all need. The softmax ordinals (`bar_count`'s softmax case
  with `Softmax.RefQ`, whose final stage fixes both round counts, `RefQ.fin`) then follow the
  correction warps' pattern.

### Lane T1 round 19: the softmax warps' scheduler reference values (2026-11-22)

- **`SmWarp.Ref` now carries `SFits`** (`SmWarp/Fits.lean`): the output warp's `Fits` of the
  softmax scan state at the thread's own shuffle and ballot counts (the softmax warps make no warp
  collective outside their scheduler, so there is no shift, unlike `CFits` and `LFits`), and from
  the used-K read to the final arrival the used-K word is the chosen request's. Kept by every
  step (`sfits_next`): the scheduler steps as the output warp's (`SmWarp/Sim.lean`, `succ_scan`;
  the first pass's end also sets the P parity, which `ofE` carries), the used-K read by its
  reference, the region from the used-K read to the final stores without a change of the scan
  state or the used-K word (`frameS`), the final arrival into the second pass by
  `Epilogue.fits_pass2`.
- **Sources** (`SmWarp/Src.lean`, `sexpect`): the reads' addresses by a second shape table for the
  reads (`SmWarp/Read.lean`, `EvR`, as the correction warps'), the launch words
  (`Epilogue.expect_word`, `expect_q`, the used-K word by `inputReadValue`), the scan's collectives
  from the source lanes at the same site by the output warp's positions directly
  (`Epilogue.shfl_same`, `vote_same`, `shfl_lt_vote`, `shfl_lt_exit`, `vote_exit`). `SmWarp.good`
  (moved to `Src.lean`) keeps its signature; the `smSrc` premise is still used for what the
  fragment's own `Expect` asks (it is not yet derived from `SFits`; doing so for the scheduler part
  is a later step).
- Strict build times: `SmWarp/Sim` 4.6 s, `SmWarp/Read` 28 s, `SmWarp/Fits` 36 s (the region's
  frame `frameS` over every region site), `SmWarp/Warp` 1.8 s, `SmWarp/Src` 2.8 s.
- Next: the softmax warps' barrier ordinals and schedule (as the correction warps'), then
  `noBarMismatch`.

### Lane T1 round 20: the softmax warps' barrier schedule (2026-11-22)

- `Top/BarSoft.lean`: the `k`-th barrier event of a softmax lane has the operands `softB` of `k`
  and the CTA's tile `tileS` (none, or the picked tile's biased and plain round counts, `nB` and
  `nP` of the chosen request's values `refVS`; one value for all lanes of a warp, `tileS_warp`).
  The ordinals are `RefQ` closed forms (`soft_ord`), the rounds' counts at the rounds' sites are
  the tile's (`nBP_ref`, from `SFits`), and at the second pass the stage and named barrier counts
  still say the tile's rounds (`SLate`, `soft_late` by `RoleTable.stateInv`). `soft_sched` is the
  per-event statement, as `corr_sched` for the correction warps. 14 s strict.
- The premises of `Top.correct2` are unchanged by this round (the list under round 19 holds):
  `noBarMismatch` still needs the CTA-level matching of the five roles' schedules.

### Lane T1 round 21: ERR-BARRIER-MISMATCH (2026-11-22)

- `Top/BarMatch.lean`, `noBarMismatch`: every barrier event of a lane has the operands `schedB` of
  its ordinal among the lane's barrier events (`bar_sched`): barrier 0 at ordinal 0 (every warp's
  startup), `softB` for warps 0 to 7, `corrB` for warps 8 to 11, barrier 2 for 416 threads with
  `bar.sync` after the startup for warp 12; the output and loader warps make no barrier event
  after the startup's (`ld_nobar`, `Top/Mbar.lean`'s `epi_nobar`). The ordinal is the ledger's
  `.mma .bar` count (`cls_bar`, `count`); the event's state, its reference invariant and its shape
  come from `RoleTable.ev_of_ne_ub`; the state has no earlier undefined behaviour (`ub_zero`). The
  schedule depends on the lane only through its warp index and the CTA's tile (`schedB_warp`), and
  `Frame.noBarMismatch_of_schedule` gives the class. 8.2 s strict; `Top/Safety.lean` uses it and
  the `noBarMismatch` field of `SafePremises` is removed.

## Proof2: the correction warps as a site machine

`Proof2/Correction/Machine.lean` is a `Flow.Code` machine for warps 8 to 11 from their
`setmaxnreg` (pc 7746) to the `ret` (243 sites; 16 rescale-load waits and 192 vector-store
elements are further states at sub-steps 1 to 3).

- A state carries the sub-step `k` of its instruction (`Code.sub`): the four elements of a
  `st.shared.v4` fire at sub-steps 0 to 3, and a rescale load (a `tcLdDataflow` site) loads at
  sub-step 0 and performs its implicit wait at sub-step 1 (`rldw`). States at other sub-steps
  are excluded by the invariant (`k = 0`, or a sub-step the site has, `Site.midOk`), so their
  obligations hold vacuously (`stepAt_junk`). Conditional successors are plain `if`s whose
  branches are at sub-step 0; the role's `lands_auto` rule (`Base.lean`) proves the sub-step in
  every branch by `ite_cases` and the segment by `seg_auto`, else `seg_sym`.
- Risk R2 materialized on the scan: the first pass's `total` site (whose segment reads
  `%ctaid.x` and branches to five successors) did not finish within ten minutes, under the
  library's `SiteIte` rule and under the role's rule alike; `down .first` takes 22 s and
  `up .first 0` 8 s. (Resolved in round 2 below: an undecided loop test, now decided by
  `ctaR_succ_le`.)
- Proved so far (`Steps*.lean`, by `site_cases`): 47 of the 243 sites — the start (4), the
  ballots and choices of both passes except the first pass's tile count (5), the request's reads
  and the named barriers before the rounds (6), the rounds' barriers, ballots, store waits and
  arrivals (10), the final stage's barriers, statistics reads, polls, fences and arrivals except
  the reciprocal and the LSE (16), and the end (6). Four are overrides: the two store waits and
  the two `bar.arrive`s (`corr_issue` with the continuation lemmas above). The Tensor Memory
  overrides (`Loads.lean`: `corr_rld`, `corr_rldw`, `corr_tst`, `corr_fld`) are written; their
  segments wait for the float lemmas above. Check times (strict build, parallel): start 19 s,
  select 26 s, request 95 s, rounds 68 s, final 28 s, end 9 s.
- The scheduler's two passes are the output warp's arithmetic on other registers (recorded in an
  `Epilogue.D`), with one difference: the role reads `%ctaid.x` itself (pc 7803), so the CTA
  index in its table and successor conditions is the code's term `ctaR` (under the launch with
  the role's parameters explicit, the launch its segments run on), and the coordinates and loop
  registers are restated on it (`coords`, `loopRegsR`). Its equality with the CTA index of the
  launch is a fact for the reference invariant.
- The machine follows every value: a 32-bit load or shuffle records the word and stops on another
  kind; a statistics word (scale, row sum, row maximum) and a Tensor Memory element record their
  real number (`.float .f32 x`, the ideal-arithmetic payload) and stop on another kind. A Tensor
  Memory element of another kind would make the following `mul.rn.f32x2` leave the ideal rule;
  stopping there keeps every segment's arithmetic in the ideal reading, and that the elements are
  payloads is left to the reference invariant (the MMA results and the softmax writes are
  payloads under `idealArith`).
- Library lemmas written here for promotion (`Proof2/Lib/TcSteps.lean`): `fires_barArrive_next`,
  `fires_tcWaitSt_next`, `fires_tcSt_next` (a `tcgen05.st` no assumption selects with
  `tcStWaitLd`), `holds_setRegs_live` (the facts after a Tensor Memory load from those before),
  `Code.step_issueAt` (`step_issue` whose continuation reads the program counter),
  `Code.step_tcLd`, `Code.step_tcLdLoad`, `Code.step_tcLdWait` (a `tcgen05.ld`, and the two
  sub-steps of one selected by `tcLdWait`). Library gaps recorded for lane L: `advances` should
  include `bar.arrive`, `tcgen05.wait::st` and `tcgen05.st`; `site_step` has no class for
  `tcgen05.ld`; `seg_sym`'s walk runs Core's local rules, so it does not evaluate a float
  instruction on a recorded real (`setp`/`selp` with an immediate, `rcp.approx`, `lg2.approx`),
  and `seg_fp` does not reduce the ideal rule of a `mul.rn.f32x2` on packed payloads to a
  state without a fault. The segments with such instructions (the rescale and final chunks, the
  scale comparison before each rescale ballot, the reciprocal before each final stage, the LSE)
  need the local-run lemmas of `Lemmas/Flow/MulPairCore.lean`, `Recip.lean` and `FloatRead.lean`
  (`mulsE_run`, `unpacks_run`, `recip_run`, `fsetp_imm`), as the old tree's
  `CorrectionRescaleCode.lean` and `CorrectionReciprocal.lean` use them; they are not written
  yet.
- `Ledger.lean`: `Code.counted` over the classes arrivals and successful polls per barrier,
  CTA-barrier arrivals per id, Tensor Memory loads and stores, shared and global stores.
- `Ref.lean` states the count conjuncts of the reference invariant (`RefRounds`, `RefCounts`)
  before their proofs (risk R1): a barrier's count at a state is the number of its signal points
  passed, with the points inside a rescale round counted once per round done; a lane without a
  tile has passed only the points before the request's reads.

### Correction, round 2 (lane T2, task T2a)

- Lane L's round 3 (9ca825723) is merged: floating steps in `seg_sym` by the assumptions' rules,
  the `ctaid` decision, the promoted `Lemmas/Flow/Step/TcSteps.lean` (`Proof2/Lib/TcSteps.lean`
  is deleted; `Base.lean` imports the library module).
- The Tensor Memory load overrides are role lemmas instead of macros with named holes:
  `rld_ok` (a rescale load at sub-step 0) and `fld_ok` (a final load) in `Loads.lean` take the
  instruction, the destination registers (`ds = rBase + 0 … 15`, `fBase + 0 … 7`, by `rfl`) and
  the live-register check (by `kernel_rfl`); the destinations' values come from the general
  `lookup_run`. `corr_rld`/`corr_fld` only discharge these hypotheses (hygienic macros, so
  `site_cases` no longer shares a hole between sites). The address register of chunk 0 is an
  `ori` (`ori_lt` bounds it).
- The scan's exit test: `ctaR_eq` (the role's CTA term is the launch's CTA index under `Pre`,
  from `explicitParams_ctaidOf` and the one-dimensional grid) and the `sym_decide` rule
  `ctaR_succ_le` in `Base.lean`.
- The LSE (`StepsLse.lean`): the two LSE segments take `lg2.approx` of the row sums, which the
  kernel's `lg2` assumption makes exact only on a positive operand (other operands use Core's
  table: `-inf` for zero, NaN for a negative sum). The machine continues from the final stage's
  last arrival (`fdone 1 1`) only when `0 < rs0 ∧ 0 < rs1`, and from the first LSE store only when
  `0 < rs1`; otherwise it stops (`some none`). This is a stop on a recorded value, not on a kind
  (a deviation from rule M1): following a zero or negative row sum would follow Core's NaN and
  infinity through the `fma` and `mul`, whose values are not real payloads. The reference
  invariant has to supply the positivity (the row sum of a row with a finite maximum is at least
  1, the exponent of its maximum element). The LSE values are `lseOf p rs rm =
  (scale · rm + log₂ rs) · ln2F` with `scaleR p` the real number of `param_12` (`scale_read`,
  from `Pre.scales`) and `ln2F` the real number of the code's constant `0f3F317218`; the store
  address is `lseAddr`.
- Stops that `Fragment.OkAt.stop_iff` cannot express: besides the LSE positivity, the machine stops
  on a statistics word that is NaN (`RetKind.float` accepts NaN) and on a Tensor Memory element
  that is not an `f32` real (a Tensor Memory load returns no value in `recv`, so its return kind
  accepts every event). Following them would leave the ideal reading of the following `mul.rn`
  and `rcp`/`lg2`. `stop_iff` is therefore not stated for this role; `ref_next` (the machine does
  not stop under `Ref` and `Expect`) is the field that matters for `followed`, and the role's
  `Expect` must say that these values are real payloads (positive for the row sums). Recorded for
  lane L: a return kind for real payloads (`RetKind.real fmt`, no NaN) and a Tensor Memory load
  in `recv` would let `stop_iff` cover them.
- Consequence for the fragment: `Fragment.OkAt` needs `stop_iff` at every state, so the role
  cannot be a `Fragment` with `Ok` until the machine follows these values. What it needs, recorded
  for lane L: `seg_sym` stepping Core's own rules on non-real `f32` operands (the `lg2.approx`
  table on zero and negative numbers, `rcp.approx` on NaN, `fma`/`mul`/`selp` on infinities and
  NaN), so that a zero or negative row sum and a NaN statistics word are followed to their LSE
  value (`-inf` from the constant, or NaN) instead of stopping; and a value for a Tensor Memory
  load in `recv` with a return kind for its element vector. With both, `ret` is `.float .f32` at
  the statistics reads and the role satisfies `stop_iff` by `stop_cases`.
- State: every state of the machine has its step obligation (`Steps.lean`, `stepAt`, 243 sites;
  overrides: the two store waits, the two `bar.arrive`s, the Tensor Memory loads, waits and
  stores (`Loads.lean`), and the LSE stop). Check times per family with `lean`, in parallel on
  the shared host: start 22 s, scans 111–168 s per pass, select 28 s, tile count 221 s, request
  118 s, rounds 80 s, scale 20 s, rescale chunks 583 s (48 sites), final stage 37 s, final loads
  541 s (64 sites), final stores 77 s and 307 s per stage (128 states each), LSE 295 s, end 10 s.
- The final stage's load addresses (`fAddrs`): stage 1 addresses its chunks from `%r569`
  (`tm0 + 128 + 8 j`), not from `%r573`; the table had `tm1 + 8 j`, which only the transition
  from a chunk's last store to the next load reads (each such site of stage 1 took minutes before
  failing). Fixed in the table.
- Two table entries that only the tile count's transition establishes were not in the code's
  form, so `sym_close` compared them by unfolding and did not finish: the 64-bit head
  (`headW`, now the `cvt.s64.s32` term `truncBits 64 (cvtIntBits …)`) and the staging row
  (`stg0`, now `r32 a ||| r32 b` as `or.b32` reads both operands). With them the tile count
  checks in 221 s.
- `Shape.lean` (with `ShapeScan`, `ShapeRound`, `ShapeFinal`, `Shapes.lean`): the event-shape
  table `Ev` and `shape`, by `site_shape` per family (strict build: start, select and end
  families with the definitions 5 min, scan 99 s, round 328 s, final stage and stores 621 s). Kernel-side additions through the hook
  `shape_inv`: the Tensor Memory classes (`Proof2/Lib/ShapeTc.lean`), `bar.sync` with a register
  barrier id and `bar.arrive` with immediates, and a load without its address
  (`Proof2/Lib/ShapeBar.lean`), all for promotion by lane L. The shared-memory statistics reads
  are overrides (`corr_shld`): `shape_ld` needs the shared effective address evaluated, which
  `site_read` does not do for a shared window. Side goals that are symbolic (a barrier id below
  16, an address word below `2 ^ 32`) are discharged inside the hook before `site_shape`'s own
  closers, whose `decide` does not fail fast on them, and every bound lemma runs
  `with_reducible`: a failed unification of `nb0W` against `nb1W` at default transparency
  unfolded the bit-vector arithmetic for minutes. Recorded for lane L: `site_shape`'s fallback
  `apply shape_store hf` passes `hf` as the store-kind argument (so a plain store never matches),
  and its closers try `decide` before the role's `addr_by`.
- Hand-off (`Handoff.lean`): `live_7746` and `facts_init`, the first state's facts as an explicit
  list. For lane T1 (`Common/Roles.lean`, `Common/Sound.lean`): a constructor `Role.correction`,
  `frag p L g .correction := Correction.code p L g`, the exit case `.correction`, and a gate that
  fixes `x1 = sharedBase` and `x3 = g % L.block / 32`. The present `Gate (L) : Entry → D → Bool`
  takes no thread index, and the correction role's first state needs the warp index exactly
  (`%r1062` feeds the named barrier ids), so `Gate` needs the thread `g` (or the startup's
  `warpW L g`). The hand-off proof is then the output warp's, register by register, with
  `addi_sb` for the five barrier addresses and `batch_word` for `%r7277`.
- Not done (remaining steps, in order): `ret`/`stop_iff` (blocked as above); `Ref` with the count
  conjuncts of `Ref.lean` plus the positivity of the row sums and the payload kinds, `Expect`, and
  `ref_next` by `ref_cases`; the never-dropped theorem by `followed_of_sources` once the fragment
  is glued (it needs T1's `Role.correction`).

### Correction, round 3 (lane T2): ledger, reference invariant, lane L round 5

- Lane L is merged up to 1dbd83a1d (round 5: family mode, `shape_st`, the promoted
  `Lemmas/Flow/Step/ShapeTc.lean`). `Proof2/Lib/ShapeTc.lean` and `Proof2/Lib/ShapeBar.lean` are
  deleted (lane L promoted both); `Shape.lean` imports the library module and its hook no longer
  carries `shape_barSyncNR` and `shape_barArriveImm`, which `site_shape` now dispatches itself.
  The role's `macro_rules` (`sym_decide`, `lands_auto`, `shape_inv`, `shape_close`) are `scoped`
  (lane L's convention against shadowing between roles). One regression: `site_shape` now applies
  `shape_st` to the final stage's `st.shared.v4` stores, whose element source the symbolic
  sub-step `k` selects, so the side goal `srcs[k]? = some _` fails; the stores and the LSE stores
  are overrides (`corr_sst` in `ShapeFinal.lean`: `shape_store` without address or value, as the
  table states them). All 243 step families and the shape table build unchanged otherwise.
- Family mode (`families [.c i … => proof]`) is not used for the rescale and final chunk files.
  It routes a family to one proof with its fields whole, but every step proof here reads the
  instruction at the site's program counter (`rldPc st c`, `fldPc st j`), which is not a literal
  for symbolic `st`, `c`, `j`; a family proof would split the family itself, so the check time
  per site is the same.
- `bl` (the barrier at a shared offset) moved to `Base.lean`, so the shape table no longer
  imports the ledger and a change of the reference invariant does not rebuild the shape files.

Ledger (`Ledger.lean`, `Ref.lean`, task 1):
- The classes name a barrier by its shared offset (`Cnt.arrive o`, `Cnt.acquire o`; the barrier
  is `bl L g o`), the CTA barrier 2 (`bar2`), the lane's named barrier `k` (`nb k`, id
  `nbOf L g k`), and the stores (`st`, one per element). The shape table names a store's kind
  but not its address, so shared and global stores are one class; the Tensor Memory loads and
  stores are not counted (their number depends on the ballots, no closed form in the site).
- Closed forms (`RefQ`): a barrier class has its signal points (`ptsOf`; `sig` is the class of a
  site's event, `sig_pts` that the two agree). A state at site `s` with `r` rounds done has passed
  `passed pts s r`: the points before `s` in the current pass (the round's points before `s`
  when `s` is in a round; for a lane without a tile only the points before the request's reads
  and those of the end) plus `r` times a round's points. The stores: eight per final chunk, 256
  in all (`finalStores`), then `ℓ ≤ lseB s` LSE stores. The statements of round 2's `Ref.lean`
  had 32 stores per chunk and gave a lane without a tile none of the end's poll and barrier;
  both are corrected.
- Rounds: `loop` (in a round `r + 1 < B` and `%r6218 = r - B`, `B` the block count as a signed
  word), `tail` (from the final stage to the LSE all rounds are done: `r + 1 = B`, or `r = 0` and
  `B < 2`), `pre` (before the rounds and without a tile `r = 0`). The correction warps poll only
  in the final stage and at the end, once per tile, so their parities are constants of the site
  in the shape table; there is no per-round parity to state.
- Proof: the successors of every site are listed (`nexts`), and every listed move is checked
  once by evaluation (`moves_ok`, `decide +kernel`, a few seconds): its points (`pmove`; `rmove`
  at the end of a round), its regions, its stores, its sub-step and its row sums. `succ_cases`
  (`RefSucc*.lean`, one theorem per family) shows that every step stays (a failed poll), moves
  to the next element of a vector store, or moves to a listed successor with the frame facts;
  `ev_cls` (`RefEv.lean`) that an event of the shape table belongs to the class `sig` of its
  site;
  `counts_step` (`RefStep.lean`) combines them, with the entry and the end of a round by hand.
  Check times with `lean` (strict build, parallel): `Ref` 16 s (the evaluations), `RefSucc*`
  2 to 5 s per file, `RefEv` 6 s, `RefStep` 5 s. A first version of `succ_cases` took 475 s:
  `contradiction` in the branch splitter whnf'd the large successor terms and the real-number
  conditions of the LSE; the splitter now closes branches by `cases` only.
- No election in the correction warps: every lane fires every event, so `ElectSource` is not used.

Reference invariant (`RefNext.lean`, task 2):
- `Ref` = `RefCounts` and the row sums positive from their read to the LSE stores (`rsPos`);
  `Expect` = a 32-bit word at the scheduler's reads and shuffles and the request's reads (the
  bytes rebuild), a real `f32` payload at the scale and row-maximum reads, a positive one at the
  row-sum reads, and real `f32` payloads at the Tensor Memory loads. `ref_next`: under `Ref`, an
  expected event of the state's shape that is no undefined behaviour does not stop the counted
  machine and leads to a state satisfying `Ref` (as the MMA warp's `ref_next`; undefined
  behaviour is excluded by hypothesis until `ref_safe`).
- The positivity is the recorded deviation from M1: the machine stops at the final stage's last
  arrival unless both row sums are positive and at the first LSE store unless the second one is.
  Who discharges `Expect` at a row-sum read: the softmax warps' row sum of a row with a finite
  maximum is at least 1 (the term of the maximum element is `2^0`); this is the source obligation
  of the row-sum read, for the softmax fragment.
- Not proved: the death clause of `Fragment.OkAt.ref_next` (`next = none → Ends e`). Under
  `Expect` the reads rebuild, so the only death left is the tile count's division without a rule
  (`afterTiles`, `divOk`), which needs the scan's values (a non-zero divisor), the content facts
  of the scheduler that the MMA lane lists as well.
- `stepAt_counted`, `shape_counted`: the counted machine's steps and shape table. `ref_init`: the
  first state satisfies `Ref`. Check time of `RefNext.lean` 24 s.
- Remaining, in order: `stop_iff` and the never-dropped theorem wait for lane L (Core-rule
  stepping on special `f32` values and a Tensor Memory load return kind; lane L's status shows
  neither yet) and for lane T1's `Role.correction`; then `followed_of_sources` with `J := Ref`,
  whose source obligations are the launch-input reads, the warp collectives, the statistics reads
  (positive row sums from the softmax fragment) and the Tensor Memory loads (`TcLdDataflow`).

## Proof2: progress by ranked descent and safety without completion (task T4)

Lane T4 owns `Proof2/Progress/` and the library candidates it writes in `Proof2/Lib/`. It does not
edit `Proof2/Common`, `Startup`, `Epilogue`, `Mma` (lane T1) or `Correction`, `Loader`, `Softmax`
(lane T2); interface changes it needs from them are listed at the end of this section.

### The cycle and how it is broken

`Proof/Correct.lean` proves safety for a prefix `X` from completion: it extends `X` to a maximal
`Y` (`bounded_largest_extension`), proves that every lane of `Y` exits (`allLanesExitOfPre`, the
visit induction `RepeatedVisitInduction`, `ScheduledSingleVisitExit`, `ScheduledRepeatedExit`,
`OutputExitFromCorrection`, `IdleCtaExits`) and transports facts back. Five safety facts take the
completion premise today: the CuQ replay addresses of the loader, softmax and correction warps
(`Thread/LoaderFallbackWord`, `SoftmaxFallbackWord`, `CorrectionFallbackWord`, `…OfMaximal`), the
aligned-work agreement of the softmax warps (`Thread/SoftmaxBarrierRank`,
`noAlignedSoftmaxWorkMismatchOfExits`), the softmax tensor alignment
(`Thread/SoftmaxTensorAlignment`), and "no decoded fault" (`DecodedFault.contradictsExitsInExtension`:
a fault would stop a lane that every maximal extension makes exit).

In Proof2 the order is the plan's §4 and no step uses a later one:

1. Fragments, glue, ledger (`Proof2.thread p L g`, lanes T1/T2): no execution premise.
2. Per role, for every consistent execution, `Frame.followedOn` with the role's reference
   invariant (`Epilogue.good`, `Mma.good` on lane T1's branch, the other roles when they land):
   every state of a lane of the role is followed (`≠ some none`) and satisfies `Ref`. The step
   uses only `Consistent` and the sources (launch input, warp collectives, elections, protected
   reads); the order is `lexOrder μ` on the collectives up to an event. When all roles are glued,
   one `followedOn` with `Q g := g < L.threads` (the per-role steps combined; a lane's `Bad`
   depends only on its own `Ref`) gives `Frame.Tracked (thread p L) X`.
3. Safety facts, each from 2 and the shape tables, for every consistent execution:
   - no undefined-behaviour event: at a followed state the role's `ref_safe` (no shape of the site
     is `ub` under `Ref`), with `Frame.fired` and the shape table (plan G9);
   - CuQ replay addresses: `Ref`'s scan values (`Fits`) at the read sites, as `Reads.read_word`
     does for warp 13 (the launch-input source replaces the protected-CuQ premise);
   - aligned work, aligned tensor and barrier agreement: the warp-collective source applied to
     two lanes of one warp (positions of the warp's common sequence, `Position.lean`);
   - every other unsafe case of `Safety.unsafeCases` keeps its current proof, which takes only
     `Pre`, `Consistent` and the footprint.
   `SafeGoal` is their conjunction; no fact refers to `Maximal`, `Complete` or an extension.
4. `ProgressGoal` by ranked descent, taking `SafeGoal` (as FA4, `Progress/Assembly.lean`):
   `Descent.progress_of_steps` with `Sched.rank (timed p L)`; every open obligation steps.
   `Maximal` appears only here.
5. `ResultGoal`: a complete execution has every thread at its exit (`FrameEnd`); the stored values
   are the `Ref` facts at the store sites.

### The time table (rank)

`Proof2/Progress/Time.lean` gives `timed p L : Sched.Timed kernel Assumptions.all L` with
`code := thread p L` (the glued, counted machine, so a time may read the ghost counts) and a time
for every state. A CTA runs one tile (the scheduler's second pass finds no further tile), so the
schedule is one timeline per CTA, phase-major:

| Phase | Times | States |
|---|---|---|
| startup | `startTime s < 64`, by the startup's program order (`sh j`, `elect j`, `init n`, `fence`, `bar`) | every thread's startup |
| first scan | `scanBase + 2 c - [not a collective]` | every scanning role; `c` the warp collectives so far (ghost `shfl + vote`) |
| pipeline | `clk r o = pipeBase p + span (r + 1) + o` | slot `r` = K/V block, offset `o` from the per-round table below |
| tail | `tailBase p + o` with `tailBase p = clk (bmax p + 1) 0` | the output warp's ready/store/commit/drain/free; the correction's final stages |
| second scan, end | `endBase p + 2 c - [not a collective]` | every role's second pass, the end sites |

`bmax p` bounds every tile's K/V blocks (from the largest `kLength`), `cmax p` every first-scan
collective count, so the phases do not overlap. Within a warp the scan times are a collective
schedule (`Sched.CollSched`, key = the CTA): the `n`-th collective of pass 1 is at
`scanBase + 2 n`, of pass 2 at `endBase + 2 n`; the pass of `n` is fixed by the CTA
(`PassStart` is unique, `PassStart.unique`), so the schedule is a function of the key and `n`.

Per-round offsets (slot `r`; a wait's blockers sit at a smaller `(slot, offset)`):

| Offset | Role | Event | Waits on |
|---:|---|---|---|
| 0 | loader | K_r copy issue | ring-empty of index `2r` (released at slot `r - 2` or earlier by the MMA commit of index `2r - 3`) |
| 1 | loader | V_r copy issue | ring-empty of index `2r + 1` |
| 2, 3 | MMA | QK_r stages 0, 1 and their commits | Q (slot 0), K_r full (offset 0) |
| 4, 5 | softmax | stage 0, 1 of block `r`, P publication | S full (MMA commit, offsets 2, 3), the correction's credit of block `r - 1` |
| 6 | correction | rescale of block `r` | statistics barrier with softmax (offsets 4, 5), O full of block `r - 1` |
| 7, 8 | MMA | PV_r stages 0, 1, ring releases | V_r full (offset 1), P halves (offsets 4, 5) |

The MMA warp's program order interleaves PV_r with QK_{r+1} (`Mma/Machine.lean`), which the
table orders by slot: PV_r at `(r, 7)` before QK_{r+1} at `(r + 1, 2)`. The offsets of the loader,
softmax and correction rows are this lane's reading of the code and the old tree's protocol files
(`LoaderReadyOrder`, `SoftmaxCreditPhase`, `CorrectionStatsSync`); lane T2 confirms them against its
fragments' polls and arrivals when it adds the roles' time cases (only the inequalities "blocker
before waiter" are used, so the offsets may move).

Roles not yet migrated get time 0 at their stub state (it only appears before the stub's first
event). The time of a new role is a new case of `roleTime`; nothing else changes.

### The wait classes and their library instances

Event kinds in the code (counted on the PTX): 48 mbarrier polls, 370 shuffles, 61 elections,
12 ballots, 3 `bar.warp.sync`, 13 `bar.sync` and 6 `bar.arrive`, 5 `setmaxnreg`, the paired
`tcgen05.alloc`/`relinquish_alloc_permit`/`dealloc`, 60 `tcgen05.ld`, 28 `tcgen05.st` and 40
`tcgen05.wait`, 2 `cp.async.bulk.wait_group.read`, 6 `cp.async.mbarrier.arrive`, no cluster
barrier and no CLC request.

| Class | Library | tml-fa4 instances | Blockers |
|---|---|---|---|
| mbarrier poll | `Sched.pollBlocked_of`, `blk_of_lags`, `mbar_at_steps` | every role | per barrier family: its producer role's lanes before their arrival (unit hand-offs and the K/V ring, `RingDecl` single-CTA with `copies = 2` per item, and the Q stages) |
| warp collective | `Sched.no_ahead`, `coll_batch`, `CollSched`/`lag_of_sched` | scan shuffles and ballots of every role, pipeline broadcasts and elections of the MMA warp, the startup's shuffles and warp 0's elections | lanes of the same warp with fewer collectives |
| `bar.sync`/`bar.arrive` | `Sched.bar_sync_steps`, `bar_arrive_steps` with `NamedBar.Shape`/`Sources` | CTA barrier 0 (pc 173, every warp), barrier 2 (416: softmax, correction, MMA), the statistics barriers `3 + w` (softmax warp `w`, correction warp `8 + w % 4`), the softmax 128-thread barriers | participant lanes with fewer arrivals on the barrier |
| `setmaxnreg` | `Sched.released_of_reg` and the warp class | one per role | lanes of the warp |
| Tensor Memory resource | `Blocked.tmemWait_cases` (`TmemOpen`, `PublishWait`) | the MMA warp's allocation, relinquish, deallocation | the MMA warp's lane 0 (address store); the deallocation waits for the other roles' last Tensor Memory access through barrier 2 |
| warp-collective `tcgen05` | `Sched.tc_steps` (`TcWaitFacts`) | softmax and correction loads, stores, waits | lanes of the warp |
| bulk-group wait | performed when released; blocked only on the store obligation (rank 0) | the output warp's two read waits | the tensor stores |
| asynchronous obligations | FA4's `commit_steps`, `tensor_steps`, `store_steps`, `mma_steps`; `cp.async` arrive-ons | MMA commits, loader TMA copies and `cp.async` packets, output tensor stores | sources from the protocols |
| cluster start | not used | tml-fa4 launches clusters of one CTA and issues no cluster barrier | — |

### What each new piece replaces in `Proof/`

- `Proof2/Progress/Time.lean`, the assembly and the per-class instances replace the visit
  induction and the per-role walks to the exit: `Proof/Progress/*` (all 101 files, 9.7k lines,
  including `Opening*` and `Repeated*`), `Termination.lean`'s use in safety, and the
  `*Progress` files of `Proof/Thread/` (141 files, 22.3k lines).
- Output warp (`Proof2/Progress/Output*.lean`): `Thread/Output*Progress`, `Thread/Epilogue*Progress`,
  `IdleOutputFree`, `OutputMetadataReads`, `OutputFrame`, `EpiloguePrefixBound`,
  `NonzeroRoleCounts`, `Progress/IdleCtaExits`, `OutputRoleExit`, `OutputWriteback`,
  `OutputExitFromCorrection` (19 files, 3.25k lines).
- MMA warp: `Progress/MmaAllocationExit`, `MmaIterationWalk`, `MmaRecurringNotifications` and the
  MMA cursors of `Thread/` (`MmaTerminalOutputProgress`, `MmaTailPvProgress`, `MmaWaitCursor`, …).
- Startup: `Prologue*Progress`, `PrologueWarp0Rounds`, `PrologueGroupProgress`.
- Safety without completion (step 3 above): `Thread/LoaderFallbackWord`, `SoftmaxFallbackWord`,
  `CorrectionFallbackWord`, `SoftmaxBarrierRank`, `SoftmaxTensorAlignment` and the fault
  transport in `Safety/`.

### Decisions

- Stubs as premises. A role that is a stub cannot be followed past its first event, so the
  assembly (every pending thread steps) needs all fragments. The pieces of this task take the
  facts of unmigrated roles as premises of named structures (`…Lag`), each stated in the library's
  vocabulary (`Sched.Lags`, `Sched.threadTime (timed p L)`), to be proved by the role's lane.
- The base was origin/main until round 2; round 2 merged `ps-merge15` (lane T1's MMA warp
  followed, the warp-generic startup facts, the glued correction fragment).
- The time reads the ghost counts of the thread machine; no new state field is needed for the
  output warp. The MMA warp's times read its `Site.ord` places and its round (`RefQ`).

### Implemented (step 2)

All in `Proof2/Progress/` and `Proof2/Lib/`, for every consistent execution, from `Pre` only (no
completion premise, no `Maximal` except in `drain_steps`, which is a descent step):

- `Time.lean`: the phases (`scanBase`, `pipeBase`, `clk`, `tailBase`, `endBase`, bounds `bmax`,
  `cmax`), the startup's times (`startTime`, the site's pc), the output warp's (`Out.time`: the
  scans by the ghost collective count, the tail by site), `roleTime` (other roles 0 until their
  tables land) and `timed p L : Sched.Timed`.
- `OutputPoll.lean`: a lane of warp 13 at the ready poll of stage `st` polls `readyLoc st` next
  with parity 0 and no successful poll so far (`ready_pollsOn`, from `Epilogue.fits`, the ledger
  and the shape table); with the premise `ReadyLag` it has an earlier blocker
  (`ready_pollBlocked`) and is an `MbarAt` below its time, its time at least 2 (`ready_mbarAt`),
  which are `Sched.mbar_at_steps`' premises.
- `OutputColl.lean`: the warp collectives of warp 13 are a collective schedule of the time table
  (`out_collSched`, key the CTA, `outSched`: startup shuffles at their pcs, first scan at
  `scanBase + 2 n`, second scan at `endBase + 2 n`, the pass fixed by the CTA's choice `Late`),
  hence the warp class's lag (`out_lag`). On warp 13 the warp collectives are the ghost-counted
  shuffles and full-mask ballots (`warpColl_eq`).
- `OutputDrain.lean`: a bulk-group wait that is not ready steps on the open store obligation
  (`drain_steps`), given that no linear bulk copy is issued (premise `hc`).
- `Lib/PollsOn.lean` (library candidate for lane L, target `Lemmas/Kernel/Progress/Poll.lean`):
  `Frame.pollsOn_of_shapeAt`, `pollsOn_of_shape`, the poll premise from the shapes of the state at
  the trace's end, for any sound machine family (FA4's `pollsOn_of_site` without FA4's machine).

At step 2 the MMA warp's instances, the startup's collectives of warps other than 13 and the CTA
barrier waited for lane T1's `Mma.good` and warp-generic startup facts; round 2 (below) writes
them.

### Measurement (step 3)

Import-graph scan of `Kernels/TmlFa4Fwd` at this commit: reachability from `Proof/Correct.lean`
with edges cut (lines are file line counts).

- `Proof/Correct.lean` reaches progress through five imports (`Progress/Async`, `IdleCtaExits`,
  `ScheduledSingleVisitExit`, `ScheduledRepeatedExit`, `OutputExitFromCorrection`); 430 files,
  62.4k lines, are reachable only through them. With the six completion-based safety files
  (`Termination` and the five `Thread/` files of "The cycle") also cut: 460 files, 67.3k lines,
  all in `Proof/`. By role (file name): Loader 117 files 21.3k, Mma 65 / 10.2k, Softmax 58 / 9.6k,
  Correction 68 / 9.3k, Repeated 39 / 4.8k, Opening 28 / 3.3k, Output 18 / 2.3k, Rescale 24 / 1.9k,
  other 43 / 4.5k. These go when `Correct.lean` takes progress from Proof2 (T5), whatever the
  state of the other old roles.
- `Proof/Progress/` is 101 files, 9.7k lines; `Proof/Thread/*Progress*` 141 files, 22.3k lines;
  605 theorems named `*OfMaximal` in 396 files.
- The warp-13 progress chain (`Thread/Output*Progress`, `Thread/Epilogue*Progress`,
  `IdleOutputFree`, `OutputMetadataReads`, `OutputFrame`, `EpiloguePrefixBound`,
  `NonzeroRoleCounts`, `Progress/IdleCtaExits`, `OutputRoleExit`, `OutputWriteback`,
  `OutputExitFromCorrection`) is 19 files, 3.25k lines. Cutting them frees 0.33k lines more, not
  the old Epilogue: its 54 reachable files (14.3k lines) are imported by 300 files outside it
  (`EpilogueCuts`, `EpiloguePrefixStartup` and `EpilogueWarpReady` are the cut and startup
  infrastructure of every old role; `Thread/Machine.lean` uses the old output machine). The old
  Epilogue goes with the old Loader, MMA, softmax and correction trees at T5.
- New so far: `Proof2/Progress/` 4 files, 0.76k lines; `Proof2/Lib/PollsOn.lean` 81 lines. They
  replace, for warp 13, the poll and collective parts of the 19-file chain; the walk to the exit
  (`OutputDrain*Progress`, `OutputWriteback*Progress`) has no counterpart: descent needs no walk.
- Projection: FA4's descent is 1.9k lines in `Progress/` plus the thread-layer facts it consumes;
  the plan's 8–12k for tml-fa4's progress stays the estimate.

### Implemented (round 2, after merging `ps-merge15`)

All in `Proof2/Progress/` and `Proof2/Lib/`, for every consistent execution, from `Pre` only:

- `Time.lean`: the MMA warp's time (`Mm.time`): a pipeline state at place `q = Site.ord` with `r`
  rounds done at `clk p s (2 q)`, slot `s = 0` for the first K/V block and `r + 1` for round `r`
  and the tail after `r` rounds (`Mm.pipeT`); the round is a function of the state (`Mm.round`,
  from the ghost broadcast count `v.ps = shAt q r`); the allocation prefix, the scheduler's passes
  and the end by the collectives so far, as the output warp. The correction warps' time
  (`Cr.time`): the final stage `st` at `tailBase + 8 st`, its ready arrival `fdone st 1` one
  later, the LSE stores at `tailBase + 17`, the passes by the collectives; the rescale rounds at
  `clk p 0 1`, a placeholder (decision: lane T2 replaces it with the per-round table of "The time
  table" once the rounds' `Ref` gives the round). Untimed roles and stubs sit at `scanBase`
  (was 0), after every startup state (`roleTime_ge`), which the CTA barrier's lag needs.
- `MmaPoll.lean`: at its fourteen polls (`wt k`, `mw b ld`) a lane of warp 12 polls the barrier
  `bl L g (pollO r s)` of its round with the parity of its successful polls (`par_eq` from
  `RefQ`: Q stages, the ring's slot and parity, the P parity; `mma_pollsOn`, `δ = 0`); the shape
  table allows a fault, which `poll_fires` excludes because every polled barrier is 8-byte aligned.
  With the premise `MmaFullLag` (a blocker when the phase has the poll's parity; the loader's case
  `fromLoader o`, the softmax warps' the other) the poll is an `MbarAt` below the lane's time
  (`mma_mbarAt`). Commits: the commit sites' times are `Mm.pipeT`, ordered as the program; the
  waiters' lag lemmas against them belong to the waiting roles' tables.
- `StartAll.lean`: every lane of every warp `w ≠ 0` is followed through its startup into its
  role's first state, migrated or stub (`start_good`, invariant `SRef`; the induction stays in
  the startup because a position after the barrier has three collectives). From it: a lane before
  the CTA barrier has not exited and is at most 174 (`bar_before`), so `bar0_lag` is the lag
  premise of `Sched.bar_sync_steps` for a waiter at the startup barrier, with warp 0 as the
  premise `Warp0Lag`; and a lane with at most `j < 3` collectives is no later than the `j`-th
  startup shuffle (`start_coll_lag`).
- `Ready.lean`: `ReadyLag` follows from `ReadyArrive` (`readyLag_of`), which names no time: the
  ready barrier has a state, and while its phase is even some correction lane of the CTA has not
  exited and is at a startup state or at a correction state at or before `fdone st 1`
  (`preReady st`) with at most `cmax p` collectives (`CorrPre`). The time half is `corr_before`.
- `Lib/WaitReg.lean` (library candidate for lane L, target `Lemmas/Flow/Step/ShapeRegs.lean`):
  `fires_wait_reg_al`, `fires_wait_reg` keeping the misalignment of the fault case.

Decisions:

- The correction ledger's closed forms and `Ref`/`ref_next` (c88dd0370, 05b790ffa) arrive with
  the second merge of `ps-merge15` (791fe9844); they are stated on the correction's own counted
  machine, so they reach the thread frame only with `Correction.good` (lane T1, in progress). `ReadyArrive` is stated so that
  `Correction.good`, the ledger's arrival count at `fdone st 1` and the ready barriers' unit
  hand-off discharge it without touching a time.
- `MmaFullLag` is stated with `Sched.Blk` rather than `Sched.Lags`: the Q and K/V barriers
  complete by the TMA copy's transaction count, so their blocker may be the open copy obligation,
  not a lagging lane.

Lines: round 2 adds 970 lines (`MmaPoll` 313, `StartAll` 378, `Ready` 115, `Time` +122,
`Lib/WaitReg` 42); `Proof2/Progress` and `Proof2/Lib` are 1.81k lines in total. Deletable at T5,
once `Correct.lean` takes progress from Proof2: with the MMA polls, `Proof/Progress/Mma*` (3
files, 177 lines), `FirstRecurringMma`, `SingleVisitMmaRetire` (132) and the 17
`Proof/Thread/Mma*Progress*` files (2.70k); with the startup and the CTA barrier,
`Proof/PrologueBarrierRelease` and `Proof/Thread/Prologue` (156); with the correction's tail
times and `ReadyArrive`, `Progress/OutputExitFromCorrection` (50) and, when the correction's own
waits are added, the 11 `Proof/Progress/*Correction*` files (1.22k) and 18
`Proof/Thread/Correction*Progress*` files (2.14k). These are within the 62.4k lines measured in
step 3; nothing in `Proof/` is deletable before T5, since `Correct.lean` still imports it.

### Remaining, by the fragment it waits for

| Piece | Waits for |
|---|---|
| `ReadyArrive` (ready barriers' hand-off, correction lanes followed and at `preReady`) | `Correction.good` on the thread frame (lane T1), the correction ledger's arrival counts (lane T2, `tmlfa4-corr-proof2`), the unit hand-off declaration (T3) |
| `MmaFullLag`, loader case (Q stages 0/8, K/V full 32/40/48) | loader fragment (lane T2): loader times, TMA copy obligations, `RingDecl` single-CTA instance |
| `MmaFullLag`, softmax case (P halves 96/104/112/120) | softmax fragment (lane T2) |
| commits as producers (ring-empty, S-full, O-full, Q-free waits) | the waiting roles' times (loader, softmax, correction); MMA side done (`Mm.pipeT`) |
| correction's own waits (statistics and named barriers, O-full, Q-free, free polls, `wend`) and the rescale rounds' times | correction `Ref` round index on the thread frame (lane T2/T1) |
| MMA collective schedule (scan, pipeline broadcasts, elections), barrier 2, Tensor Memory allocation and deallocation | the softmax and correction fragments (barrier 2's participants); MMA side's facts are in `Mma.good` |
| `Warp0Lag` (warp 0 before the CTA barrier), warp 0's elections | `StartAt` for warp 0's path (elections, barrier initialization) — interface request to lane T1 for `Proof2/Common/Frame.lean` |
| loader times, ring-empty polls, `cp.async` arrive-ons, `hc` of `drain_steps` | loader fragment (lane T2) |
| softmax times, S-full and credit polls, the 128-thread and statistics barriers, `tcgen05` waits | softmax fragment (lane T2) |
| warp-collective class for every warp (`Sched.WarpRec`, `no_ahead`, `coll_batch`) and the assembly (`obl_steps`, `Tracked`) | every fragment: the library's lemmas quantify over all threads |
| `SafeGoal` without completion | every fragment's `Ref` and `ref_safe` |

Interface requests: to lane T1, `StartAt` (or a warp-0 analogue) for warp 0's startup path in
`Proof2/Common/Frame.lean`, and `Correction.good` stating, at the end of a trace, the correction
lane's site and its first-pass collective bound (what `CorrPre` reads). No request to the Mma or
Epilogue directories.

## Proof2: the softmax warps as a site machine

`Proof2/Softmax/Machine.lean` is a `Flow.Code` machine for warps 0 to 7 from their
`setmaxnreg` (pc 3102, lane T1's entry of the role) to the `ret` (pc 9205): 142 event sites,
with the elements of the sixteen bias vector loads of a biased round at sub-steps 1 to 3, the
implicit waits of the plain rounds' score loads (`tcLdDataflow`) at sub-step 1, and the stores
after the implicit waits of the first P stores of the first and the biased rounds
(`delayedTmem`) at sub-step 1.

- **Control registers only.** The machine's facts name the registers live at a state that are
  not data registers (`Live.lean`, `ctlLive pc = (Flow.live pc).filter ctl`). The data registers
  (`dataRanges`, 4650 ids) are the closure of the score and bias loads' destinations under the
  role's floating instructions, conversions and moves. No branch, guard or event other than a
  store reads a data register (checked on the PTX when the ranges were computed), so the control
  flow and every event's control operands are stated in full; what the stores and Tensor Memory
  stores write is not stated. Facts are a choice of the machine, so stating fewer registers is
  sound: a state's concrete states are those whose control registers have the table's values.
  The segment tactics read the live function of the facts at every program counter they walk
  (`liveFn` in `seg_sym`), so the filter is a function of the program counter, not a list per
  site.
- Consequence: the 63 sites whose following local code reads a data register (the score and bias
  loads' unpacking, the maximum and exponent segments, the P packs before the stores and the
  row sums after the closing poll) cannot be stepped by `seg_sym` from these facts; they need
  the data plane in the table (or, per segment, the old tree's local-run lemmas restated as
  `Seg` pieces). The other 79 sites are control sites and are stepped by `site_cases`.
- The data plane is still followed (rule M1): the score loads record their 32 values per load
  (`sv`) and the bias loads their four words per load (`bv`) whatever they are (rule M4); bytes
  that do not rebuild into a value fault the thread (`none`), as `step_ldv_mid`/`step_ldv_last`
  require.
- The first pass's scan compares with `%r12` (`ctaW`, as the MMA warp); the second pass reads
  `%ctaid.x` itself (pc 7659), so its CTA term is `ctaR` under the explicit-parameter launch, as
  in the correction warps; `ctaR_eq` and the `sym_decide` rule `ctaR_succ_le` decide its loop
  exit test.
- The machine has no `ent` argument (lane T1's interface): the registers live at pc 3102 that
  the role never writes are in `valuesStart` with their startup values, `%r6187` with the batch
  word the dispatch loaded.
- **Steps by `site_cases`** (`Steps*.lean`, role tactic `soft_sites`): the start, both
  scheduler passes, the choice of the request, the request's reads, the control sites of the
  three round kinds (polls, fences, the P stores after the first two, store waits, warp barrier,
  election, the elected lane's arrival, the statistics stores; the Tensor Memory stores by the
  override `soft_tst`), the final stores and the end: 79 event sites, 4 of them (`pst _ 2`,
  `pst _ 3` per round kind) overrides. Check times (strict build, files in parallel, process
  start included): start 9 s (2 sites), first pass 98 s and 129 s (8 + 8 sites), second pass
  139 s and 154 s (8 + 8), choice about 270 s (3 sites; the tile count's segment runs the
  coordinates, both divisions and the 16 bias addresses and lands in three branches, most of the
  time), request 33 s (3), first round 46 s (11), biased rounds 85 s (11), plain rounds 38 s (9),
  final stores 10 s (3), end 24 s (9 states). Risk R2: the scan families are 12 to 19 s per site and the choice
  about 90 s per site, above the 15 s rule; no site exceeds five minutes. Recorded, not changed.
- Three decision rules: the Epilogue's `cta_succ_le` for the first pass, `ctaR_succ_le` for the
  second, `warp_ne8` (a softmax warp, index below eight, does not take the correction warps' path
  at pc 7744; the end's theorem takes `g % L.block / 32 < 8`, which the hand-off gives). The two
  role rules are tried `with_reducible`: an `exact` of the second pass's rule on a first-pass goal
  otherwise unfolds `explicitParams` and exhausts the heartbeats, which `sym_decide` does not
  catch, and the walk unrolled the loop (the error named the predicate at pc 3162).
- `soft_sites` builds its simp list as an array: a quoted `[… tlOf, $us,*]` with an empty `$us`
  gives a malformed simp argument, `next_simp`'s `try simp only` then silently does nothing, and
  every load or `if` successor fails with an unsolved `succ … = ?nv v`. The correction lane's
  uncommitted `corr_sites … using […]` has the same form.
- `soft_tst` (a Tensor Memory store that no assumption makes wait) is hygienic: the named hole
  `?dn` of a non-hygienic macro is shared by all sites of a `site_cases` call, so the second
  store got the first one's successor (the correction lane's `corr_rld`/`corr_fld` problem).
- The stage-dependent words follow the code's own terms: `selp.b16 1, 0` then `mul.wide.u16 … 8`
  gives `sel16`, and `sbS` is the shared base plus `(sel16 stg).toNat * 8`, so the tables close by
  `rfl`.
- `Ledger.lean` (`Code.counted`: arrivals, successful polls, CTA-barrier arrivals per id, Tensor
  Memory loads and stores, shared stores, shuffles, ballots, won elections) and `Ref.lean`
  (statements, risk R1): the rounds are closed forms in the rounds done `j` (`r169 - r299`
  biased rounds, `min r169 r299` plain rounds, counters and the three parities `j mod 2`), and
  every count is the start's points plus `roundsCount` of the rounds done plus the current
  round's points before the state; the elected lane's P-ready arrivals are its won elections.
  198 lines; no proof yet.

- Lane-L round 6 merged (with origin/main's MMA, startup and output-warp fragments). The scan
  state `Epilogue.D` lost its collective counters `ns`/`nv` (the ghost ledger counts shuffles and
  ballots), so the softmax machine no longer updates them and `RefCounts.coll` is dropped; the
  collective counts are the ledger's `Cnt.shfl`/`Cnt.vote` classes. The role's `sym_decide` and
  `lands_auto` rules are `scoped` (lane L's convention). `Proof2/Lib/TcSteps.lean` (promoted to
  `Lemmas/Flow/Step/TcSteps.lean`) is deleted; the correction warps' `Base.lean` imports the
  library file and their machine drops `ns`/`nv` the same way (a minimal fix to keep this branch's
  copy of `Proof2/Correction` building; the correction lane's branch has its own).
  The merge also kept two files of an older MMA snapshot of this branch that origin/main no
  longer has (`Proof2/Mma/Thread.lean`, `Proof2/Mma/Dispatch.lean`; their declarations now live
  in main's `Proof2/Mma/Startup.lean` and clash with it); they are deleted, so `Proof2/Mma` is
  main's tree.

- **Sub-steps that stay at their instruction** (`StepsMid.lean`, 41 s): the first three
  elements of each of the 32 bias loads (96 states, `step_ldv_mid_sel` through `site_cases`, no
  override), the implicit wait of the first P store of the first and the biased rounds (lane L's
  `step_tcStWait`, override `soft_tstw`), and the four score loads of a plain round at sub-step 0
  (`step_tcLdLoad`, override `soft_sldp`: the destinations are data registers, so the facts at the
  implicit wait are the control registers live after the load, which the load does not write:
  `Proof2/Lib/SetRegsFrame.lean`, `holds_setRegs_frame`, for promotion). The invariant's midway
  part now names the accumulator per site (`Site.midOk s k acc`: a bias load holds one value per
  element read, the implicit waits hold none), as `step_tcStWait` and `step_tcLdLoad` require.
  The last element of a bias load, the implicit wait of a plain score load and the delayed P store
  at sub-step 1 continue into local code that reads data registers: they are numeric sites.

- **Shape table** (`Shape.lean`, `Shape{Ctl,Scan,Tc}.lean`, `Shapes.lean`: `shape`, every event a
  state fires has the state's shape `Ev`), by `site_shape` at every family; overrides: the
  statistics and final shared stores (`soft_st`: `shape_st` names the stored value, a data
  register no fact names, so the store is stated as a write or undefined behaviour without
  address or value). Polls name the stage's barrier `bl L g o` (shared base, plus 8 in the second
  stage, plus the site's offset) and the parity `(truncBits 32 w).toNat % 2` of the site's
  parity word; arrivals the stage's barrier and one unit; the named barriers their ids (`nbW`, 11
  or 12 by stage, 2); Tensor Memory loads, stores and the bias reads are stated by kind (their
  addresses come with their sources). Kernel-side library lemmas for promotion:
  `Proof2/Lib/ShapeTcWait.lean` (`shape_tcStWait`, `shape_tcStStore` for the delayed P store's two
  sub-steps, `shape_barArriveR` for `bar.arrive` with a register id). The table needs the facts of
  a plain load's implicit wait at sub-step 0 to be those before the load (`livePc` depends on the
  sub-step), so that the address register reads there. Check times (strict build, files in
  parallel): `ShapeCtl` 1532 s (61 control sites, about 25 s per site), `ShapeTc` 402 s (28
  score-load and P-store sites), `ShapeBld` 242 s (32 bias loads at every sub-step),
  `ShapeTcWait` 157 s (6), `ShapeScan` 168 s (28 scheduler sites), `Ref.lean` 31 s. Risk R2: the
  control sites are above the 15 s rule (each evaluates the role's value table through
  `site_read` and the address tactic); recorded, not changed.
- **Ledger and counts** (`Ledger.lean`, `Ref.lean`): the ledger's classes are by barrier offset
  (`Cnt.arrive o`, `Cnt.acquire o`) and by named barrier kind (`bar2`, `nb`, `sb`), so that a
  class's points are a function of the site. `RefQ` states the counts as places (the correction
  warps' method): a state's position is twice its pc (plus one at a plain load's implicit wait),
  a class's points are the positions of the sites of its class (`ptsOf`, computed from the site
  list), the points of a biased round count once per biased round done (`rb`), those of a plain
  round once per plain round done (`rp`); a lane without a tile passes none between the request's
  reads and the final poll; the bias-slot arrival (offset 336) is lane 0's only (`lz`); the
  elected lane's P-ready arrivals (offset 112) equal its won elections (`elect`). Parities:
  `(1 + rb) mod 2` in a biased round, `(1 + rb + rp) mod 2` in a plain round and after the rounds,
  1 on a lane without a tile. Checked by evaluation: every move between listed successors
  (`moves_ok`), the class of every site against its points (`sig_pts_all`); proved:
  `passed_move`, `passed_rmoveB`/`passed_rmoveP` (a round's end), `sig_pts`, `refCounts_init`.
  Not proved yet: the step (`counts_step`, `ref_next`): it needs the successor analysis
  (`succ_cases`, as the correction warps' `RefSucc*.lean`) and the frame of the parity words.
  Not stated: the closed forms of the round counters `%r6188`/`%r6194` and the bounds
  `rb ≤ nBias`, `rp ≤ nPlain` (the exit tests on 32-bit words, as the correction warps' `loop`).
- **Row sums for the correction warps** (`RowSumPos`, `Ref.lean`): every event a lane fires at its
  row-sum store (`fin 0`, offset 368, read by the correction warps at pcs 8466 and 8762) writes a
  positive `f32` real. It is stated as the softmax fragment's named obligation, not proved: the
  machine's facts do not name the data plane, so the stored register has no value in the table.
  Its proof follows the numeric steps (a row with a finite maximum has a row sum of at least 1).

- **Merge of `ps-merge17`** (main acf2c9865 with lane T1's d826f6cf4, which includes lane L
  round 6, edc9fd0d7): everything outside `Proof2/Softmax` and this lane's `Proof2/Lib` files is
  `ps-merge17`'s side. None of this lane's `Proof2/Lib` lemmas (`holds_setRegs_frame`,
  `shape_tcStWait`, `shape_tcStStore`, `shape_barArriveR`) is in `Lemmas/` yet, so both files
  stay. Lane L has no commit after edc9fd0d7 (round 7 not posted), so its merge is the one inside
  `ps-merge17`. Full strict build of the merge: 9846 jobs, rc 0.

- **Successor and class cases of the count step** (the correction warps' method, files
  `RefSucc*.lean`, `RefCases.lean`, `RefEv.lean`). `succ_cases`: every step stays at its site with
  its values and fires no event of a ledger class (a failed poll, an element of a bias load before
  the last, the implicit wait of a delayed P store), or moves to a listed successor (`nexts`) with
  the step facts `MoveFacts`: the sub-step, no failed poll, the delayed store past its wait, the
  frames of the parities and counters (landing in a round or after the rounds) and of the scan
  and used-K length (landing in a round or at the final stores) for a site that does not end a
  round, the parity of a lane without a tile, and the election's outcome. One theorem per family
  (four files, 4 to 21 s each with `lean`); the ends of the rounds (`pwend`) by `pwend_move`,
  which splits the nested conditionals with `ite_P` instead of `split at h` (`split` on the
  rounds' conditions, terms of `%r169`, `%r299`, `%r431`, reaches the maximum recursion depth).
  No `contradiction` on large terms. `ev_cls`: an event of the shape table that is no undefined
  behaviour, no failed poll and no delayed wait belongs to its site's class among the pointed
  classes and the elected lane's arrival (`Pre` gives the named barrier `nbW` in 3 to 10);
  `ev_won`, `ev_won_pel`: the won elections change only at the election.
- Two statement changes this needed, inside this lane's files: the shape of a plain load's
  implicit wait depends on the sub-step (`if d.k.val == 1 then` the wait or a fault `else` a load),
  so that the wait at sub-step 1 has no ledger class (`soft_shape` unfolds with `Nat.reduceMod`,
  `Nat.reduceBEq`, `ite_true`, `ite_false`); and the ledger's store class `sst` counts every store
  (the role stores to shared memory only, and its shape table states the stores without their
  addresses, so a class on the address space could not be decided from the table).
- **Round counters in closed form, with bounds** (stated in `RefQ.bias`, `.plain`, `.fin`): `nB`,
  `nP` are the two's complement values of `%r169 - %r299` and `%r431`, which the code compares
  with 1. In a biased round `rb < nB` and `%r6188 = rb - nB - 1`; in a plain round `rp < nP`,
  `%r6194 = rp - nP` and the biased rounds are done (`Done rb nB`: `rb = nB`, or none when
  `nB < 1`); at the final stores both kinds are done. `regOk` also keeps the final stores' region
  (`finR`) closed, and no longer admits entering the region before the rounds from an end state
  without a tile (every such move starts before the rounds; `moves_ok` checks it). The exit tests
  on 32-bit words decide `rb + 1 = nB` and `rp + 1 = nP` within one period:
  `Proof2/Lib/Counter32.lean` (`i32_addi`, `ne_m1`, `ne_0`, `scmpi_lt1`, `neg_eq`, `sub32_swap`,
  `xor_par`), for promotion; the correction and MMA warps have private copies of the first two.
  `sub32_swap` is proved through `trunc_toNat`, `sub32_toNat`, `addm1_toNat`, `i32_toNat`: a direct
  `omega` on the `toNat` forms hits the kernel's recursion limit (seen nondeterministically, 5 min).
- **`counts_step` and `ref_next`** (`RefStep.lean`, `RefNext.lean`). The generic parts (`cnt_move`,
  `elect_move`, `bump_stay`, `refq_stay`, `moveOk_pmove`, the move inside a region) follow the
  correction warps' `RefStep`. The three ends of a round (`refq_first`, `refq_bias`,
  `refq_plain`) close by evaluation on the site table: the round counts are restated as functions
  of the scan and the used-K length (`nBt`, `nPt`, with `nB_t`, `nP_t`), so that the counts of a
  successor's values, a structure update of the state's values, reduce to the state's by
  projection (`simp only [nB_t]`); the region conjuncts of a successor are closed after
  `dsimp only` (`not_in`, `no_wait`), which removes the state's free fields from the goal before
  `decide`; the parity words are the flipped words of `par_flip`, rewritten to the next round
  count before the structure is built; the exit tests are rewritten by `lt1_nB`, `lt1_nP` and the
  counter step (`c1`) inside the unfolded successor, with no `let`. `ref_next` (the correction
  warps' form): under `Ref` (the count conjuncts) and `Expect` (a 32-bit word at the scheduler's
  and the request's reads and shuffles), an event of the state's shape that is no undefined
  behaviour does not stop the counted machine and leads to a state satisfying `Ref`. Check times
  (`lean`, loaded host): `RefStep` 5 s, `RefNext` 34 s.
  Not covered: the `ref_next` conjunct of `Fragment.OkAt` that a `none` successor ends the thread
  (the bias loads' bytes that do not rebuild and a division without a rule give `none`; `Expect`
  and `Ref` do not exclude them yet), and `ref_safe`.

- **`ShapeCtl` split** (risk R2): eight files by family (`ShapeCtl1` … `ShapeCtl8`) that check in
  parallel; `ShapeCtl.lean` combines them. With `lean`, file by file on the loaded host: start and
  request 48 s (6 sites), polls, fences and barriers 68 s (11), statistics stores 25 s (2), P part
  119 s (12), closing polls and final stores 55 s (5), store waits 70 s (6), the end 530 s (7), and
  the three arrivals at the correction warps' named barrier (`narr`, `ShapeCtl6`) 1409 s: the
  previous single file's cost was these three sites (about 470 s each: the barrier id `nbW` is
  read through the role's value table and the address tactic). The wall time of the family is now
  that one file; cutting `narr` further needs the id as a table fact in closed form (`nbW_tval`
  evaluated once per stage), recorded as the next step for R2.

- **Merge of lane L round 7** (lane-L 7bdc0a125: multi-destination side-split steps for the
  unpack `mov.b64 {a, b}`, a source for a thread's own local-memory reads). Lane L promoted
  `holds_setRegs_frame` to `Lemmas/Flow/Step/TcSteps.lean`; this lane's copy
  `Proof2/Lib/SetRegsFrame.lean` is deleted and `Base.lean` imports the library file. Lane L
  measured, from this branch's code, the masked maximum (pcs 3872 to 4397, 605 s, 26 GB, one call)
  and the exponent stretch (pcs 4399 to 4826, 1622 s, 27 GB); not covered there: the `neg.f32` of
  the scale word at pc 4398 and restating the maximum's end facts as the exponent's start facts.
  Round 7 also promoted lane T1's `Proof2/Lib/WaitReg.lean` (`fires_wait_reg_al`, now in
  `Lemmas/Flow/Step/ShapeRegs.lean`) and `Proof2/Lib/PollsOn.lean` (now
  `Lemmas/Kernel/Progress/PollsOn.lean`); the copies clash with the library, so this merge deletes
  them and `Progress/MmaPoll.lean`, `Progress/OutputPoll.lean` import the library modules (the
  minimal change outside this lane's directory for the merge to build; lane T1's branch does the
  same when it takes round 7).

- **Hand-off** (`Handoff.lean`): the fragment is `code p L g` (no `ent`); its first state's facts
  are the 13 registers live at pc 3102, all control registers (`facts_init`); `handoff hp hg hF`:
  a thread state holding `Startup.facts p L g ⟨.enter .softmax, ofNat sharedBase, x2,
  ofNat (g % L.block / 32)⟩` holds them (local copies of `addi_sb`, `cta_word`, `batch_word`).
  What lane T1 adds in `Proof2/Common` (not done here):
  - `Roles.lean`: `Role.softmax` with `frag p L g .softmax := if g % L.block / 32 < 8 then
    Softmax.code p L g else stop L g 3102` (the steps of the end take `g % L.block / 32 < 8`, a
    fact about `g`, so the fragment carries it), the gate `Gate L g .softmax d := decide (g %
    L.block / 32 < 8) && d.x1 == ofNat sharedBase && d.x3 == ofNat (g % L.block / 32)` (the
    warp index below 8 is the dispatch's own test on `x3`), `roleOf .softmax := .softmax`, exit
    pc 9205 (`softmaxDecl` is already in `Roles.lean`), the ledger class `soft (c : Softmax.Cnt)`
    with `Softmax.cls`.
  - `Sound.lean`: the `handoff` case `.softmax`: from the gate, `⟨hpc, hs, ha, hf,
    Softmax.handoff hp hg hF⟩` and `inv` by `Or.inl ⟨rfl, rfl⟩`; `frag_steps` case `.softmax`
    needs `Softmax.stepAt` at every state, which waits for the 63 numeric sites.

- **The masked maximum** (`MaskSeg.lean`, `MaskW0` … `MaskW3`, `MaskFold.lean`), with lane L's
  opt-in `sym_selp_value` (scoped in `MaskSeg.lean`): one `Seg` per mask word from the mask count
  `m` (`%r2175`) and the word's 16 score pairs to its 32 conditional elements (pcs 3872, 3987,
  4101, 4215, 4329), and one for the `max.f32` tree from the 128 elements to the row maximum
  `%r6196 = erealValue .f32 (foldM m sc)` (pc 4395). The terms mirror the code (`mword`, `mkeep0`,
  `mdrop`, `mdrop31`, `mre`, `foldM`), so the walk's values close by `rfl`. Not yet connected to
  the machine: the role's facts do not name data registers, so these pieces are stated with
  explicit start facts (each word 48 to 52 s, the fold 21 s, strict build). Lane L round 7
  checks the same stretch in one call (605 s, 26 GB); the per-word split keeps each file small.
  Chaining them into the steps of `barr false`/`bsync false` needs the
  table's data plane and a frame of the facts the pieces do not mention.

- **Merge of `p4b-epilogue-wire`** (lane T1, d173a2acb: main with lane L round 7 and
  `Proof2/Top`): everything outside `Proof2/Softmax` and this lane's `Proof2/Lib` files is lane
  T1's side; the only conflict was this file (both sides appended sections; both kept). Full
  strict build of the merge: 9914 jobs, rc 0.

- **The masked maximum as one segment** (`MaskChain.lean`, `mask_max`): the pieces are restated so
  that each piece's end facts are the next piece's start facts: word `k`'s piece starts from the
  mask count, the constant `-1` (`%r3080`, from word 1 on), the elements selected by the words
  before it and the score pairs of words `k` to 3, and ends with the same facts one word on; the
  last word ends with the 128 elements only, the fold's start facts. `Seg.comp` then gives one
  segment from the mask count and the 64 score pairs (pc 3872) to the row maximum (pc 4395). The
  pieces carry more facts, so they take longer: strict build, files in parallel, words 0 to 3
  103 s, 143 s, 187 s, 232 s (11.5 GB for word 3 with `lean`), the fold 29 s, the chain 3 s.
- **The negated scale at pc 4398** (`NegScale.lean`, `neg_scale`; `scale_word` from `Pre`): Core's
  `neg.f32` of register 7132, which holds the word the role loaded from parameter 12
  (`.bits 32 (paramW p.scaleLog2Bits)`), proved by `Seg.writes` with Core's rule: Core classifies
  the word through its pattern, whose number `Pre.scales` gives (a positive finite `f32`), and
  writes `.float .f32 (-s)` to register 1230. Library candidate: `classify_word`
  (`Proof2/Lib/FloatWord.lean`: a word whose pattern has the finite nonzero `f32` number `s`
  classifies as `FVal.fin s`).
- **Why the exponent stretch is not walked yet** (blocked on the library, request to lane L).
  Lane L's run of pcs 4399 to 4826 started from register 7132 as `.float .f32 s`; in the role
  the register holds the parameter word `.bits 32 (paramW p.scaleLog2Bits)`, and pc 4402 packs it
  (`mov.b64 %rd738, {%r6072, %r6072}`) into the multiplier of all 64 `fma.rn.f32x2` of the
  stretch, so every packed `fma` reads the word through its pattern. `seg_sym` does not read a
  symbolic pattern (checked: the walk stops at the first such step, "does not evaluate" on
  `classify .f32 (.bits 32 (paramW S))`), and the plain and biased rounds read the same word
  (registers 7132, 7133). Request: `seg_sym` reads a register `.bits 32 w` as the float `s` when
  the context has `classify .f32 (.bits 32 w) = .ok (.fin s)` (`classify_word` gives it from
  `Pre`), at Core's float reads (`valFloat`, `classify`) and at the assumptions' real reads
  (`readERealOpnd`). Restating the table's entry as `.float .f32 s` would be false (the load
  writes the word), so this is not done in the role. The split of the stretch into files waits
  for that reading; the cuts are then at the boundaries lane L measured, pc 4594 (after the 64
  pack/`fma`/unpack triples) and pc 4626 (after the `ex2`s), with the probability packs (727 s in
  lane L's run) cut further, each piece's facts the live data registers at its cut, and the files
  checked one at a time (lane L: 27 GB for the whole stretch).
- **The bias unpacks** (after the last element of each bias load) read the bias words that the
  loader's copies of the input put in shared memory: `rebuild` gives a pair of two halves, each
  the `bf16` payload of an unmasked bias element or the bits of the masked one (`biasValue`), and
  `cvt.f32.bf16` reads them. The machine records the bias loads' values whatever they are; a step
  through the unpacks needs the values' form in `Expect` (from the protected-read source) and a
  return kind for it (`RetKind` has none for a pair of `bf16` values), recorded for lane L.
- **The data plane of the table is not started.** Every numeric step needs the facts of the data
  registers at the numeric sites and at the control sites between them (the score loads' values
  are live from their load to the masked maximum or the scaled scores, across the bias poll,
  the bias loads and the barriers; the row maximum and row sum across rounds, up to the final
  stores). The steps of those control sites then carry up to 128 more facts each, which raises
  the `site_cases` cost of risk R2. Decided: the data plane is added when the two library reads
  above exist, so that every numeric stretch can be walked once the facts are named; the score
  loads then record reals (`RetKind.real .f32` at `sld`, the machine stops on another kind as the
  correction warps do).

- **The invariant excludes a plain round's implicit wait at sub-step 0** (`Machine.lean`,
  `Site.first`): the machine enters `sldw` at sub-step 1 only (after the load), and at sub-step 0
  it stopped on every event, so `stop_iff` (which takes only the invariant) could not hold there.
  The invariant is now `(k = 0 ∧ acc = [] ∧ site.first) ∨ midOk`; the successors and the role's
  tactics are unchanged except `soft_inv` (`⟨rfl, rfl, rfl⟩`) and the two `junk` lemmas.
- **`stop_iff`** (`Stop.lean`, `ret`, by lane L's `stop_cases`): the machine stops exactly on a
  value that is not a 32-bit word at the scheduler's reads and shuffles and at the request's
  reads; every other site has `ret = .none` (the score and bias loads, the polls and the election
  record whatever they return). 28 s (strict build). When the data plane makes the score loads
  stop on a value that is not an `f32` real, `ret` at `sld` becomes `.real .f32`.
- **`stepAt_ctl`** (`Steps.lean`): the step obligation at every state that is not numeric
  (`D.numeric`, the 63 states listed there), assembled from the family files; a state its
  invariant excludes by `stepAt_junk`. For lane T1's `frag_steps`: `frag p L g .softmax` is
  `Softmax.code p L g` under `g % L.block / 32 < 8`, which `stepAt_ctl` takes (`hw`); the numeric
  states remain open.
- **`RowSumPos` is not proved.** Its statement reads the event at `fin 0` from a state that holds
  only the control registers' facts: the row-sum register (`%r6197`, accumulated over all rounds)
  has no value in the table. Its proof needs the data plane, with the row sum (and the row
  maximum) named at every site from the first round's sum to the final stores and the conjunct
  `0 < rs` in `Ref` (each round adds `ex2` values, positive by the `approx` assumption, to a
  positive sum, rescaled by a positive factor). Lane T1's `CorrWarp.DataSrc` positivity premise
  stays open until then.
- Size after this session: `Proof2/Softmax` 53 files, 6,377 lines (4,474 before); the
  `ShapeCtl6` (`narr`) file 985 s and the `ShapeTc` file 648 s in the full strict build on the
  loaded host.

- **Merge of `p4b-epilogue-wire`** (lane T1, 0161e036a: lane L round 8 through 731ce134d, the
  loader's reference invariant, safety by class): everything outside `Proof2/Softmax` and this
  lane's `Proof2/Lib/Counter32.lean`, `Proof2/Lib/FloatWord.lean` is lane T1's side, including
  files this branch had kept from older merges (the loader's split step files, `Startup/Shape.lean`,
  `Proof2/Lib/ShapeInit.lean`, which lane L promoted). This lane's `Proof2/Lib/ShapeTcWait.lean`
  is deleted (promoted to `Lemmas/Flow/Step/ShapeTc.lean`); `Shape.lean` imports the library file.

- **The fragment without the data plane** (`Fragment.lean`, `frag`, `ok`): `Fragment.Ok` of the
  softmax warps' fragment (the counted machine `MC`, the shape table `EvS`, `ret`, `Ref`,
  `Expect`) from two named premises about the data plane, `NumSteps` (the step obligation at the
  63 numeric states) and `DataStoreSafe` (the stores of data registers are no undefined
  behaviour). Everything else is proved:
  - **No death before the exit** (`RefNext.lean`, `next_ends`): an expected event of the state's
    shape whose successor is `none` is undefined behaviour or the exit. Two conjuncts were added
    to `Expect`, both on values a source supplies: at the first pass's tile count, the word's
    coordinates have divisions with a rule (`divOk` of both divisions of `Mma.coords`; the output
    warp's `coords_W` gives it from the scheduler's values, so lane T1 discharges it where it
    discharges the word's other facts), and at a bias load, bytes that rebuild into a value (the
    protected-read source of the loader's copies). `ExpectD` now takes `p L g`.
  - **No undefined behaviour** (`Safe.lean`, `SafeBld.lean`, `Align.lean`): at every site whose
    shape admits undefined behaviour, the fired instruction's template is not undefined behaviour
    under the facts (`NoUb` as a shape table): full-mask warp barrier and election, the CTA
    barrier's arrival with immediate operands, the store waits and the implicit waits (whole
    warps), the score loads (`tcDataAddressOk` of `tmS` and its column offsets, decided over the
    512 threads: the lane field `(tid >> 5) & 3` is the warp's chunk), the scheduler's and the
    request's global loads (`addrU`/`addrS` of the 4-aligned `cuQBase`, `usedKBase` from
    `Pre.alignment`), the bias loads (16-aligned: the low four bits of each word operation of
    `bAddr`, with the 1024-aligned shared base and the swizzle's mask `112`). A site whose shape
    has no undefined-behaviour alternative needs nothing (`ev_noUb`). `EvS := Ev ∧ no ub`, so
    `ref_safe` is the second conjunct and `ref_next` no longer needs its `hub` premise.
  - Not covered, the premise `DataStoreSafe`: the P stores after their wait and the statistics
    and final stores read data registers; Core faults such a store unless the register's value
    has four bytes (`storeValue`, `tcgen05.st`'s `bytes = 4` check), which the data plane's facts
    give.
  - Library candidates for lane L, `Proof2/Lib/UbFree.lean`: `elect_imm_ok`, `barArrive_imm_ok`,
    `tcLd_wait_ok`, `tcSt_wait_ok`, `tcLd_word_ok`, `loadTmpl_ok`, `effAddr_global`,
    `effAddr_shared32`, `ldGlobal_ok`, `ldShared4_ok` (templates that are not undefined behaviour,
    next to `Lemmas/Flow/UbStop.lean`).
  - Check times (strict build of the targets, loaded host): `Safe` 33 s, `SafeBld` 139 s (128
    states), `Align` 2.3 s, `UbFree` 1.6 s, `RefNext` 30 s, `Fragment` 4 s (`lean`).
  - Pitfalls met: a term-mode `by` inside `exact` that fails is logged and recovered, so `first`
    does not move on (the alternatives are tactic blocks ending in `done`); `fin_cases` leaves
    `(fun i => i) ⟨k, _⟩` in the state, and an `exact` whose unification meets it timed out on
    the score loads, while `refine'` with named holes did not; unifying `(tmS L g).toNat` with
    `(ori (tmS L g) 32).toNat` at default transparency does not fail fast (`with_reducible`).

- **Risk R2: `ShapeCtl6` and `ShapeTc` by hand.** The named-barrier arrivals (`narr` per round
  kind and `finarr`, now both in `ShapeCtl6`) read the barrier id `%r5127` once from the table
  (`nbW L g`) and apply `shape_barArriveR` with `nbW_tlt`; the Tensor Memory sites at sub-step 0
  (`ShapeTc`) apply their class lemma directly with the address register read once. Strict build
  of the targets: `ShapeCtl6` 941 s → 7.4 s, `ShapeCtl8` 390 s → 23 s (without `finarr`), `ShapeTc`
  555 s → 83 s. Through `site_shape` each site tried the role's `soft_addr` alternatives in turn,
  and the slow failures were unifications that unfold the table's words at default transparency.

- **Merge of lane L** (lane-L 01611b0f3, round 9: `seg_sym` reads a `.bits 32 w` register as the
  float `s` from `classify .f32 (.bits 32 w) = .ok (.fin s)`, including packs and assumption-ruled
  `mul`/`fma`; `RetKind.packed`; `classify_word` and `Counter32` promoted). This lane's
  `Proof2/Lib/FloatWord.lean` and `Proof2/Lib/Counter32.lean` are deleted; `NegScale.lean` and
  `Ref.lean` import `Lemmas/Flow/FloatWord.lean` and `Lemmas/Flow/Counter32.lean`. Conflicts:
  the loader's files and this file's loader paragraphs, where lane L carried main's older state;
  this branch's side (lane T1's newer loader) is kept.

- **Data-plane restatement: the plan as decided** (not started in Lean: lane L's reads were merged
  at the end of this session, 8ae42d54c). In order, each a commit that builds:
  1. `V` records reals: `sv : Fin 4 → Fin 32 → ℝ` (the score loads' payloads), the bias pairs as
     `bv : Fin 16 → Fin 4 → BitVec 64` words with `RetKind.packed .bf16` at `bld`, the row maximum
     `mx : ℝ` (or `-∞`, an `EReal`) and the row sum `rs : ℝ`; `succ` stops (`some none`) on any
     other kind, `ret` at `sld` becomes `.real .f32`, `stop_iff` re-run.
  2. `dataVals p L g d : List (Nat × Value)`: the data registers live at the state's pc
     (`Flow.live pc` filtered by `!ctl`), each the code's term from the recorded reals (the score
     registers, their packed pairs, the masked elements' conditionals as `MaskSeg.lean` states
     them, the row maximum and sum, the probabilities' packs before each P store), and
     `facts := factsFrom (ctlLive pc) valueOf ++ dataVals`. The masked maximum's and the
     exponent's start facts (`mask_max`, lane L's `E6`) are this function at `barr false`'s and
     `narr .first`'s pcs; their end facts must be its value at the next site, so each walk ends
     with `restate` to `dataVals` of the successor.
  3. Re-run the control families whose states carry data registers (the first and biased rounds
     from `sld` to `pwend`, the plain rounds from `sldw` to `pwend`): their facts grow by up to
     128 entries; the families are re-split if one exceeds the R2 rule.
  4. The numeric steps by family (`NumSteps`), the exponent stretch in pieces cut at pcs 4594 and
     4626 and inside the probability packs, one file at a time (27 GB for the whole stretch).
  5. `DataStoreSafe` from `dataVals` (four-byte values at every stored register) and `RowSumPos`
     from `0 < rs` in `Ref` (each round adds `ex2` values, positive by the approx assumption, to
     a positive sum rescaled by a positive factor).

- Size and verification after this session: `Proof2/Softmax` 57 files, 7,002 lines (6,377 before),
  plus `Proof2/Lib/UbFree.lean` 125 lines; `Proof2/Lib/ShapeTcWait.lean`, `FloatWord.lean`,
  `Counter32.lean` deleted (promoted). Full strict build at the lane-L merge 8ae42d54c: 9961 jobs,
  rc 0, including the statement, contract and axiom checks of `Tests/Kernel`; pytest (pre-commit)
  passed; `reading_uses --lean` consistent (61 EXT notes, 13 kernels); the axioms of
  `TmlFa4Fwd.correct` are `propext`, `Classical.choice`, `Quot.sound`; the diff of `Theorem.lean`,
  `Spec.lean`, `Assumptions*`, `Core/`, `lakefile.lean` against 0b44fb35f is empty.

- **Merges of this round.** At its start origin/main (684d6d442) and lane T1's
  `p4b-epilogue-wire` at 59b6ac874; that T1 tip carried a lane-L merge which T1 later withdrew
  (with the next tip, 15eb9f972, it broke the build and slowed step files about tenfold). On the
  coordinator's instruction the library is restored to origin/main's version (`Lemmas/`,
  `Tactics/`, `Tools/`, `tests/`, `Tests/`, FA4's two files and the three kernel files that lane-L
  merge touched: commit "restore the library to origin/main's version"), then T1's current head
  (a78bfce80) and origin/main (945ab1917, which now contains T1's loader work) are merged.
  Everything outside `Proof2/Softmax` equals origin/main except this lane's
  `Proof2/Lib/UbFree.lean`. Lane L's safe tip be1d8c350 (which carries the `UbFree` lemmas, as
  `Lemmas/Flow/UbFree.lean` and `TmplOkSync.elect_imm_ok`) is not merged: it does not contain
  origin/main, and the merge conflicts in four library files (`Counter32`, `Safety/Classes`,
  `Safety/Table`, `Lemmas/DECISIONS.md`) that only lane L can resolve. Decided: take it with
  origin/main's next batch; this lane's `UbFree` copy is deleted then (`Align.lean` imports
  `Lemmas.Flow.UbFree`; the library names `effAddr_global` `effAddr_global_bits`, used only
  inside the file).

- **Data plane, step 1: the score reals and the data machine** (`Data.lean`, `StepsScore.lean`).
  - `V.sv : Fin 4 → Nat → ℝ`: a score load records the reals of its 32 elements (`flAll`) and the
    machine stops (`some none`) when an element is not an `f32` payload; `ret` at `sld` is
    `.real .f32` (`stop_sld`). `ExpectD` at `sld` asks for `f32` payloads, the source obligation
    of the kernel's `TcLdDataflow` assumption (for lane T1).
  - `codeD`: the machine `code` whose facts are the live control registers and the live *named*
    data registers (`liveD`, `dnamed`), valued by the data table `valuesData` before the control
    table (`valueOfD`); one `factsFrom` table, so `seg_sym` reads it unchanged. Same states,
    invariant and successors as `code`; its facts contain `code`'s (`factsD_mono`), so every
    shape and safety lemma of `code` transfers (`shapeAtD`, `shapeD`) and the shape files are not
    re-run. `MC`, the fragment, `NumSteps`, `DataStoreSafe`, `RowSumPos` and the hand-off are on
    `codeD` (the hand-off's first facts are unchanged: no data register is live at pc 3102).
  - Named so far: the score pairs of each round kind (`pairReg`; pair `j` holds elements `2j` and
    `2j + 1`, element `n` is element `n mod 32` of load `n / 32`, `V.score`) from their packing to
    the bias products (first and biased rounds) or the exponents (plain rounds), and the
    destinations of the score loads (live from a load to its packs). Checked against the
    generated liveness by a script: at every event state of the role the live named registers
    are exactly the table's keys.
  - Every step family now proves `(codeD p L g).StepAt`. Strict build of the targets, loaded host
    (before → after): `StepsMid` 41 → 52 s (the bias loads carry the 64 pairs), `StepsFirstCtl`
    46 → 83 s, `StepsBiasCtl` 85 → 127 s, `StepsPlainCtl` 38 → 56 s; the families without data
    registers are unchanged apart from the host's load (scan 122 to 198 s, choice 224 s).
  - Numeric states stepped (`StepsScore.lean`, 202 s, 8.7 GB with `lean`): the score loads of the
    first and the biased rounds (8 states, override `soft_sld`: `step_tcLd` with the facts after
    the load, `valueAfterLd`), and the implicit waits of a plain round's first three loads (3
    states, `soft_sldw`). `sldp_ok` (a plain load at sub-step 0) now states the loaded
    registers (`holds_setRegs_live`, `valuesPairs_update`). `D.numeric` lists the 52 states still
    open; `NumSteps` is the step obligation there.

- **The bias words need a return kind lane L does not have yet** (request). The bias loads'
  words go through `mov.b32 {lo, hi}` (Core checks the word's bytes and splits it) and
  `cvt.f32.bf16` (the `bf16Convert` assumption reads a finite payload, Core decodes a bits
  pattern). Both evaluate only on a value of known form, and `cvt` on a half `.bits 16 w` with a
  symbolic `w` does not evaluate at all. `RetKind.packed .bf16` accepts such halves (any 16-bit
  word), so a machine that follows every accepted value cannot step the unpacks and the bias
  products for all its states, and stopping on other words would break `stop_iff`. What the
  data actually holds (the loader's copies of the Spec's `biasValue`) is narrower: each half is a
  `bf16` payload or the masked pattern `0xFF80`, and two masked halves rebuild into the word
  `0xFF80FF80`. Request to lane L: a return kind that accepts exactly the words a load of payloads
  of `fmt` or one masked pattern `m` rebuilds (`.pair a b` with each of `a`, `b` a payload of
  `fmt` or `.bits (8 · fmt.bytes) m`, and the merged word of two `m`); the machine then records
  each bias word as two `Option ℝ` (`biasValue`), stops on other words, and the unpacks and
  `cvt`s evaluate. Until then the 32 bias-load states at sub-step 3 (their unpacks) and the
  bias products after the named barriers stay in `NumSteps`. Decided: not worked around in the
  role (a premise on the recorded words would be a statement no proof can discharge).

- **`RowSumPos` as stated is false for padding rows** (report, for lane T1 and the correction
  lane). A row `row ≥ qLength b` of a 128-row stage has bias values the Spec does not constrain
  (`biasMask` covers `row < qLength b` only), so all of them can be the masked `-∞`; on a tile
  without plain rounds every element of such a row is `-∞`, the code selects 0 for the maximum
  (pcs 4395 and 4396), every `ex2` gives 0, and the row sum it stores at `fin 0` is 0. The
  correction warps' code handles this (`setp.ne.f32` and `selp` of 1 at pcs 8469 and 8470), but
  their `Expect` at `fsum` (`Correction/RefNext.lean`: a positive real) and `Correction.Ref.pos`
  ask for `0 < x` for every row, which no source can supply. What holds: `0 ≤ x` for every row,
  and `0 < x` for a row with a finite maximum (each row `row < qLength b` has one: its key 0 is
  unmasked, `biasMask`), as the old tree's `DenominatorValid` states. Decided: the softmax
  fragment will prove those two (step 4); `RowSumPos` is restated when the row sum is in the
  table, and lane T1's `CorrWarp.DataSrc` positivity premise needs the correction warps to accept
  a zero row sum (their `Expect` and `Ref` are lane T1's / the correction lane's statements).

- Size and verification after step 1: `Proof2/Softmax` 59 files, 7,479 lines (7,002 before). Full
  strict build (a58dc50bb, before the library restore): 9977 jobs, rc 0, including the statement, contract and axiom checks of
  `Tests/Kernel`; pytest (pre-commit) passed; `reading_uses --lean` consistent (61 EXT notes, 13
  kernels); the axioms of `TmlFa4Fwd.correct` and of `Softmax.ok` are `propext`,
  `Classical.choice`, `Quot.sound`; the diff of `Theorem.lean`, `Spec.lean`, `Assumptions*`,
  `Core/`, `lakefile.lean` against origin/main is empty. After the library restore and the merges
  of a78bfce80 and origin/main 945ab1917: full strict build 9972 jobs, rc 0; the same axiom,
  `reading_uses` and trusted-file checks pass.

- **Data plane, step 1b: the row maximum and row sum as recorded values, the masked maximum over
  masked bias products, and a plain round's maximum** (`Machine.lean`, `Data.lean`,
  `PlainFold.lean`, `MaskSeg.lean` … `MaskChain.lean`, `StepsScore.lean`).
  - `V.mf`, `V.mr`, `V.rs`: the row maximum and row sum before the current round. The maximum is
    the code's value `mxVal`: the `f32` number `mr` when `mf`, else the pattern of `-∞`
    (`0fFF800000`), so it may be `-∞` (a padding row whose first round is all masked). They are
    the values of `%r6191` in a bias round, `%r6195` in a plain round, `%r6196` and `%r6197` at
    the final stores. Decided: they are fields updated at a round's end (`afterFirst`,
    `afterBias`, `afterPlain`, inside the closing poll's step, which is still numeric), and a
    round's own maximum, subtracted maximum and rescaling factor are terms of the table over the
    round's recorded values and these fields (rule M2), not fields set inside the round. The
    first round's updates are added with its numeric steps (no transition into the bias or plain
    rounds is stepped before them).
  - Named in the data table: `%r6191`, `%r6195`, `%r6197` at the bias and plain rounds' states
    (`valuesRun`), and at a plain round's states from its statistics store on the maximum
    `%r6196`, the subtracted maximum `%r4454` and the rescaling factor `%r432` (`maxP`, `facP`,
    with the keep test `keepP`: `setp.ge.f32` of the scaled difference against `-8`); at the
    final stores `%r6196` and `%r6197`. The first and bias rounds' `%r6196` (live from their
    maximum on) is not stated before pc 6661 (`liveF`); it needs the bias products.
  - `liveD` (the live function the segment tactics read) is the table's registers at the role's
    state program counters (`statePcs`, `liveF`) and every live register elsewhere: `seg_sym`
    restricts a walk's facts at every program counter to the end facts' live function, so with
    the table's filter at every pc a numeric walk dropped the unnamed data registers it had just
    computed. The control families are unchanged by this (all re-checked).
  - **`mask_max` over masked bias products**: a product is `bv32 bf sc n`, the `f32` number
    `sc n` when its bias element is a payload (`bf n`), else the pattern of `-∞` (the masked
    bias `0xFF80` converts to `-∞`, and the ideal `fma` keeps it); `mre` takes an extended real
    and the fold is `foldM m (bpe bf sc)`. With the bias kind the products' facts take this form
    from the bias halves. The product pairs are written as explicit conditionals in the word
    pieces' statements: the unpack `mov.b64 {a, b}` does not evaluate on a pair of an
    abbreviation's values (Core's byte check does not unfold it), while the fold reads the
    elements through the abbreviation. Check times (strict build of the targets, loaded host):
    words 0 to 3 91 s, 115 s, 142 s, 170 s (6.5 to 10.8 GB with `lean`), the fold 24 s, the
    chain 2 s.
  - **A plain round's maximum** (`stepAt_sldw3`, the implicit wait of the fourth score load):
    the packs of the fourth load, the fold from `%r6195` and the 128 scores (`foldPT` from a
    finite maximum, `foldPF` from `-∞`, generated from the code's `max.f32` tree), the keep test,
    the rescaling factor (`ex2.approx` read exactly; `2 ^ (s · (mr - F))`, the pattern of one when
    kept, `+0` when the maximum before was `-∞`) to the statistics store (pc 6890). Three
    findings:
    1. The walk runs once per kind of the maximum before the round: as a conditional value the
       `-∞` side goes through Core's `max` rule (`condStep`'s constant side), whose result the
       following `sub.f32` does not read.
    2. Uncut, the walk carries the fold's 130-node term into the keep test and the factor and
       did not finish in 40 minutes; cut after the fold (pc 6877, `Seg.comp_ex`, the fold stated
       from the statistics store's table as `foldP`, `liveCut`) both cases check in 175 s in
       scratch; in the strict build of the targets `StepsPlainMax.lean` checks in 424 s,
       `StepsScore.lean` in 156 s.
    3. The table's value of `%r6195` (a reducible match on `mf`) is not read by the rule steps,
       so the walk takes it as an explicit first fact (`seg_start_cons`).
    The `-∞` case multiplies the scale (left operand) by `-∞`: `Proof2/Lib/MulEReal.lean`
    (`mulEReal_coe_bot_pos`, for promotion next to `mulEReal_bot_pos`) in context lets the rule
    step evaluate. `D.numeric` lists 51 open states.

- **Merge of origin/main 693bc5a5b** (batch 28: lane L's `UbFree` lemmas in the library, the
  masked `bf16` return kind `RetKind.packedWith fmt (maskedElem fmt m)`): this lane's
  `Proof2/Lib/UbFree.lean` is deleted; `Align.lean` imports `Lemmas.Flow.UbFree` and
  `Lemmas.Flow.TmplOkSync` (`elect_imm_ok`). An earlier merge of fce3eb8fe was superseded by this
  one before its full build finished.
- **A wrong control fact** (found while preparing the plain exponent stretch): the plain rounds'
  table stated register 8692 (`%rd1404`, the exponent stretch's multiplier) as `.bits 64 0`; the
  code sets it at pc 6659 to the pair of the scale word (`mov.b64 %rd1404, {%r6073, %r6073}`),
  `joinValue` of the two words as in the first round's 7896. No proved step read it (the plain
  control families carry it, the entry into the plain rounds is in the open closing-poll steps);
  corrected in its own commit.
- **The plain round's exponent stretch** (scratch walk of pcs 6892 to 7416 from the pairs, the
  subtracted maximum as a real, `%r170 = -s` and the multiplier pair): the `fma` and hardware
  `ex2.approx` part walks (the probabilities are `2 ^ (x n · s + mu · (-s))`, read exactly); the
  walk stops at the first software `exp2` site (pc 7090): `seg_sym` has no step over a segment
  assumption (the kernel's `swExp2`, a `segmentRule` over `cuteExp2`'s template). Needed: a
  `Seg` piece per template site from the template's match (`cuteExp2.matchAt kernel pc`) whose
  outputs are `swExp2Lane` of the inputs (the old tree's `SoftmaxExponent.softwareExponentRun`
  and `softwareExponentValues` are the model), in `Proof2/Lib` or from lane L (request recorded
  for lane L). Also `%r170` (register 1230, `-s`, written at pc 4398 in the first round) is live
  through all later rounds and must be named at the first round's P part and at the bias and
  plain rounds' states.
- **The bias kind, how it will be used** (decided, not yet in Lean): the bias load at `bld`
  stops on a word that `packedWithVal .bf16 (maskedElem .bf16 0xFF80)` rejects (`ret` becomes
  `.packedWith`, `stop_iff` re-run) and records each half as a finite flag and a real (the
  conditional form `bv32` uses, not `Option ℝ`), so that the walk through the unpacks, the
  `cvt.f32.bf16` widenings and the bias products splits per half (`condStep`) and lands in the
  `bv32` products `mask_max` takes. `Expect` at `bld` then asks for an accepted word (the
  protected-read source of the loader's copies of the Spec's `biasValue`, lane T1).

- Size and verification after this session: `Proof2/Softmax` 61 files, 8,531 lines (7,479
  before), plus `Proof2/Lib/MulEReal.lean`; `Proof2/Lib/UbFree.lean` deleted (in the library).
  Full strict build of the merge of 693bc5a5b: 10011 jobs, rc 0, including the statement,
  contract and axiom checks of `Tests/Kernel`; strict build of the softmax targets after the
  8692 fix: rc 0. pytest (pre-commit) passed; `reading_uses --lean` consistent (61 EXT notes,
  13 kernels); the axioms of `TmlFa4Fwd.correct`, `Softmax.ok` and `stepAt_sldw3` are `propext`,
  `Classical.choice`, `Quot.sound`; the diff of `Theorem.lean`, `Spec.lean`, `Assumptions*`,
  `Core/`, `lakefile.lean` against origin/main is empty.

- **The bias loads with the masked kind; `%r170` named** (`Machine.lean`, `Stop.lean`,
  `RefNext.lean`, `Data.lean`, `BiasUnpack.lean`, `StepsBiasLoad.lean`, `StepsBiasLoad2.lean`).
  - A bias load accepts a word exactly when lane L's `packedWithVal .bf16 (maskedElem .bf16
    0xFF80)` does (`biasOk`) and stops (`some none`) otherwise, at every element; `ret` at `bld`
    is `.packedWith .bf16 (maskedElem .bf16 0xFF80)` (`stop_bld`). The invariant's midway part
    for a bias load now also says the accumulated words are accepted. The last element records
    the halves of the four words (`recordBias`: `V.bk`, `V.br`, a finite flag and a real per
    half, low half first; `V.bv` is gone). `Expect` at `bld` asks for an accepted word (the
    protected-read source of the loader's copies of the bias, lane T1).
  - The last element of each of the 32 bias loads is stepped (`stepAt_bld3`): the four unpacks
    are pieces from lane L's `exec_unpack_masked` (`seg_unpack`, the high and low half written
    as `hv16`, the earlier words accepted by the invariant, fresh keys decided on the keys only:
    `freshKeys_eq`, `fresh_keys`), and the landing facts are checked by `seg_sym` without a step.
    The data table names the halves at the later bias loads, the fence, the named barrier and
    the arrival (`valuesHalves`, literal registers and indices: a case split of the segment
    tactics rewrites facts with `simp`, which would reduce arithmetic in a table entry). Check
    times (strict build): `StepsBiasLoad` 263 s, `StepsBiasLoad2` 284 s (16 states each, about
    16 s per state): above the 15 s rule, recorded as a defect to cut (the remaining cost is the
    landing check over the 200 table facts and the fresh-key evaluations).
  - `%r170` (register 1230, the negated exponent scale) is named from the first round's P part
    to the end of the rounds (`negS`).
  - Open numeric states: 19 (`D.numeric`).
- **Transfer of the old tree's numeric proofs (measured, coordinator's plan).** The old softmax
  machine (`Proof/Thread/Softmax.lean`) is an observation machine with no per-site step
  obligation, so `Code.stepAt_map` (equal facts and a `StepAt` of the image) has nothing to map
  from. The old tree's numeric content is local-run lemmas over thread states (`At t s [] →`
  register hypotheses `→ ∃ u, At u s' facts ∧ ReflTransGen (Tau …) t u ∧ frame`), in the
  vocabulary `scoreValue (Option ℝ)` (with `-∞` as `none`, no finiteness hypotheses), `fl`,
  `probabilityDoubleWord`. Coverage of the 19 open states:
  first round products to maximum (`bsync false`, `barr false`): `firstCausalMaskLocal`
  (3863→4329), `firstMaskedMaxLocal` (4329→4395), `finiteReferenceLocal`; the products 3591→3863
  to be located; exponent (`narr .first`): `firstAffineFrameWithNegScaleLocal` (4398→4403),
  `firstShiftedPacksLocal` (→4818), `probabilityUnpackLocal` (unpacks before each store);
  P packs: `probabilityUnpackLocal`; first row sum and loop entry (`pwend .first`):
  `firstRowSumLocal` (4877→5006), `firstLoopEntryLocal`, `plainLoopEntryLocal`; bias round
  maximum and rescale: `biasedMaximumLocal`, `biasedReferenceLocal` (→5675),
  `biasedShiftScaleLocal`; plain: `plainMaximumLocal`, `plainReferenceLocal`,
  `plainShiftOffsetLocal`; repeated exponent with the software `exp2`:
  `repeatedShiftedWordsLocal`; repeated row sum and loop tail (`pwend .bias`, `pwend .plain`):
  `repeatedSumAndLoopTailLocal`. What the transfer needs: a landing from a run instead of a
  segment (`Code.Cont` already takes a `ReflTransGen` run; a `Lands` variant with a run, kernel-
  local in `Proof2/Lib`), and the table's data values stated in the old vocabulary so that the
  old lemmas' hypotheses and conclusions match by `rfl`. The fragment interface (`NumSteps`,
  `codeD`'s states and successors) does not change.

- **The run landing for the transfer** (`Proof2/Lib/LandsRun.lean`, for promotion next to
  `Lemmas/Flow/Step/Combinators.lean`): `LandsR` asks that every state after the event reaches the
  successor's site with its facts by local steps (`ReflTransGen Tau`), the form of the old
  tree's local-run lemmas; `Lands.toR`, `LandsR.cont`, and `step_issueR`, `step_arriveR`,
  `step_waitR`. The recipe per numeric state, starting with `pwend .plain`:
  1. The table at the plain P part's states names the probabilities in the old reduction's
     layout (`Repeated.scalarInputs .unbiased`: registers 1493 to 1536, 5128 + 3k, 1537 to 1548,
     …, 1573 to 1604) as `fl (probP p v i)`, `probP` stated in the old exponent lemmas'
     vocabulary (`scoreValue`, `affineScore`, the hardware and software `exp2` values) so that
     the exponent stretch's transfer matches by `rfl`. Found while preparing it: the old
     reduction indexes the weights by column (`RepeatedWeights r u weights`, the old thread
     layer's `weights col = shiftedWeight …`), and a column's weight is the hardware `ex2`
     value (`2 ^ x`, read exactly) or the software `exp2` value (`cuteExp2.fn x`, the kernel's
     `swExp2` assumption) by its lane (the unbiased layout interleaves four groups of four
     software outputs, registers 5128 + 3k and its three shifts), and `0` for a masked column;
     so `probP` is defined per column from the round's affine score
     (`affineScore s (-reference) (score col)`, `repeatedShiftedWordsLocal`) and the column's
     lane.
  2. `pwend .plain`'s successful poll: `repeatedSumAndLoopTailLocal .unbiased` from pc 7466
     (after the poll's branch, a short `seg_sym` piece) with `weights := probP p v`,
     `old := v.rs`, `alpha` the real of `facP` (adapter: `valFloat .f32` of the three forms of
     `facP`), `mx := some (maxPR p v)` (adapter: `maxP p v = scoreValue (some (maxPR p v))` by
     cases), landing at the loop head 6661 or the exit; then `seg_sym` to `ws .plain` or
     `fin 0`. `afterPlain` records `mf := true`, `mr := maxPR p v`, `rs := v.rs · alpha + Σ
     probP` (the old lemma's `mass`).
     Found when checking the hypotheses: the old row-sum lemmas frame only the loop's own
     registers (`repeatedRowSumLocalOfWordWithFrame`: `sumContinuationRegs`, seven registers;
     `repeatedSumAndLoopTailLocal`: only the registers it states), so the control registers the
     next state's table names (the plain round's addresses and barrier words, `valuesPlain`)
     are not carried through their run. Decided: the row sums (pcs 7466 to 7599, 6561 to 6647,
     4877 to 5006: sums of the 128 weights, linear terms) are walked by `seg_sym` with the
     weights in the table, and the transfer is used where an old lemma exports a full frame
     (`firstMaskedMaxLocal`, `repeatedShiftedWordsLocal`, `firstShiftedPacksLocal`:
     `∀ r ∉ writes, u.regs r = t.regs r`).
  3. The same for `pwend .bias` and, with `firstRowSumLocal` and the loop-entry lemmas, for
     `pwend .first` (which also sets `mf`, `mr`, `rs` in `afterFirst`).
  4. The exponent stretches (`narr _`) and the P packs by `repeatedShiftedWordsLocal`,
     `firstShiftedPacksLocal`, `probabilityUnpackLocal`; the first and bias rounds' maxima by
     the mask and maximum lemmas.
  Check cost (audit item 9) after the transfers move: one applicable alternative per site in
  `soft_addr`, per-site transition lemmas instead of `soft_sites`' 21-lemma list, default
  heartbeats in the shape files, and `StepsBiasLoad*` below 15 s per state.

- **A plain round's closing poll and row sum** (`StepsPlainEnd.lean`, `stepAt_pwend_plain`;
  `Machine.lean`: `maxR`, `probR`, `rsP`, `afterRound`; `Data.lean`: `valuesProbP`,
  `valuesPlainP`, `valuesData`; `PlainFold.lean`: `rowSumT`).
  - The table names a plain round's 128 weights at its P part's states, in the order of the
    code's row sum (`valuesProbP`: column `i` is the `i`-th register of the old reduction's
    layout, `Repeated.scalarInputs .unbiased`), as `fl (probR p v i)`: `probR` is `2 ^ (x_i s - M
    s)` per kind of the maximum before the round (the software `exp2` template's function is
    also `2 ^ x`, `cuteExp2.fn`).
  - The successful poll walks the row sum (pcs 7466 to 7598, `rowSumT`, generated from the
    code's add tree), the loop tail and the next round's poll or the final stores; the state after
    records `mf := true`, `mr := maxR p v`, `rs := rsP p v` (`afterRound`). The walk runs once per
    kind of the maximum before the round (`mf`); with `mf` true the walk's values on the keep test
    are conditional values of numbers and the table's are numbers of conditionals, which
    `sym_close` closes once the table names the state's values (not projections of the state:
    `valuesData` now matches on the state) and `maxR`, `rsP` are reducible (so that `sym_close`
    sees their conditional).
  - The plain round's table states `maxP`, `facP` and `mxVal` per kind of the maximum before the
    round (`valuesPlainP` matches on `mf`): a conditional on `mf` in a table entry, even with a
    literal `mf`, made the walk's case split restate the facts by a `simp` that did not close.
  - The old tree's `repeatedRowSumLocalOfWordWithFrame` does not fit (it carries seven
    registers through its run), so the row sum is walked.
  - Check times (`lean`, loaded host): `StepsPlainEnd` 450 s (the two cases of the maximum before
    the round), `StepsPlainCtl` 405 s (the plain P part's states carry the 128 weights, and
    the family runs once per kind of the maximum before the round, as the table states it per
    kind):
    both over the rule, to be cut with lane L's generated-value runs (`Tools/out_gen.py`,
    32-instruction pieces) once batch 31 is on main.
  - Open numeric states: 18.

- **Generated runs for the numeric states; the first round's exponent stretch and P part**
  (`Gen/Out/softmax_expo1.json`, `softmax_pk1.json` → `Proof2/Softmax/Gen/Expo1.lean`,
  `Pk1.lean` by lane L's `Tools/out_gen.py`; the declarations sit where `tests/test_out_gen.py`
  checks the outputs' freshness; `GenRules.lean`; `StepsNarr1.lean`, `StepsP1.lean`; library
  candidates in `Proof2/Lib/OutKinds.lean`, `RunFrame.lean`, `RegionFrame.lean`).
  - Decided: inside a round's P part the data table is the generated run's end facts (rule M2:
    each register's entry is the term the code computes from the start state's values), not a
    closed form. `valuesData` at the first round's P states is `p1Data`: the exponent stretch's
    end facts over the values at pc 4399 (`vExpo1`: the arrival state's values with `%r170`), then
    the halves the later unpacks write as splits of the packed words' terms. The arrival state
    (`narr .first`) names the 128 masked products, the maximum the exponents subtract (`selMax`,
    `%r2625`) and the row maximum in closed form (`valuesNarr1`, the forms `mask_max` states).
    `valuesData` now takes `L g`; the closed-form table is `valuesData0`, so the generated terms
    over the arrival state's values (`valueOfD0`) are no recursion.
  - The condition of a generated piece (each item's outcome is no fault) is decided by kinds
    (`OutKinds.lean`): a kind is a set of values (`pw`, `nn`, `fl`, `ni`: clean four-byte values
    that the ideal assumption reads as a positive real, a real `≥ 0`, a real, a real or `-∞`;
    `pr k` pairs; `h16` bias halves), each item kind maps its sources' kinds to its destination's
    (`kItem`; `fma2` of `ni`, `pw`, `fl` lanes gives `ni`, `ex2` of `ni` gives `nn`, the packs of
    `fl` give `w4`), and `kRun_sound` gives the condition from the start values' kinds. The kinds
    after each piece are literal lists (`kList`), the checks of all pieces one kernel evaluation
    (`expo1_kok`), so no check recomputes the pieces before it. The start kinds are lemmas on the
    closed forms (`elemVal_ni`, `selMax_fl` with `foldF < ⊤`, `paramW_pw`).
  - Control facts a run does not write are carried by `SegD.frame` (`RunFrame.lean`: a
    straight-line run keeps the registers its code does not write, checked on the code slice;
    needs `RulesFrame Assumptions.all`, `Gen.rulesFrame`, with the frames of `lg2` and
    `bf16Convert`). The landing (`land_run`): the successor's table lists the run's end facts
    first (`valueOfD_prefix`, distinct keys by `nodupB`), its control registers have the start
    state's values.
  - The P part's control sites (the last two stores, the store waits, the warp barrier, the
    election, the elected lane's arrival) are proved on the control machine `code` and lifted to
    `codeD` (`Lift.lean`, `stepAt_lift` from `RegionFrame.lean`'s `Code.StepAt.lift`): the event
    (`eventWrites`) and the local code up to the next event (`regionB`, a Boolean check on the
    code) write no data register the state names, and the successor has the state's data table.
    So the 170 data facts of a P state are never walked by the segment tactics.
  - Kernel pitfall: an equation `lookup … = selMax (foldF …)` checked by `rfl` made the kernel
    unfold `selMax` and the 128-term fold (lazy delta by definition height; 200 s and a deep
    recursion). The closed-form entries are first in `valuesNarr1` and read through
    `lookup_head`, a lemma with the value as a variable. Likewise a destructuring `obtain` of a
    Boolean conjunction made the elaborator evaluate the checks (`band_split` instead).
  - Kernel pitfall 2: a generated piece's end-facts equation (`factsFrom … (xFinal …) = G`)
    checked by `kernel_rfl` with the start values a concrete state's `valueOfD` made the kernel
    unfold the state's table (deep recursion after 200 s). Every such check is stated for a free
    value function (`pkA_G`, `expo1_chain`) and instantiated; the landing of the store unpacks
    goes through `unpackSpec1` (`valueOfD_p1h`, `p1_halves`, `unpack_land`) instead of `rfl` on
    table lookups. `StepsP1` checks in 45 s, `StepsNarr1` in 86 s (`lean`, loaded host).
  - Open numeric states: 14 (`D.numeric`).

- **The first round from its named barrier to its closing poll** (`StepsProd1.lean`,
  `StepsBarr1.lean`, `StepsPw1.lean`; generated runs `Gen/Out/softmax_prod1.json`,
  `softmax_rsum1.json`).
  - The bias products (pcs 3593 to 3849) are a generated run (9 pieces); its condition holds by
    kinds (bias halves `h16`, the bias scale word `pw`, score pairs `pr fl`; `prod1_ok`), and each
    product pair equals the closed form `mask_max` reads (`prod1_pairs` from `prod_eq`: the scaled
    bias plus the score, or `-∞` for a masked half). The run's declaration also outputs the bias
    scale's pair `%rd608` (control register 7896, live through the later rounds).
  - `chain1` (pc 3591 to the arrival at pc 4397) composes the scale-word reads (`seg_sym` on the
    control facts), the products, the mask count (`seg_sym`), the mask selects and the fold (the
    existing `mask_word0` … `mask_fold`, restated on `maskPairs`/`elemsF` by kernel-checked list
    equalities) and the maximum the exponents subtract (`sel_max`, per kind of the maximum). Each
    piece is stated on what it reads; the other facts are carried by `SegD.frameR` up to the event
    at pc 4397 (`seg_frame`), so no piece walks the 192 data facts. `stepAt_barr1` (lane 0's
    arrival) and `stepAt_bsync1` (the named barrier; the other lanes branch to pc 3591) use it.
  - Decided: the round's maximum and row sum are recorded at the first round's end
    (`afterFirst`: `mf := finE (foldF …)`, `mr := (foldF …).toReal`, `rs := rs1 …`), as the
    plain rounds' end does. `rs1` is the generated row sum of the exponent stretch's weights
    (`valR` of `Gen.rsum1_v5005`); it is the number value of a real `≥ 0` (`rsum1_float`, from the
    weights' kind `nn` and the last `add.f32`). For `Machine.lean` to state it, the closed forms
    the first round's exponent stretch reads (`elemRegs` … `valuesNarr1`, `ninf32`, `negS`) moved
    from `Data.lean` to `Machine.lean`, and `vExpo1` is now a lookup in the arrival state's data
    (with `%r170` and the scale word) instead of an update of `valueOfD0`; `StepsNarr1` relates
    the two on the run's keys (`vExpo1_eq`).
  - `pwend .first` stays open. Proved: the row sum's value (`rsum1_float`), the successful poll
    to pc 5006 (`pw1_run`: the branch by `Seg.bra`, the run framed by `SegD.frame`, the control
    facts restated on the control table `valueOf`), and the failed poll's return (`seg_jmp`, an
    unconditional branch as a piece). Open: the walk from pc 5006 into the bias rounds, the plain
    rounds or the final stores. `seg_sym` from the 23 facts at pc 5006 to the final stores'
    facts (one branch, the maximum's kind and the branch conditions as hypotheses, the row sum
    generalized to a variable) did not finish in 20 minutes (7 GB); with the successor still an
    unsplit `if`, `site_norm` reached the maximum recursion depth. The plain rounds' closing
    poll lands the same way through `lands_auto`. Likely cause, to check first: the walk's branch
    tests at pcs 5024 and 6656 compute `%r299` from `%r168` and `%r166` (pcs 5006 to 5008), so the
    hypothesis on `r299 p L g v` does not decide the walked test syntactically and the walk
    follows both outcomes into the rounds; the remedy is a cut before each branch with the
    walked predicate rewritten (`Seg.pred_ex`) or a role `sym_decide` rule for `r299`.
    Checked on the PTX (not yet by a walk): pc 5008 writes `%r299` as `max.s32` of `%r166 -
    min(%r168, %r166)` with 0, which is the body of `r299` but not the term `r299 p L g v`;
    pc 6654 writes `%r431` as `min.s32 %r169, %r299`. The branch hypotheses are to be stated
    with `r299` and `r431` unfolded (`simp only [r299, r431] at h1 h2`) before the walk, each
    walk cut at the branch and bounded to minutes.
    Measured (`lean`, loaded host, `seg_sym` from the 23 facts at pc 5006 with an empty target,
    5 or 3 min bound): to pc 5013 4 s, to 5019 7 s, to 5022 9 s, but to 5021 and to 5024 not
    within the bound; to the final stores with `r299`, `r431` unfolded in the hypotheses not
    within 5 min. So the cost is not the branch decision: it depends on where the walk stops
    (pcs 5021 and 5024 end just after `%r2903 = %r169 - %r299` is live with `%p628` unwritten
    or written; pc 5022 ends after both). Next: cut at pc 5022 with the facts stated there
    (`%p628` as `scmpi .lt .s (sub32 (r169 …) (r299 …)) 1`, the control registers of the
    rounds' tables), then the branch by `Seg.pred_ex` and `Seg.bra`, then the plain entry's
    test the same way.
- Merge of origin/main ec4c9aa8c (lane T1's `SmWarp/Fits.lean` reads `afterFirst` as
  `D.ite _ (plainEntry …) _`): `afterFirst` keeps that shape (its outer test reads `d.v`, the
  plain entry the updated values), so `keepS_afterRound` checks unchanged.
  - Kernel pitfall 3: lookups whose value is a large closed form (`vExpo1 … 7256 =
    erealValue (foldF …)`) are rewritten by a lemma with the value as a variable (`lookup_snd`),
    not checked by `exact`/`rfl`, as for `lookup_head`.
  - Open numeric states: 12 (`D.numeric`): the first round's closing poll, the bias round from
    its named barrier (products, maximum, exponent stretch, P part, closing poll) and the plain
    round's exponent stretch and P part.
  - A wrong control fact (found by the first landing into a bias round's poll from a walk): the
    bias rounds' table (`valuesBias`) did not name the bias scale's pair (register 7896, `%rd608`,
    set once at pc 3596 and read by every bias round's products), so their states stated it as
    the default `.pred false`. No proved step read it (the bias rounds' control steps carry it
    unchanged; every entry into the bias rounds was open). Added with the first round's value.
  - Check times (strict build of the family, loaded host, 200+ jobs in parallel): `StepsProd1`
    47 s, `StepsNarr1` 169 s, `StepsP1` 72 s; `StepsBarr1` 889 s, of which 520 s were the four
    frames' `regionB` checks: `regionB` looks each position up in the whole code (`K.code[pc]?`),
    which the kernel evaluates from the list's start for each of the 800 positions. The frames
    now check `regionS` on the slice `(K.code.drop lo).take (hi + 1 - lo)` (`Proof2/Lib/
    RegionSlice.lean`, `regionB_of_S`, for promotion): `chain1` 546 s → 95 s (`lean`, loaded).
- **What the remaining numeric states need** (measured on the code, decisions for the next
  session):
  - First round's closing poll: the walk from pc 5006 (above).
  - Bias round (7 states). The products (pcs 5279 to 5534) are a generated run like `prod1`
    (inputs: the later rounds' halves 914 to 1041, the score pairs 7367 to 7430, the scale pair
    7896). The maximum (pcs 5535 to 5674) folds the products with the maximum before the round
    (three-operand `max.f32`, which `Tools/out_gen.py` has no item for): a segment like
    `mask_fold` from the products and `mxVal`, then the keep test and the factor per kind of the
    maximum (as `StepsPlainMax`). The exponent stretch branches at pc 5815 on `%p632` (round
    index below `%r301`): pcs 5816 to 5976 use the hardware `ex2` only, pcs 5977 to 6298 also
    the software `exp2` template at 8 sites (6059 … 6277), whose inputs can be `-∞` (a masked
    bias half); `Seg.segTwo` (`Lemmas/Flow/FloatRun.lean`) needs real inputs, so a `-∞` variant
    of the template piece is needed (the `swExp2` assumption states the zero output). The
    tables at `stat false`, `narr .bias` and the bias P part must name the round's generated
    terms (as `p1Data`), and the bias P part's control sites then move to the lifted form
    (`stepAt_lift`, as the first round's). `afterBias` must record the maximum and row sum.
  - Plain round (4 states). Its exponent stretch (pcs 6892 to 7415) has the software `exp2`
    template at 8 sites (7090 … 7307) with real inputs (`Seg.segTwoAt` applies); the run is cut
    at those sites into generated runs. Its P part's table states the weights in closed form
    (`probR`), which `StepsPlainEnd` uses; the generated terms must be shown equal to it, or the
    table moved to generated terms and `StepsPlainEnd` redone on a generated row sum.

- **Check cost: re-cuts** (task step 2; audit item 9). Strict build of the family after lane L's
  `seg_fp`/`sym_close` speed-up (merge of 582c598e9), loaded host (200+ jobs in parallel), files
  at or above 60 s: `StepsBarr1` 889 s (now about 100 s, `regionS` above), `StepsPlainMax` 821 s,
  `StepsPlainEnd` 659 s, `ShapeBld` 428 s, `StepsBiasLoad` 379 s, `ShapeScan` 327 s,
  `StepsBiasLoad2` 286 s, `ShapeTcWait` 286 s, `StepsSelect` 285 s, `StepsScore` 278 s,
  `StepsPlainCtl` 271 s, `StepsScanSecond` 270 s, `StepsScanLoop2` 256 s, `SafeBld` 212 s,
  `StepsScanLoop` 211 s, `StepsBiasCtl` 200 s, `StepsScanFirst` 186 s, `ShapeCtl4` 172 s,
  `StepsNarr1` 169 s, `ShapeTc` 169 s, `StepsFirstCtl` 116 s, `StepsMid` 106 s, `Safe` 92 s,
  `ShapeCtl2` 85 s, `ShapeCtl7` 81 s, `ShapeCtl1` 74 s, `StepsP1` 72 s, `StepsReq` 71 s,
  `StepsEnd` 71 s, `RefNext` 68 s, `ShapeCtl5` 66 s. `ShapeCtl6` went from 1409 s to 14 s with
  the library speed-up alone.
  - Done: the plain round's P part's control sites (stores, store waits, warp barrier, election,
    the elected lane's arrival) are stepped on the control machine (`stepAt_plain_pctl`) and
    lifted (`StepsPlainP.lean`, `StepsPlainP2.lean`, as the first round's P part), so the 128
    weights are not walked; `StepsPlainCtl` keeps the poll and the statistics store.
    `StepsPlainCtl` 271 s → 40 s; the lifted sites 77 s in one file, then 45 s and 44 s split.
  - Next, by expected saving: `StepsPlainEnd` (the row sum as a generated run instead of a walk;
    needs the generated sum shown equal to `rowSumT`), `StepsPlainMax` (the fold cut into
    framed pieces), the bias rounds' P part by the same lift once their table names the generated
    terms, and audit item 9 (`soft_addr` one alternative per site class, per-site transition
    lemmas instead of `soft_sites`' 21-lemma list, default heartbeats in the shape files).

- **The first round's closing poll** (`StepsPwE.lean`, `stepAt_pwend1`). The walk from pc 5006
  is cut at pc 5022 (`pwA`, facts `pwMid`: `%p628` as the test on `r169` and `r299`, `%r299` and
  `%r300` (`r300`, the unclamped bound of `r301`) in closed form, the control registers as an
  explicit list, since `seg_fp` reads only literal fact lists or `factsFrom (ctlLive pc) …`);
  the branch reads `%p628` as a literal (`Seg.pred_ex`), and the plain entry's test at pc 6656
  reads the walked `min32 (r169 …) (r299 …)`, which the hypothesis states with `r431` unfolded.
  Six walks (three successors, two kinds of the maximum), each about 20 s; `StepsPwE` 97 s with
  `lean` on the loaded host. Kernel pitfall 4: rewriting `r431` of the updated values by `rfl`
  and `simp` over the unfolded successor made the kernel recurse too deep; `r431_eq_of` (by the
  scan and used-K fields) and `ite_cond_eq_true`/`_false` per case avoid it. Open numeric
  states: 11.

- **The plain round: plan** (lane L's `Seg.segLaneTwo` and the `max.f32` item are on lane-L
  fe26702a5, not yet on main; a merge of that commit alone conflicts in `Lemmas/DECISIONS.md` and
  adds `Lemmas/Flow/RegionFrame.lean`, `RunFrame.lean`, `RegionSlice.lean`, which duplicate this
  lane's `Proof2/Lib` copies; lane L replaces the copies when it lands, so this branch waits for
  main). The exponent stretch (pcs 6892 to 7415) is cut into generated runs between the 8
  software `exp2` sites and one `Seg.segLaneTwo` piece per site (the plain round's inputs are
  reals; `Seg.segTwoAt` does not apply, `swExp2` being a record update of `segmentExact`). The
  P part's table moves to the generated terms (as `p1Data`), and `StepsPlainEnd` to a generated
  row sum (as `rsum1`), with `afterRound .plain` recording the generated row sum (a Machine-level
  term, as `rs1`); the closed forms `probR`, `rsP` then go. This also cuts `StepsPlainEnd`'s
  walk (758 s). `StepsPlainMax`'s fold becomes a generated run with lane L's `max.f32` item.
  - Done: the five generated runs between the software `exp2` sites (`Gen/Out/softmax_expoP.json`
    → `Gen/ExpoP.lean`: pcs 6892–7089, 7142–7153, 7196–7231, 7274–7285, 7328–7415; each site's
    template ends at the next run's start, the defining one after 31 instructions, the reusing
    ones after 21), outputs the data registers live at each run's end; the module builds.
  - Decision between the two tables, measured on the code: keeping `probR` needs per-lane
    equalities through 5 runs and 8 template pieces (`fma2E`/`mulE`/`ex2E` on `.float` inputs, the
    template lane on `.float`) plus the bf16 packs and store halves added to the table, and leaves
    `StepsPlainEnd` slow; the generated table (as `p1Data`) needs the narr state's values at
    Machine level (`vExpoP`, a separate hunk) and a generated row sum in `afterRound .plain`, and
    replaces `StepsPlainEnd`'s walk by a generated run. Decided: the generated table.
  - Design of the generated table (next): `vExpoP p L g v` in `Machine.lean` (plain-round hunk),
    the values run 0 reads, by key: `1230` `negS`, `5514`/`7256` `maxP`, `1492` `facP`, `7257`
    `.float v.rs`, `8692` the scale word's pair, the score pairs `7431 + j - 4` (j ≥ 4) and
    `8690 - j` (j < 4) as `.pair (.float (score 2j)) (.float (score 2j+1))`; `StepsNarr*` shows
    the arrival state's values equal on run 0's keys (as `vExpo1_eq`). Each template piece
    (`Seg.segLaneTwo`) adds `segValsY` (outputs `.float` of the lane reading; the defining site
    7090 also its constants, which the reusing sites read from the facts); the next run's start
    values are the lookup in those lists, so the table at `pst .plain 0` is run 4's end facts
    (`expoPE`) plus the store halves (as `halvesP1`). Template sites and their lanes, from the
    PTX: 7090 `%r4504`, `%r4505` → `%r4068`, `%r4071`; the others the same shape (the `out_i`
    moves at the template's end name the outputs). `afterRound .plain` records the generated row
    sum (`valR` of the row-sum run's last term, as `rs1`).
  - Done: `vExpoP` (`Machine.lean`); `expoP_start` (`StepsPlainE0.lean`): on run 0's keys the
    arrival state's values are `vExpoP`'s, one kernel-checked list equality per kind of the
    maximum; `expoP0_ok`: run 0's condition and end kinds from the start kinds (`maxP` and `%r170`
    reals, the scale word's pair positive, the score pairs reals).
  - Done: the stretch's values in `Machine.lean` (`expoPS0` … `expoPS7`, `expoPE`): each run's end
    facts over the lookup in the lists before it, and each software `exp2` site's outputs
    (`swOut`, the lane reading `laneR` of the input) with the defining site's constants
    (`cuteConsts`, in the template's order, as `segValsY` writes them). Sites, from the template
    match: 7090 `5564, 5565 → 5128, 5131` (stops 7121), 7121 `5566, 5567 → 5134, 5137`, 7154
    `5580, 5581 → 5140, 5143`, 7175 `5582, 5583 → 5146, 5149`, 7232 `5596, 5597 → 5152, 5155`,
    7253 `5598, 5599 → 5158, 5161`, 7286 `5612, 5613 → 5164, 5167`, 7307 `5614, 5615 → 5170,
    5173`. Lane L's fixture `Tests/Flow/SegLane.lean` shows the piece at 7090.
  - Done: the 8 site pieces (`StepsPlainSw.lean`, `sw7090` … `sw7307`, 23 s with `lean`): the
    lane accepts inputs that read as reals or `-∞` (`lane_ok`), the instance is
    `swMatch pc shape` (the template matcher's slots, `matchAt… : … = some … := rfl`), the
    reusing sites take the constants' facts as a hypothesis. Next: the kinds through runs 1 to 4
    (template outputs are `.float` of `laneR`, kind `fl`), the composition from `narr .plain` to
    `pst .plain 0` (each run framed, each piece on `valueEx (lookupD list) []` facts, restated
    to the next run's start facts by kernel-checked list equalities generic in the values), then
    the P part's table switch with `StepsPlainEnd` on a generated row sum.
  - Done: the kinds through runs 1 to 4 (`StepsPlainE1.lean`, 49 s with `lean`): `kinds_pre` puts
    a prefix of written values (each site's two outputs, `pre2`; the constants without a kind,
    `preNo`; appended, `preApp`) in front of facts whose kinds the previous run's check gives;
    `expoP1_ok` … `expoP4_ok` give the runs' conditions and end kinds.
  - Next, the composition (`narr .plain` to `pst .plain 0`), measured constraints: a template
    site is a segment step, so `SegD.frame` and `SegD.frameR` (both need segment-free positions)
    cannot carry facts over it; the control facts go into the site piece's own `liveS`/`liveT`,
    with `base := lookupD (run's end facts ++ control facts)`. The next run's start facts follow
    from the piece's end facts by a kernel-checked list equality on the run's keys
    (`valueEx base (segValsY …)` against `lookupD (expoPS… p v)`), and the runs carry the control
    facts by `SegD.frame` (concrete lengths). The composition and the P part's table switch go
    in one commit, since the table at `pst .plain 0` is its end.
  - Done: the composition (`StepsPlainE2.lean` run 0 and the sites at 7090 and 7121 and run 1;
    `StepsPlainE2b.lean` the six later sites, 162 s in the strict build, to split;
    `StepsPlainE3.lean` runs 2 to 4 and `expoP_seg`: from `factsD (narr .plain)` at pc 6892 to
    `expoPE p v ++ cHP p L g v` at pc 7416, 21 s). The P part's store unpacks are generated runs
    (`Gen/Out/softmax_pkP.json`: pcs 7417–7424, 7426–7433, 7438–7445; spec `(5749, 5750, 8799)`
    … `(5796, 5797, 8842)`).
  - Next, one commit: `pPData p v := expoPE p v ++` the unpacks' halves (`Machine.lean`, as
    `p1Data`); `valuesData` at the plain P part's states (`Data.lean`, its own hunk) and `dnamed`
    extended to the new keys; `stepAt_narrP` from `expoP_seg` (landing by `valueOfD_prefix`, the
    control facts by `cHP`); the store steps as `stepAt_pst1_0s`, `pst1_1`, `parr1`;
    `StepsPlainEnd` on a generated row sum (`add.f32` of `fl` lanes, `afterRound .plain` recording
    it), since its walk reads the closed forms `probR`.
    The plain row sum (pcs 7466 to 7598) has `mov.b32 %r4746, 0f00000000` at pc 7467, an immediate
    move `Tools/out_gen.py` has no item for: the run is cut there (7466 by itself, the move as a
    `seg_sym` step on two facts, 7468 to 7598 generated). Its first item multiplies the row sum
    before the round by the factor (`%r432`, `facP`: the pattern of one or a real), so the last
    `add.f32` reads `fl` lanes, not `nn` ones (`add_float` needs an `fl` variant).
  - Prepared and checked file by file, not yet committed with its users: `pPData` and
    `unpackSpecP` (`Machine.lean`); `rsPG := valR (Gen.rsumPb_v7598 (lookupD ((5806, 0) ::
    Gen.rsumPa_facts1 (lookupD (pPData p v)))))` and `afterRound .plain` recording it;
    `valuesData` at the plain P part's states `pPData`; `plainNamed` (the run's end keys and the
    halves 5749–5797 but 5781, the `mov.b32 %r4721, 1` control register) in `dnamed`, with its
    `ctl_of_dnamed` case by one kernel-checked list check. Remaining for the commit: the kinds of
    the row-sum runs (run a reads `%r6197` and `%r432`, kind `fl`; run b reads the weights, kind
    `nn` from run 4's end kinds, the template outputs `fl`, `%r4745` from run a and the zero),
    `stepAt_pwend_plain` on the runs (the move at 7467 by `seg_sym` on the run's end facts), the
    walk from 7599 per kind of the maximum (`soft_seg_ite`), `stepAt_narrP` from `expoP_seg`,
    and the three store steps as the first round's.

- **The plain round's numeric states, done** (roadmap A2). The P part's table is the generated
  terms (`pPData`: the exponent stretch's end facts and the store halves); `plainNamed` names its
  registers (5781, a control register amid the halves, excluded). `stepAt_narrP` lands
  `expoP_seg` on it; the stores and the arrival between the store waits run the generated unpacks
  (`StepsPlainP0.lean`, as the first round's); the closing poll (`StepsPlainEnd.lean`) runs the
  generated row sum (`StepsPlainRs.lean`: run a, the move at 7467 by `Seg.writes`, run b; its
  value `rsPG`, which `afterRound .plain` records, from the last `add.f32` of two real lanes,
  whose kinds come from running the kind checker on the last piece's first two items), then the
  loop tail per branch (`pwW_loop`, `pwW_exit`, one walk each, the maximum written as
  `.float (maxR p v)` by `maxP_eq`). The closed forms `probR`, `rsP` are no longer read by any
  step. `StepsPlainE2b` is split into three files of two sites. Open numeric states: 5 (the bias
  round's, lane tmlfa4-bias). Lane L request (immediate moves in `out_gen`) in
  `machine-plan-status.md`.
- **The plain round's maximum is a generated run** (roadmap A2 cuts). `Gen.maxP_run` (pcs 6747
  to 6876, `softmax_maxp.json`, the bias round's `max.f32` rules of `GenRulesB`) replaces the
  fold part of the walk in `StepsPlainMax` (821 s): the walk over the fourth load's packs ends at
  pc 6747 on the facts of the live registers (all control or named, so `liveCut 6747` is the
  table's), `maxP_mid` (`PlainMaxK.lean`) runs the fold with those facts carried (frame region to
  the store at pc 6890, the first event) and states the cut at pc 6877 from the table, and the
  walk from the cut is unchanged. The run's value is the bias round's tree `foldB` (same shape),
  equal on real scores to `foldPT`/`foldPF` (`PlainMaxV.lean`). The two kinds of the maximum
  before the round get one file each: `StepsPlainMax` 44 s, `StepsPlainMax2` 36 s. The row sum
  file is split into run a (`StepsPlainRs`, 33 s) and run b (`StepsPlainRs2`, 50 s), and the last
  two software exp2 sites into `StepsPlainE2d`/`StepsPlainE2e` (32 s, 30 s).
- **The softmax warps' source premise reduces to the bias and score loads** (roadmap A5, D17).
  `SmWarp.expectD_of` (`SmWarp/Expect.lean`) derives the fragment's expected values
  (`Softmax.ExpectD`) at every scheduler site from the scheduler's reference values (`SFits`) and
  the returned values (`SExpect`, `sexpect`): the launch words and the used-K word rebuild to
  32-bit words, the shuffles return 32-bit words, and at the first pass's tile count the chosen
  request's coordinate divisions have rules (`tiles_divOk`, the steps of the output warp's
  `Epilogue.tiles_next`: `picked_of_pre`, `chosen_divOk`; `Mma.coords` and `Epilogue.coords`
  have the same four division operands). What is left is `ExpectRest`: the bias loads' bytes
  (`.bld`, the bias tile the loader's TMA writes to shared memory) and the score loads' `f32`
  payloads (`.sld`, Tensor Memory written by the MMA warp), whose sources are other roles'
  writes (C1 and B2/B3). `Top/SmSrc.lean`: `SmSrcRest` (the premise at those sites only),
  `goodRest` (`SmWarp.good` with it) and `smSrc_of_rest : SmSrcRest → SmSrc` (given also
  `DataSrc`, which places a softmax state on a softmax warp through `good_all` and
  `role_warp`). The field swap in `Top/Safety.lean` (`smSrc` to `smSrcRest`, with
  `smSrc_of_rest` at the uses) is left to the owner of `SafePremises`.
- **`Top/TaddrSoft.lean` after the plain P part's table** (minimal fix of a user of the A2 change):
  `pst_plain_mem` asked that the register is not in `valuesPlainP ++ valuesProbP`, the table the
  plain P stores had before A2; it now asks that it is not a key of `pPData`
  (`lookup_none_of_keys`, the key check by the kernel).

### Remaining steps of the softmax fragment

1. Data plane (18 open states, `D.numeric`), by transferring the old tree's local-run lemmas
   (above) where they fit:
   (a) the exponent stretches after `narr` (3 states): the plain round's from the table's
   `maxP`, the pairs and `%r170` (the `swExp2` segments need a segment piece, above); the first
   and bias rounds' need their elements and maximum at `narr`, which come from the bias
   products; cut each stretch where a large term
   would be carried (as the plain maximum is cut after its fold) and at lane L's boundaries
   (pcs 4594, 4626), one file at a time;
   (b) the probabilities and their bf16 packs named at the P part's states, then the P packs
   (`pst _ 1`, `pst .plain 0`, the delayed stores at sub-step 1, `parr`) and the row sums after
   `pwend` (which also set `mf`, `mr`, `rs` for the next round in `afterFirst`, `afterBias`,
   `afterPlain`);
   (c) done: the bias words as payload-or-masked halves and the 32 bias unpacks; open: the bias
   products in the `bv32` form `mask_max` takes, the masked maximum into `bsync`/`barr` (first
   round) and the bias round's maximum (4 states).
2. `DataStoreSafe` from the table (four-byte values at the stored registers), then the row-sum
   facts (`0 ≤ rs`, and `0 < rs` with a finite maximum).
3. Lane T1 glue, below.

### What lane T1 needs for gluing the softmax fragment

- `Common/Roles.lean`: `Role.softmax`, `frag p L g .softmax := if g % L.block / 32 < 8 then
  Softmax.codeD p L g else stop L g 3102` (the data machine; same states and successors as
  `code`), the gate (shared base, warp word `g % L.block / 32`, warp below 8), `roleOf .softmax
  := .softmax`, exit pc 9205, ledger class `soft (c : Softmax.Cnt)` with `Softmax.cls` (as
  recorded under "Hand-off").
- `Common/Sound.lean`: the hand-off case from `Softmax.handoff` (now about `codeD`'s first facts,
  the same 13 registers); `frag_steps` from `Softmax.stepAt hp hg hw hN d` (`Fragment.lean`),
  whose only premise is `NumSteps p L g` (18 states).
- Following: `Softmax.ok hp hg hw hN hD : (Softmax.frag p L g).Ok` gives `step`, `shape` (table
  `EvS`, no undefined behaviour), `stop_iff`, `ref_next` (with the death clause `next_ends`) and
  `ref_safe`, for the counted machine `MC` (on `codeD`). Named premises: `NumSteps`,
  `DataStoreSafe`. `Expect` has four source obligations: 32-bit words at the scheduler's and the
  request's reads and shuffles, the tile count's `divOk` (from `Epilogue.coords_W`), bias bytes
  that rebuild, and `f32` payloads at the score loads (`TcLdDataflow`).
- `CorrWarp.DataSrc`: its row-sum positivity cannot be supplied for padding rows (above); the
  softmax side will give `0 ≤ rs` and `0 < rs` for rows with a finite maximum. The state now
  records the row maximum and sum before a round (`V.mf`, `V.mr`, `V.rs`, default `-∞` and 0 at
  the first state); the hand-off, ledger, `Ref` and `Expect` are unchanged by them.

## Proof2: the loader warps as a site machine

`Proof2/Loader/Machine.lean` is a `Flow.Code` machine for warps 14 and 15 from their
`setmaxnreg` (pc 179) to the `ret` (pc 9205): 540 sites at 538 program counters (the two
rounds of each page-table and pointer loop share their program counters), and the second
element of each address load at sub-step 1.

- One machine for the three periods of the old tree (priming, warm, steady; 115 `LoaderWarm*`
  files): the period is a site field (`Per`: `prime`, `warm`, `steady`). Every block runs the
  same stretch of sites in its period's code: the page-table loop (`pgLd`, `pgSt`, `rwSt`),
  then per half (`v`) the slot wait, the pointer loop (`ptP`, `ptR`, `ptS`) and the packet
  (`lw`, per row `xl`, `xh`, `cp`, then `commit`, `arrive`). Warp 14's Q and Bias TMA loads are
  seven groups (`tw`, `te`, `ta`, `tc`, `t < 4` in the first block, `t = 4, 5` per warm round,
  `t = 6` after the warm loop). The warm loop counter `%r6114` and the steady counter `%r6121`
  are one field `rnd`: the steady loop starts at the number of warm rounds done, so both count
  the same rounds.
- The scheduler's two passes are the output and MMA warps' arithmetic on other registers
  (recorded in an `Epilogue.D`); the loader's register ids for them were read off the code by
  aligning it with the MMA warp's. The loader reads `%ctaid.x` before its `setmaxnreg` (pc
  174), so the CTA index is a hand-off register as for the MMA warp (`ctaW`), not the code's
  term that the correction lane needed (`ctaR`); the scan sites check in 6 to 10 s each.
- The chosen request's coordinates (`co`) and the tile's setup words (`su`: the K/V head bases,
  the page-table row, the block counts) are recorded in the state at the transition that
  computes them (`afterTiles`, the used-K read). Stated as terms of the scan words, every later
  site's table repeated the coordinates' two floor divisions inside every setup word, and the
  first page-loop family did not finish in ten minutes; as fields, the later sites' terms are
  small. This is rule M2 with the closed terms named once: the table still mirrors the code
  from the recorded values, and the fields' values are conjuncts of `Ref`.
- The machine follows every value: a load or shuffle of a 32-bit word records it and a value of
  another kind stops the machine (`some none`). A pointer round's page and row loads
  (`ld.local.s32` into a 64-bit register) are located by `accessLoc` (`locSpace?` is `none` for
  `.local`), so Core sign-extends them (`extendLoaded`); the machine records the word.
- Proved (`Steps*.lean`, by `site_cases`; `Steps.lean` combines them as `stepAt`): every state.
  The families: the `setmaxnreg` and both scheduler passes, the choices, the request's
  offsets and the used-K read (whose segment computes the tile's setup), the three periods'
  page-table loops, the six slot waits, the six pointer loops (page and row loads, address
  stores), the twelve address loads (both elements), the six packets' rows, commits and
  arrivals, warp 14's seven TMA groups, and the drain and exit.
- The first block's V arrival (`StepsArrPrime.lean`) is the transition into the later blocks: its
  segment computes the later blocks' first block (`%r56 = %r28 - 2`, an `add.s32` with the
  immediate `-2`) and branches on terms built from it. The transition is split at pc 909, after
  `%r56` and the first branch's predicate are computed: the first part (`seg_auto`) ends in the
  arrival's table extended by those four registers (`cutRegs`), with `%r56` as the term
  `addi r28 (-2)`; before the second part (`seg_sym`) that term is generalized to a free word in
  the start facts and in the successor (whose `V.r56` is the same term), so the walk and every
  condition it decides read `%r56` as a recorded word and never evaluate the literal. The
  machine is unchanged; `stepAt` has no exclusion hypothesis. With lane L's `try_rt` (edc9fd0d7) the unsplit
  walk (`load_step` on this state) still fails, after 298 s: the runaway is now reported as a
  failure of each `site_step` alternative instead of aborting, but no alternative closes the
  segment, so the split stays. Check time 156 s for the one state
  (over 15 s: it walks every successor, the warm rounds, the last Bias block, the steady rounds
  and the scheduler's second pass).
- Check times (one `lean` per file, run in parallel on the loaded host): scan rounds 6 to
  10 s per site, choices 28 s, used-K read 68 s (one site, over 15 s: it walks the setup), page
  loops 2 to 9 s, slot waits 5 s, pointer loops 2 to 18 s, address loads 4 s, K packet rows
  about 11 s per site in the warm and steady blocks (680 to 720 s for 64 sites), V rows 3 to
  4 s, commits and arrivals up to 76 s per arrival site (the arrivals end a half block and walk
  into the next round or the second pass; over 15 s), TMA groups 2 to 30 s.
- Merge of lane L at c292de7d2: `Proof2/Lib/CpAsyncSteps.lean` and `Proof2/Lib/TcSteps.lean` are
  deleted (promoted as `advances` rules in `Lemmas/Flow/IssueNext.lean` and as
  `Lemmas/Flow/Step/TcSteps.lean`); the correction warps import the promoted module; the
  packets' copies check with plain `load_sites`.
- Tables of the later blocks: `valuesWarm`/`valuesSteady` (the round, ring, Bias parities, the
  lane's row and column offsets), `valuesPgWarm`/`valuesPgSteady`, `valuesWarmK`/`V`,
  `valuesSteadyK`/`V` (row bases, slot destinations, the next slot and parity of a V half),
  `valuesPt` (the pointer loops), `valuesTma` (the seven groups' barriers, coordinates and
  tensor maps). New recorded words: `len` (the rows of a warm or steady block, recorded at the
  code's `selp`) and `r56` (recorded at the end of the first block). The page index is the code's
  multiply-high division with Core's `cvt.u64.u32` (`zext` is `truncBits 64 (r32 x)`).
- Evaluation that runs away. A term that adds the 32-bit pattern of a negative immediate to a
  recorded word (`addi x (-2)`: `+ 4294967294`) recurses through the literal when evaluated
  (`Nat.ble` against `Nat.succ`, millions of steps). Library tactics evaluate such terms: the
  `change` of `site_norm` at a conditional successor, `rfl` of a successor's sub-step, `sym_close`'s
  first `rfl`, `seg_fp`'s evaluation of a segment; their runtime exceptions escape `first`.
  Decisions, all in this lane's files: (1) the later blocks' conditional successors (`D.iteS`)
  are a structure whose sub-step is 0 without deciding `c` (the scheduler's successors keep
  `D.ite`, an `if`); (2) `%r56` is a recorded word (`V.r56`), so the later blocks' terms
  have no such literal; (3) the conditions of the later blocks' successors are opaque
  constants `geW`, `ltZ` (`@[irreducible]`; `geW_eq`, `ltZ_eq` are stated over variables, so the
  kernel checks them without evaluating), and the role's `sym_decide` rule (`opaque_decide`,
  `Loader/Base.lean`) decides the code's branch from the case split's hypothesis by unification,
  skipping other hypotheses and catching runtime exceptions (`decideBool` runs `sym_decide` in a
  budget of 400 thousand heartbeats); (4) definitions whose bodies hold these conditions use `if`
  on the period, not `match` (the equation lemmas of the `match` forms timed out); (5)
  `load_seg` runs `seg_fp` under `catch_rt` so that `seg_sym` takes a segment whose evaluation runs
  away.
- Shape table (`Shape.lean`, `Ev`; proofs `ShapeSites.lean`, `ShapeRowsPrime/Warm/Steady.lean`,
  assembled with the return kinds in `ShapeAll.lean`: `shape`, `ret`, `stop_iff`). Every site
  has an entry: the scheduler's sites are the output warp's `Epilogue.Ev`; the reads of global
  memory, the local stores (with the stored word's bytes), the local loads (element `k` of the
  two-word address load at sub-step `k`), the shuffles (source lane `i mod 8`), the `cp.async`
  copies (source and swizzled destination; some source size), the commit, the copy arrival on
  the slot's full barrier, the polls (address and parity), the elections (with the site's pc),
  the expect-tx arrivals and the tensor copies (with their barrier). Operands are the table's
  words at the state (`rv d r`, the register's value in `values`), with per-site register tables
  read off the code (`waitRegs`, `arrRegs`, `taRegs`, `tcBar`, `cpDst`, `xSrc`, `lwBase`,
  `ptRegs`, `pkRegs`). Undefined behaviour is admitted where the template admits it (global
  reads, stores, copies, elections, tensor copies); the local loads, polls and arrivals have
  none, since their addresses are proved aligned.
- Proofs by `site_shape` (`load_shape`) with families as theorems, and by `load_with lemma` for
  two classes whose library lemma does not fit: a `cp.async` whose source size is a `selp` on a
  symbolic condition (`shape_cpAsync` needs the size's value; `shape_cpAsyncN` states the copy
  with some size) and a tensor copy (`shape_cpTensorAt` names the barrier the table gives). The
  role's address facts: a local address is `L.localBase` plus a constant, aligned because
  `L.localBase % 32 = 0` (`Pre.localMemory`; `lb_mod4`, `lb_mod8`, with the table's
  `add64`/`wideU4`/`shl64` terms normalized by `add64_ofNat`, `wrap_ofNat0`, …); an mbarrier
  address is the shared base plus multiples of 8 whatever the ring slot's word (`mbarLoc_reg`,
  `trunc_add_mod8`, `load_m8`: `Pre.shared` gives `sharedBase % 1024 = 0`).
- Lessons for `site_shape` on a large table: simp must not unfold `reqAddr`-style definitions
  whose `match` has a wildcard over the site type (equation-lemma generation timed out); a
  table entry that does not match the computed operand (a wrong register in `cpDst`) is not a
  quick failure but a slow `rfl` (minutes per site), so the per-site register tables were read
  off the decoded program with a script and checked against it.
- Library candidates for lane L (`Proof2/Lib/ShapeAsync.lean`): `shape_cpAsyncN`,
  `shape_cpTensorAt`, `mbarLoc_bits`, `mbarLoc_reg`, `trunc_add_mod8`. Requests: `site_shape`
  should take `shape_cpAsyncN` when the source size is not decided, `shape_cpTensorAt` for a
  tensor copy, and an mbarrier address register whose alignment needs a role fact (the hook
  `addr_by` sees a goal `mbarLoc … = .ok ?m`; `mbarLoc_reg` turns it into a register read and an
  alignment fact).
- Check times (one strict build, the four proof files in parallel): `ShapeSites` 81 s, each
  `ShapeRows*` about 90 s (128 sites), `ShapeAll` 102 s (mostly `stop_iff`); 764 lines with
  `Lib/ShapeAsync.lean`.
- Reference invariant (`Ref.lean`, `RefRows.lean`; the ledger is `Ledger.lean`, lane L's
  `Code.counted` on the machine). `RefRing` now reads the site through its class (`ringCls`:
  warm, steady, the last Bias group, the drain, other), so `refRing_congr` moves it along every
  step that keeps the class and the ring words. Correction of the statement: the copy-arrival
  count of a state is `ringCnt (arrAt s r A)`; the earlier `arrAt + (inPkt s).2` counted the
  pending arrival at the `arrive` site, where only the commit is done (found by the proof of the
  commit step).
- Proved: `ref_step_rows` — a step of the counted machine from a state inside a packet (address
  loads at both sub-steps, shuffles, copies, commit: 402 of the 540 sites) on an event of the
  state's shape that is not undefined behaviour keeps `RefRing` and `RefCounts` (4 s); and
  `next_ne_stop`, the first conjunct of `ref_next`, from `stop_iff`.
- Not proved yet (next steps of T2c, in this order): (1) the quiet steps of the page and pointer
  rounds (local loads and stores, counted by no class; the round ends move the site within its
  class); (2) the slot waits (a successful poll adds one acquisition of slot `k mod 3`: needs the
  poll's address word `emptyAt L v.slot` read as `bl L g (56 + 8 (k mod 3))` from `RefRing`'s
  slot word, as the MMA warp's `smLoc_slot`); (3) the copy arrivals and the ends of the halves and
  rounds (`roundV`: slot and parity two packets on, `rnd + 1`; the warm/steady exits compare
  `rnd + 1` with `warmRounds` and `r31`); (4) warp 14's TMA groups (won elections, expect-tx
  arrivals and tensor copies, with `ExpectElect` as the MMA warp's); (5) the drain; (6) the
  fragment (`Fragment` with `Ref := ∃ r A, RefRing ∧ RefCounts`, `Expect` the return kind and
  the elections) and `ref_next` by cases on the site, as the MMA warp's `RefNext.lean`.
- Reference invariant (`Ref.lean`; the ledger is `Ledger.lean`, lane L's `Code.counted` on the
  machine): `Ref p L g w dn := ∃ k A, RefRing p L g w dn.1 k A ∧ RefCounts L g dn k A`, with `k`
  the packet of the current warm or steady block's K half and `A` the packets of the tile.
  Decision (this round): the counts and ring words are stated over packets, not over the round
  counters. The earlier statement used the rounds done `r` (packet `2 + 2 r`) with the bounds
  `r < W`, `W ≤ r ∧ r + 1 < B` and `r = W`; keeping them needs the setup's relation
  `r31 = r28 - 1` and a bound on the blocks (`r28` can be any 32-bit word as the machine sees it:
  with `r28 = -2^31` the warm loop is skipped and the steady counter starts at 9), so their proof
  is arithmetic over the whole setup. The counts need none of it: the round counters only decide
  how many packets there are, which matters for progress (lane T2's T4 adds a bound conjunct
  when it needs one). `k` moves to 2 after the first block and by 2 at a round's end; `A` is fixed
  when the rounds end (`k` and `A` both the next packet; 0 when the first pass finds no tile).
  - `RefRing`: the TMA groups run on warp 14; by class (`ringCls`): the first block's V half has
    `bq0 = (w = 14 ? 0 : 1)`; warp 14's first four groups have `bq0 = 1` (0 after the fourth
    group's last election); a warm round has the ring words of packet `k` (`SlotIs`), `bq0 = bq1`
    and `bq0 = (w = 14 ? (rnd + f) mod 2 : 1)` with `f` set past the round's second Bias group; a
    steady round and the last Bias group have the ring words of packet `k`; the second scheduler
    pass and the drain those of packet `A`.
  - `RefCounts`: unchanged in form, with the second scheduler pass at `A` packets (the earlier
    table gave its sites 0 acquisitions) and `cls .copy` counting the tensor copies
    (`tensorIssue`) with the linear ones: the table's copy count adds the won elections at the
    tensor copies, and a `tensorIssue` event is not a `.copy` event in Core.
- Proved (`RefBase.lean`, `RefRows.lean`, `RefStepScan/Block/Arr/Tma.lean`, `RefNext.lean`):
  `ref_init`; `ref_step`: every step of the machine from a state satisfying `Ref` on an event of
  the state's shape that is not undefined behaviour leads to a state satisfying `Ref` (warps 14
  and 15); and `ref_next`, the obligation in the form of the correction lane's: under `Ref` and
  `Expect` (the returned value has the site's kind, `(ret d).accepts e`), such an event neither
  stops the counted machine nor leads to a state that breaks `Ref`. The steps: the counts move by
  `counts_frame` (an event counted by no class `RefCounts` names), `counts_acquire` (a successful
  poll of the empty barrier of packet `j`'s slot), `counts_publish` (a packet's copy arrival),
  `counts_won` (an election the lane wins makes its arrival or copy pending), `counts_tmaArr`,
  `counts_tensor`; the barrier locations are `smLoc` of the shared base plus `8 (j mod 3)`
  (`smLoc_empty`, `smLoc_full`, from `Pre.shared`); the ring words two packets on by
  `slotIs_roundV` (`nslot`, `npar` of the code).
- Local stores (for the sources of the local loads). The ledger counts the lane's local stores
  per offset (`cls (.lst o)`: a `.wr` whose location is `⟨.local, g, L.localBase + o⟩`), and
  `RefCounts`' last conjunct gives the count at each of the eight offsets (`lstOffs`) in closed
  form (`lstAt`): per block the lane stores the page and row of page round 0 (96, 64) and round 1
  (100, 68), then the K half's two row addresses (0 and 8 in the first block, 32 and 40 later),
  then the V half's (0, 8). The closed form needs `2 ≤ k` in a warm or steady round (a conjunct
  of `RefRing`'s warm and later classes: `k` starts at 2 and grows by 2), since the stores at 32
  and 40 before later block `b` are `b - 1`. `Local.lean` gives the locations of the pointer
  rounds' loads (`ptP_loc`, `ptR_loc`; the packets' loads by `Ev` with `lwBase_val`) and that the
  count at the loaded offset is positive (`lst_ptP`, `lst_ptR`, `lst_lw`).
- What lane T1 uses to follow warps 14 and 15 (`good`), in the form of the correction warps':
  the counted machine `MC p L g w ent` (`code … |>.counted (cls L g)`), `Loader.Ref p L g w`,
  `Loader.Expect`, `Loader.ref_init`, and `Loader.ref_next hp hw hi hJ hE hev hub` (`hw : w = 14 ∨
  w = 15`, `hi` the machine's invariant). The words the loads return: the scheduler's as for the
  other warps, the request's and the page table's from the launch (read-only input), the local
  loads' by lane L's `Frame.local_read_of_last_store` (merged with `p4b-epilogue-wire` 7951d3f13;
  `LocalOwned` is the kernel's `localWriteOwner`): the store is the lane's event at which the
  count `lst o` of the load's offset reached its value at the load (`ledger`), and no store at
  that offset lies between, since the count does not change. `Expect` asks only for the kind (a
  32-bit word): every local store is a 4-byte word (`pgSt`, `rwSt`) or an 8-byte address (`ptS`)
  of which a packet loads one 4-byte element, so the returned bytes rebuild to a 32-bit word.
- Conditional successors (`D.ite`, `D.iteS`) are split by `ref_ite`/`ref_iteS` without unfolding
  their conditions: splitting the unfolded successor of the second pass's scan loop took 428 s for
  one site family (the `if`s inside the scheduler's words), by `ref_ite` the whole scheduler file
  checks in 4 s. No `contradiction`/`simp_all` on large terms.
- Not proved here: the death clause of `Fragment.OkAt.ref_next` (`next = none → Ends e`): the
  machine dies at a read whose bytes do not rebuild (`rebuild 3 bs = .error`), which `Expect`
  (kind only) does not exclude, and at the scheduler's division without a rule (`afterTiles`);
  and `ref_safe`. The correction lane's `ref_next` has the same two conjuncts.
- Hand-off (`Handoff.lean`, after the merge of lane T1's `ps-merge15`): the fragment is
  `Loader.F p L g b` (`code p L g (wOf b) (ent p L)`, no `ent` argument left: `ent` gives the
  startup's values of the six registers live at pc 179 that the warp never reads). The warp
  index is the value of register 1062 that the dispatch compared, and the step proofs need it to
  be 14 or 15 (`warp_facts`: the walk back to the common return passes the dispatch's tests), so
  the fragment is indexed by `b : Bool` with `wOf b = if b then 15 else 14`. Exported:
  `Loader.steps hp hg b d : (F p L g b).StepAt d` (every state), `Loader.live_179`,
  `Loader.init_facts` (the first state's 32 register facts) and `Loader.handoff hp hg b hF`: a
  thread state holding `Startup.facts p L g ⟨.enter .loader, ofNat sharedBase, x2, ofNat (wOf b)⟩`
  holds `(F p L g b).facts (F p L g b).init` (the shared addresses by `addi_sb`, the CTA index by
  `cta_word`, the thread index by `tid_word`, the batch by `batch_word`; local copies of
  `Common/Sound.lean`'s lemmas, since the loader may not import lane T1's files).
- What lane T1 adds in `Proof2/Common` (not done here; `Common` is lane T1's):
  - `Roles.lean`: the constructor `Role.loader (b : Bool)` (warps 14 and 15, entry pc 179, exit
    pc 9205, return kind a 32-bit word at every value-returning site), `frag p L g (.loader b) :=
    Loader.F p L g b`; the startup's exit at `.enter .loader` enters `.loader false` when
    `x1 = sharedBase ∧ x3 = 14`, `.loader true` when `x1 = sharedBase ∧ x3 = 15`, else
    `.stub .loader` (the gate fixes the warp word, so `roleOf` needs the state, not only the entry);
    `loaderDecl` and the loader's site list are already in `Roles.lean`.
  - `Sound.lean`: `frag_steps` case `.loader b => Loader.steps hp hg b d`, and the `handoff` case
    `.loader`: from the gate, `⟨hpc, hs, ha, hf, Loader.handoff hp hg b hF⟩` and `inv` by
    `Or.inl rfl`.
- Library code written here for promotion by lane L: `opaque_decide` (`Loader/Base.lean`; lane L
  keeps it here, since it unfolds this role's opaque conditions). Merge of lane L at edc9fd0d7:
  `catch_rt` is lane L's `try_rt` (`Lemmas/Flow/TryRt.lean`), used by `seg_fp`, `sym_close`,
  `site_norm` and `site_step`; `Proof2/Lib/CatchRuntime.lean` is deleted. The `sym_decide`
  budget is the option `seg_sym.decideHeartbeats`.
- Merge of `ps-merge15` (lane T1's `Proof2/Common`) after lane L's edc9fd0d7: the
  `Proof2/Correction` and `Proof2/Mma` files are `ps-merge15`'s (no conflict in
  `Correction/Base.lean`; `Mma/Ledger.lean` taken from `ps-merge15`); lane L's test
  `Tests/Flow/SiteFamily.lean` is kept (it is on `lane-L`, which this branch merged, and builds).
  Every Proof2 target builds except `Proof2/Mma/Warp.lean` (lane T1's): lane L's 84cb4b9b2 changed
  `RetKind.accepts` to read `recvAll`, and seven `simp only [Flow.recv, …]` steps there make no
  progress. That file is lane T1's; it needs `Flow.recvAll` in those steps when T1 takes lane L's
  round 6.
- Status after this round: `Proof2/Loader/` is 3712 lines (machine 1.3k, steps 1.0k, shape 0.7k,
  hand-off 0.15k, reference invariant 0.3k) plus 82 lines of `Proof2/Lib/ShapeAsync.lean`,
  against the old Loader family's 106k. The full strict build passes except lane T1's
  `Proof2/Mma/Warp.lean` (the `recvAll` change above); `Tests/Kernel` statements and contract,
  pytest, `reading_uses --lean`, the axioms of `TmlFa4Fwd.correct` (`propext`,
  `Classical.choice`, `Quot.sound`) and the trusted-file diff are clean.
- Projection for the whole Loader fragment, from the measured parts: the machine 1.3k lines
  (written), step files 0.9k (written), shape about 0.5k, hand-off about 0.4k, reference
  invariant and sources 2 to 4k (est.): about 5 to 7k lines against the old family's 106k.
- Status after the round of `ref_next` (T2c): `Proof2/Loader/` is about 5.5k lines (machine
  1.3k, steps 1.1k, shape 0.7k, hand-off 0.15k, reference invariant, ledger and local stores
  1.75k) plus 82 lines of `Proof2/Lib/ShapeAsync.lean`, against the old Loader family's 106k.
  Check times of the reference-invariant files (one strict build on the loaded host): `RefBase`
  7 s, `RefStepScan` 3 s, `RefStepBlock` 11 s, `RefStepTma` 18 s, `RefStepArr` 56 s, `RefRows`
  6 s, `RefNext` 2 s, `Local` 4 s.
- Merges of this round: `p4b-epilogue-wire` at 843d00467 (ae6b12288; the full build failed on lane
  T1's `Proof2/Lib/WaitReg.lean`, a copy of lane L's promoted `fires_wait_reg_al`), then at
  7951d3f13 (which deletes that copy and brings lane L's local-memory source 7bdc0a125): the full
  strict build passes.
- The slowest step files are split so that their halves check in parallel (the theorems that
  `Steps.lean` uses are unchanged): each K packet's rows into the low-word and high-word shuffles
  (`StepsRows*KL`, `StepsRows*KH`, dispatched by `StepsRows*KS`) and the copies
  (`StepsRows*KC`), the commits and arrivals into `StepsCommit`, `StepsArrWarm`,
  `StepsArrSteady`. Before the split, on the loaded host of this round: K rows 1196 to 1289 s
  each, `StepsPkEnd` 873 s. After it (same host): the high-word shuffles 857 to 945 s (about 55 s
  per site: their segments run through the row's copies), the low-word shuffles 14 s, the copies
  172 to 179 s, `StepsArrWarm` 457 s, `StepsArrSteady` 178 s, `StepsCommit` 9 s. The longest file
  is now a high-word shuffle file; splitting it by rows (`i < 8`, `i ≥ 8`) is the next cut.


### Correction step files: the tensor-load condition on a code slice, seg_sym first, step lemmas (lane L, 2026-11-22)

- Profile of `StepsRescale` (lane L): 21.7 of 35 s of `stepAt_rld` was the kernel checking
  `corr_rld`'s `rw [Assumptions.all_tcLdWait]; kernel_rfl`, about 1.4 s per site: `ldConsumedAt
  kernel pc` reads `kernel.code[pc]?` and scans `kernel.code.drop (pc + 1)`, walking the code from
  its head at every load. `Correction/Loads.lean` now states the code from 7744 once as the
  decoder's chunks (`corrCode`, `corr_tail` by one `kernel_rfl`) and the condition on that slice
  (`tcLdWait_at`, through the library's `Flow.ldConsumedAt_eq_in`); `corr_rld`, `corr_rldw` and the
  third site use `corr_wait`.
- `Correction/Base.lean`'s `lands_auto` tries `seg_sym` before `seg_auto` (the library's rule walks
  first since lane L round 13; the old order evaluated a doomed `seg_auto` at every landing).
- Every `Correction/Steps*.lean` imports `Kernels.TmlFa4Fwd.Gen.StepCorrection` (the per-pc step
  lemmas, lane L fe2a65851).
- Measured (CPU s, the same files before and after in this tree; load 100–190 before, 50–140
  after): `StepsRescale` 390.0 → 87.7, `StepsFinalData` 323.2 → 94.4, `StepsTiles` 163.4 → 19.8,
  `StepsScanFirst` 163.5 → 33.6, `StepsReq` 125.1 → 41.4, `StepsLse` 18.5 → 3.8.
- `Correction/Shape.lean` has the same `all_tcLdWait; kernel_rfl` four times (lines 179–217); it is
  being edited by lane L2 and is not changed here — it can use `corr_wait` / `tcLdWait_at`.
### Bias round numerics (branch tmlfa4-bias, ex-FlashMLA agent)

- Generated runs, both checked: the products `Gen/ProdB.lean` (pcs 5279 to 5534, 8 pieces, from
  `Gen/Out/softmax_prodb.json`; 17 s) and the maximum `Gen/MaxB.lean` (pcs 5536 to 5665, the
  unpacks and the two- and three-operand `max.f32`, output `%r3500`; 5 s).
- `Softmax/GenRulesB.lean` (new file, so that `GenRules.lean` keeps one owner): `rule_widenB`, the
  widening reading with the arithmetic site test `widenB` (pcs 5279 to 5534, first two of every
  four) in place of `biasWidenSites.contains`, whose elaboration walks the 256-entry list and
  exceeded the generated file's default recursion depth at the list's second half (pieces at pcs
  5439 and later failed; with `maxRecDepth 4000` the same file checked). The membership of every
  `widenB` pc is checked once by the kernel (`widenB_all`). `rule_max2`/`rule_max3` copied from
  lane L's test readings onto `formsMax` (the kernel's ideal reading of `.max .f32`, which is in
  `arithScope`).
- Next, in order (not started): (1) `StepsProdB.lean` as a transform of `StepsProd1.lean`: halves
  base 914 (`halvesList true`), score pairs 7367 + j (`valuesPairs .bias`), state `.barr true`, run
  `prodB` with 8 pieces (`prodB_facts0` … `prodB_facts8`, `pL1` … `pL8`); the scale pair 7896 is a
  start value of the bias table (`valuesBias`), so the start kinds need a kind for the pair of
  `pw` words in place of `(7135, .s .pw)`, and `prodB_pairs`' rewrites use `prodB_v<pc>` with the
  first group at pcs 5279 to 5282 (no scale move) and four pcs per group after it. (2) The
  barrier step: the control instruction at pc 5535 (`%p632`) by `seg_sym`, `maxB_run` from the
  products, then pcs 5666 to 5681 (keep test, factor, statistics address) per kind of the
  maximum before the round (finite or `-∞`, as `StepsPlainMax`), ending at `stat false`; the table
  at `stat false` must name `%r6196`, `%r302` and the factor's terms. (3) `narr .bias` (exponent
  stretch, branch at pc 5815; `Seg.segLaneTwo` at the eight `swExp2` sites), (4) the P part by
  `stepAt_lift`, (5) the closing poll, then `DataStoreSafe` and the row-sum facts.
- Step 1 done: `StepsProdB.lean` (0d9dcd383, 30 s): `prodB_ok` (the run's condition by the kind
  checker; the scale pair 7896 is a start value of kind `.pr .pw` by `join_has`) and
  `prodB_pairs` (the 64 products at pc 5535 as `bvl (bpf v n) (bps p v n)` pairs, the same closed
  forms as the first round's), generated from `StepsProd1.lean` by a script.
- Step 2 (the barrier step to `stat false`), findings before writing it:
  - The state `stat false` (pc 5682) names none of the round's new data registers: `dnamed`
    excludes the products 8317 to 8443, `%r302` (1362), `%r3505` (4565), and `%r6196` (7256) is
    named only from pc 6661. So the step to `stat false` alone needs only the control facts, but
    `narr .bias` then has nothing to compute the exponents from. The bias tables must be extended
    first (`dnamed` for those registers in the bias round's pcs; `valuesData0` at `stat false`,
    `narr .bias` and the bias P part with the products, the maximum and the factor), as
    `valuesPlainP` does for a plain round, written per kind of the maximum before the round
    (`v.mf`) and with the keep test in the walk's comparison form (as `keepP`).
  - The maximum's value: `Gen.maxB_run` needs `Gen.maxB_cond`, and the kind checker
    (`Lib/OutKinds.lean`, `kItem`/`XItem.FnOk`) has no `max.f32` item (a two-source `fn` is read
    as a pack). Either add a `max` kind rule there (`ni`/`fl` operands, the result the larger
    kind; `FnOk` must tell `maxE` from `packE` by the item's `Op`), or prove the condition and the
    value (`erealValue .f32 (foldB (mxE v) (bpe (bpf v) (bps p v)))`, `foldB` the tree of
    `Gen.maxB_v5537` … `maxB_v5665`) by a generated chain of `maxE` equations from
    `readEReal_erealValue_f32` and `bvl_read` (no kind checker). The keep test (pcs 5666 to 5681)
    then walks per kind of the maximum (`⊥` or finite, as `sel_max`).
- Step 2 (the bias barrier step to `stat false`):
  - `Lib/OutKinds.lean` (b6096e95f, additive): a `max.f32` rule — an `XItem.fn` whose op is a
    `.float` instruction with two or three sources is a maximum (`SK.maxK`: `fl` when every
    source is at most `fl`, else `ni`; `FnOk` asks `MaxSpec`, met by `maxE_maxSpec`); the pack
    rule (non-float two-source items) is unchanged. `kItem_sound` splits on the op first.
  - `Data.lean` (11cba3ddd): `dnamed` is `dnamed0 || biasNamed` (products 8317 to 8443, `%r302`
    1362, `%r3505` 4565, `%r6196` 7256), `liveF` names them in pcs 5682 to 6558, and
    `valuesData0` states them at `stat false`, `narr .bias` (`valuesBiasM`, `valuesProdB`) and
    in the bias P part (`valuesBiasM`). `valuesBiasM`'s entries are `bif v.mf` per entry (a
    literal spine): with a `match v.mf` around the list, `StepsBiasCtl`'s walks could not read
    the entries for an opaque `v` (they failed at `pwst .bias 0`); with `bif` they carry them
    unchanged (`StepsBiasCtl` 71 s, unchanged file).
  - `BiasFold.lean` (`foldB`, the code's tree), `BiasMax.lean` (`maxB_value`: the generated
    term is `erealValue (foldB x0 e)`, one `simp` with `maxE_er2`/`maxE_er3`), `StepsMaxB.lean`
    (`maxB_ok` by the kind checker, `maxB_val`), `StepsKeepB.lean`/`StepsKeepB2.lean` (the keep
    test: one walk for a finite maximum before the round onto the table, and for `-∞` before
    the round one walk each for a finite fold and for `-∞` (every half masked), onto the table
    with the three written registers updated (`keepW`), since a walk onto an explicit list of
    another live function fails (`seg_fp: not a list literal`, G29)). `StepsBarrB.lean`: the
    chain 5279 → 5682 (`chainB`) and the steps `stepAt_barrB`, `stepAt_bsyncB`.
- Step 3 (the exponent stretch at `narr .bias`, pcs 5684 to 6507), generated and checked so far:
  `Gen/ExpoB0.lean` (5684 to 5814: the subtracted maximum times `-s`, the products' `fma2` with
  the scale pair, the 128 unpacked exponents `%r303` … `%r430`, ids 1363 to 1490),
  `Gen/ExpoBA.lean` (the hardware path 5816 to 5975, ending at the `bra.uni` to 6299; outputs
  `%r6192` and the 64 packed pairs ids 9541 to 9604), `Gen/ExpoBB.lean` (the software path's
  nine runs between the template segments: [5977, 6059), [6090, 6091), [6112, 6131),
  [6152, 6153), [6174, 6193), [6214, 6215), [6236, 6255), [6276, 6277), [6298, 6299); outputs
  every data register live at each run's end). The template segments: 6059 → 6090 (the defining
  31-instruction shape) and 6091 → 6112, 6131 → 6152, 6153 → 6174, 6193 → 6214, 6215 → 6236,
  6255 → 6276, 6277 → 6298 (the 21-instruction reuse shape); each is one `Seg.segLaneTwo`
  piece (`Tests/Flow/SegLane.lean` is the pattern: `cuteExp2.matchAt kernel pc = some m` by `rfl`,
  the lanes by `swExp2Lane` of the exponent values, `0` for `-∞` by `swExp2Lane_negInf`).
  Open: the glue between the generated facts lists and `segLaneTwo`'s `factsFrom live
  (valueEx base ex)` form, the branch at 5815 (`%p632`, both paths), the common tail 6299 to
  6507 (another generated run), the values (`ex2` of `s · product - s · max`, as
  `expoE`/`p1Data` for the first round) and the P part's tables (`valuesData0` for the bias P
  part must then name the weights and packs, as `p1Data`).
- Step 3, continued (A3): `StepsExpoB0.lean` (3717e9ae7, 18 s): the scaled-product run's
  condition and the kinds after it (exponents `ni`) by the kind checker; the stretch's values
  stay the generated terms, as the first round's `expoE`. `SwExpB.lean` (0669f130c): `laneY` (a
  lane's reading; `laneY_spec` from `SK.ni`) and `seg_swExp2`, one software `exp2` instance from
  facts of any `W` (`factsFrom keys W`) to `factsFrom liveT (valueEx W (segValsY m y0 y1 (laneY
  (W x0)) (laneY (W x1)) ++ []))`. Checked at 6059 against the generated runs (16 s): the
  match is a definition `mB<pc> := (cuteExp2.matchAt kernel pc).get (by rfl)`, the side
  conditions are `decide +kernel`, and the key lists must be written on a dummy value function
  (`(Gen.expoBB0_facts3 fun _ => .pred false).map Prod.fst`) so that `decide` sees no free
  variable. The template constants (registers 8511, 8515, 8516, 8518, 8520, control registers
  by `ctl`) are now outputs of the software path's runs, so the reuse instances' `hcst` reads
  them from the facts.
  - Next: the chain of the software path as one generated file: value functions `vBB0` (the
    run-0 start, the scaled-product run's end) and `vBB(k+1) := valueEx (lookupD (Gen.expoBBk_facts_end
    (vBBk))) (segValsY mB<site_k> y0 y1 …)`; per run the kind chain (`kpiece_lit`) with start kinds
    `kList keys (fun r => if r is an output of the instance then .s .fl else kOf <previous end> r)`;
    per instance `seg_swExp2` with the lane kinds from the previous end kinds. The hardware path
    (`Gen.expoBA`) is one kind chain. The branch at 5815 picks the path by `%p632`; the P part's
    tables then name the packs as `bif (scmp .lt .u v.bt (r301 p L g v))` of the two paths'
    terms.
- Step 3, done for the exponent stretch and the P part (A3). `BiasExpoVals.lean`: the template
  matches `mB<pc>` and the software path's value functions `vB0`..`vB8`, `nextTA`/`nextTB`.
  `Data.lean` (bias hunks only): `vExpoB` (the scaled-product run's end), `vTailB` (per path, a
  `bif` on `%p632`'s test so that the table spine stays literal), `tailB` (the tail's end facts),
  `unpackSpecB`/`halvesB` (the 24 unpacks before the second to fourth P stores), `pBData`; the bias
  P states' table is `pBData`, and `biasNamed` names its keys. The unpack with a sink at pc 6380
  (`mov.b64 {lo, _}`) is not an `out_gen` instruction: it is `exec_unpackLo` plus `Seg.rule1`
  between the tail's two runs, and the tail is one run pair per path (`Gen.expoBTA*`,
  `Gen.expoBTB*`), because the pair's kind is the maximum of its halves' kinds and only the low
  half (`%r3607` on the hardware path, `%r3650` on the software path, both outputs of the runs
  before) keeps `ni`; `split_join_lo` reads the low half back from its clean value. The software
  path's runs carry the 25 control registers live at 6299, so `ctlTail` (6299 to 6307) starts from
  their end facts without a frame across the template instances (`seg_frame` cannot frame a
  stretch that contains `swExp2Sites`). Steps: `stepAt_narrB` (`StepsNarrB.lean`, the branch by
  `Seg.pred_ex` on `%p632`, then `narrB_pathA`/`narrB_pathB`), `stepAt_pstB_0s`, `stepAt_pstB_1`,
  `stepAt_parrB` (`StepsPB.lean`, `StepsPB2.lean`, from `StepsP1.lean`'s pattern), and the
  control sites of the P part lifted from the control machine (`StepsBiasPCtl.lean`,
  `StepsBiasP.lean`). `StepsBiasCtl.lean` needed one minimal edit: its
  site list keeps only the polls (`ws .bias`, `wb true`, `fence true`, `stat false`, through
  `StepsBiasCtlPoll.lean`), and `StepsBiasCtlStore.lean` is removed, because the P part's control
  sites read the P part's data table (`pBData`) and `StepsBiasP.lean` now steps them by
  `stepAt_lift`.
- Handoff checks: the regenerated `ExpoB0` carries the negated scale, factor, maximum and row
  sum. Its generator freshness check passed and its Lean check took 11.21 s. The hardware tail
  formatting check took 36.00 s. The software tail's formatting-only edit was dropped after its
  Lean check twice exceeded 60 s. The checkpoint build still needs to validate the underlying proof.
- Merge with `origin/main` (c64f10c2a): the data table dispatches to both `pPData` and `pBData`,
  and the step dispatcher uses both rounds' exponent and P proofs. Only `pwend .bias` remains in
  `D.numeric`. The software-tail unpack now checks the pair equation on the arbitrary input
  of the last generated run. Its isolated check with the long-line linter took 48.45 s. The
  other edited modules took 4.93 s (`Machine`), 13.91 s (`Data`), 4.23 s (`Steps`), and
  4.89 s (`Fragment`).
- Generated the closing bias poll's arithmetic from the PTX: `rsumBa` rescales the previous
  sum at pc 6561, and `rsumBb` starts after the zero move at pc 6562 and ends at 6647.
  The addition tree has four pieces, with the final pair addition, unpack and scalar addition
  in the last piece. `Gen/RsumB.lean` checked in 4.42 s in isolation and 3.9 s in the strict
  build. Generator freshness passed.
- Resumed on `349d93bc7`. The merge keeps the newly split plain proofs and the bias
  exponent and P proofs. Saved work `6a9d7536b` moved the bias values ahead of the successor
  and updates `mf`, `mr` and `rs` in `afterBias`, using `maxB` and `rsB`. This batch
  retains those changes after isolated checks of the merged files and a strict
  `Proof2.Top.Correct` checkpoint. One numeric state remains in the dispatcher,
  `pwend .bias`. Its proof still needs the generated sum's kinds, the three successful
  continuations, and the failed poll's back edge.
- The closing poll is done: `StepsBiasEnd.lean` (`stepAt_pwendB`) from the sum's kinds
  (`BiasSum*.lean`), its segment (`StepsBiasSum.lean`) and the three continuations
  (`StepsBiasTail*.lean`). `SmWarp.numAll` (from `Pre`) closes the premise `numAll`. The back edge
  first carries the registers that do not read the tile counter over tables in which that
  counter's two values are opaque (`biasT_carried`): with the tables unfolded the kernel compared
  the words' arithmetic and ran out of stack after 150 s; now 6 s.
- A4 done: `Softmax.dataStoreSafe` (`DataStore.lean`): the P stores' halves have four bytes by the
  kinds of the exponent stretches (`DataStoreBytes.lean`), the statistics are numbers or the `-∞`
  pattern, and the addresses are in the lane chunk or 4-aligned (`DataStoreSite.lean`,
  `Lemmas/Flow/UbFreeStore.lean`). `DataStoreSafe` has no premise of the state's invariant beyond
  the machine's, so no row-sum fact is needed.

## Lane tmlfa4-safety (ex-Inkling agent): the frame-free SafePremises fields (2026-11-22)

### What each assigned field needs (read off Core and the Proof2 tree)

- `noWarpDivergence`: every lane-compared instruction of the code is a `pollAgree` site
  (checked: no other `Instr.laneCompared` position), so `not_warpDivergent_synced` with the
  code's poll guards, `LocalLands` (the software `exp2` segments land off poll branches; the old
  `Thread/PollUniformity.lean` checks are static and move as they are) and `PollSynced`: two lanes
  of a warp polling one position at different objects must be ordered. The softmax, correction
  and output warps' polls name one object per site and warp (`Softmax.stS + pollOff`,
  `Correction.pollOff`, the output's ready/free barriers by site), so only the MMA warp's ring
  polls (`bl L g (pollO r s)`, by round `r`) and the loader's ring polls differ, by round; the
  order comes from the warp collectives each round makes (elections, shuffles: Inkling's
  `meet_elect`/`meet_shfl`, `Proof2/Lib/PollMeet.lean`) with exact per-round collective counts.
- `noTmemWrites`, `noTmemReads`: two writes of a cell, or a read and a write, ordered
  (`TcMma.WritesSafe`, `ReadsSafe`): the MMA warp's D writes against the correction warps'
  rescale stores and the softmax warps' P stores, through the Tensor Memory hand-offs (commit,
  poll) — not frame-free.
- `noTmemSource`: every `tcgen05.ld` cell and every completed MMA's accumulator and A read has a
  source write (`SourceSafe`): the same hand-offs plus `tcLdDataflow`.
- `noTmemInstruction`: `IssueShape` per MMA (descriptors and masks from the MMA shape table,
  `Top/MmaDesc.lean`) and `CompletedValues` (every completed result cell has a derived value: the
  operand values, so the shared-memory hand-offs of Q, K, V and P), copies (none) and collector
  reuse.
- `noTmemAccess`: Inkling's `Protocol/TmemAccess.lean` (`no_access_unsafe`) with the warp as a
  parameter, `Tmem1Facts` (`Top/TmemWord.lean`), the access shapes, and two orders: every
  `tcgen05.ld`/`st` of a CTA before its deallocation (`TmemLife`), every MMA done before it
  (`MmaDoneDealloc`).

### Round 1 results and what blocks the rest (lane tmlfa4-safety)

- `noTmemAccess`: `Proof2/Lib/TmemAccess.lean` (Inkling's argument with the allocating warp as a
  parameter, namespace `Proof2.Tmem1`; a `Lemmas/Tmem/` candidate) and `Top/TmemAccess.lean`.
  The field is replaced by `tmemAccess : TmemAccessFacts` (access shapes `info`, the allocation
  and wait orders `life`, the MMAs done before the deallocation `done`); `life` and `done` are
  requested from lane T1 in `machine-plan-status.md`; `info` is this lane's next step (the
  roles' Tensor Memory addresses from the allocation word 0: the MMA warp's D/accumulator/A
  columns, the softmax and correction warps' load/store columns; no `cp`/`shift` statically).
- `noWarpDivergence`: the poll classification works for every role but the loader. MMA ring
  polls are ordered by elections: `Mma.RefQ` gives a lane's elections exactly
  (`won`/`lost` = `electAll q r`, strictly increasing in the round), so Inkling's `meet_elect`
  applies. The loader's ring polls (`slot_loc`, by packet) need a per-packet warp-collective
  count; the loader's `RefCounts` has none (its rows' shuffles are not counted), and adding a
  conjunct means re-proving the loader step files. Open.
- `noTmemWrites`, `noTmemReads`, `noTmemSource`, `noTmemInstruction` (its `CompletedValues`),
  `noSharedLifetime` (asynchronous uses completed before an exit) and the parts of `noTma` other
  than initialization (object record faults, writes overlapping an object ordered after its
  initialization, `cp.async` overlap) all need hand-off orders or write frames: none is free of
  them. `noTma`'s `ObjectPublished` part follows from `obj_initFirst` (Inkling's
  `objects_published` pattern).

### Assignment, round 2 (lane tmlfa4-safety): the Tensor Memory hand-off orders

Order of work, from the coordinator (2026-11-22): (1) `TmemAccessFacts.info`, then `noTma` split
(the published part from `obj_initFirst`/`use_pub`, the rest named premises); (2) the Tensor
Memory hand-off orders, owned by this lane: the MMA warp's `tcgen05.mma` writes and commits
against the softmax and correction warps' `tcgen05.ld`/`st`, per region and round, through
commit → mbarrier → poll (`Frame.Handoff`, `SingleTmaRing` patterns), warp 12's allocation before
every access and every load/store/MMA waited on before the deallocation (`life`, `done`); then
`noTmemWrites`, `noTmemReads`, `noTmemSource`, `noTmemInstruction` (operand values a named
premise); (3) `noWarpDivergence`'s MMA half by `meet_elect`, the loader half a named premise until
T1's K/V ring bound (`phase_le`/`Reach` over the empty barriers 56–72) lands; (4)
`noSharedLifetime`, `noAligned`.

Findings for (1): the role shape tables leave the Tensor Memory address of a `tcgen05.ld`/`st`
free (`Softmax.tcLdOrUb`, `Correction.Ev` at `rld`/`rst`/`fld`), and `tcDataCell`'s column is
`base % 2^16 + columnIn`, not bounded by itself. So `info` needs, per Tensor Memory site, the
address register's value from the role's fact table (the allocation word 0 plus the site's
offset: e.g. `Softmax` `tm j`, line 474 of `Softmax/Machine.lean`), and for the MMA warp the
`d` register at each issue (`mmaTmem_ok`/`mmaSmem_ok` leave it a free word). These per-site
address lemmas are also what the region hand-offs need (which cells each access touches), so
they are the first piece of (2) as well. Plan: one file per role of site address lemmas
(`Top/TaddrSoft.lean`, `TaddrCorr.lean`, `TaddrMma.lean`), each a step-free evaluation of the
fact table at the site (no `site_shape`), checked under 60 s.
### Correction step files: the tensor-load condition on a code slice, seg_sym first, step lemmas (lane L, 2026-11-22)

- Profile of `StepsRescale` (lane L): 21.7 of 35 s of `stepAt_rld` was the kernel checking
  `corr_rld`'s `rw [Assumptions.all_tcLdWait]; kernel_rfl`, about 1.4 s per site: `ldConsumedAt
  kernel pc` reads `kernel.code[pc]?` and scans `kernel.code.drop (pc + 1)`, walking the code from
  its head at every load. `Correction/Loads.lean` now states the code from 7744 once as the
  decoder's chunks (`corrCode`, `corr_tail` by one `kernel_rfl`) and the condition on that slice
  (`tcLdWait_at`, through the library's `Flow.ldConsumedAt_eq_in`); `corr_rld`, `corr_rldw` and the
  third site use `corr_wait`.
- `Correction/Base.lean`'s `lands_auto` tries `seg_sym` before `seg_auto` (the library's rule walks
  first since lane L round 13; the old order evaluated a doomed `seg_auto` at every landing).
- Every `Correction/Steps*.lean` imports `Kernels.TmlFa4Fwd.Gen.StepCorrection` (the per-pc step
  lemmas, lane L fe2a65851).
- Measured (CPU s, the same files before and after in this tree; load 100–190 before, 50–140
  after): `StepsRescale` 390.0 → 87.7, `StepsFinalData` 323.2 → 94.4, `StepsTiles` 163.4 → 19.8,
  `StepsScanFirst` 163.5 → 33.6, `StepsReq` 125.1 → 41.4, `StepsLse` 18.5 → 3.8.
- `Correction/Shape.lean` has the same `all_tcLdWait; kernel_rfl` four times (lines 179–217); it is
  being edited by lane L2 and is not changed here — it can use `corr_wait` / `tcLdWait_at`.

### Round 2 results (lane tmlfa4-safety, roadmap B2, D1, D8)

- **Addresses (B2).** `Top/TaddrCorr.lean` (`corr_tc`), `Top/TaddrSoft.lean` and
  `Top/TaddrSoftSt.lean` (`soft_tc`): every `tcgen05.ld`/`st` of a correction or softmax warp is
  `.32x32b` with `address % 2^16 + registers ≤ 512`. The MMA warp needs no address table: Core's
  `resultCell` and `aCell` already bound the columns, and the CTA is the issuer's by the single
  CTA group (`Mma.actualMmaOwnership`, `Mma.singleCtaGroup`), so `TaddrMma` was not needed.
- **D1, `info` proved.** `Top/TmemInfo.lean` (`tmem_info`, 6 s): `Tmem1.AccessInfo` from the
  address lemmas, the MMA cells (`mma_access`, `aCell_col`), the lifting of an event to its role
  state (`ldst_ok`: `ev_at`, then the role code's `fired_at_site`) and the code's lack of
  `tcgen05.cp`/`shift`. `TmemAccessFacts` keeps `life` and `done`.
- **D8, `noTma` split.** `Top/NoTma.lean` (`noTma_of_rest`): no invalidation (`no_inval`), every
  object with a record is a startup object (`obj_of_rec`), initialized first (`obj_initFirst`),
  and published to every other record's issuer (`pub_of_use`, `init_unique`). The field is now
  `tmaRest : TmaRest`: non-init record faults, accesses of object bytes, `cp.async` overlap,
  masked ranges (write frames, C1).
- **Barrier 2 (B2).** `Top/Bar2.lean`: `bar2_ev`, `srcs2`, `shape2`. `Lib/BarUpTo.lean`
  (`Frame.Handoff.of_bar_upTo_ord`): `of_bar_upTo` with consumers required to sync only at the
  ordinals below the bound (the softmax and correction lanes' second barrier-2 event is an
  arrive). `Top/MmaEntry.lean` (`mma_bar1_before`): every MMA code state other than `bar1`
  follows the lane's `bar.sync 2, 416`; this gives the MMA producer's arrival for the allocation
  hand-off (`hexit` of the hand-off: lane 0 of warp 12 exits only from a code state) and the
  MMA consumers' arrival.

Next for `life.alloc_before`: the softmax and correction access states have one barrier-2 event
before them (`soft_cnt`'s `before` counts with `RefQ`; the correction analogue), then
`of_bar_upTo_ord` with `n = 1`, producer the allocation of lane 0 of warp 12 (before its `bar1`).
For `ldst_before_dealloc`: every `wait::ld`/`wait::st` of a softmax or correction lane precedes
its `barEnd` arrive (ordinal 1), and the deallocation follows the MMA lane's `bar2` sync
(ordinal 1): `of_bar_upTo` with `n = 2`, consumers warp 12 (all syncs).

### Lessons for other kernels (from tml-fa4's Tensor Memory work)

- An access-info fact (`Tmem1.AccessInfo`) is cheapest as: per-role site address lemmas read off
  the fact table (`holds_mem` + `lit_mem` + `code_lookup`, one macro per site kind), a dispatcher
  over the role's shape table, then one lifting lemma per role from the event to its role state
  (`ev_at`, the role code's `fired_at_site`). MMA cells need no table: Core's layouts bound them.
- `bv_decide` fails in `module` files; column facts on `or`/`and` words go through
  `Nat.or_mod_two_pow`, `Nat.and_mod_two_pow` and `Nat.or_lt_two_pow (n := k)`.
- Facts a data table may shadow (Inkling's softmax-like data tables) need the lookup shown `none`
  before `mem_factsFrom` (`pst_plain_mem`); `unfold` the table and `split <;> rfl`.
- A "this role state follows its first barrier" fact needs no invariant: induct on the trace
  position through `Frame.stateAt_succ` and the glue's `enter` (`mma_entered`).

### Round 3 (lane tmlfa4-safety, B2): the allocation hand-off is proved

`Top/AllocBefore.lean` (`alloc_before`, 3 s) proves `Tmem1.Life`'s first field through barrier
2's first rendezvous, from `Top/Bar2First.lean` (`first_bar2_sync`), `Top/AllocPre.lean`
(`pre_bar2_zero`, `lane0_alloc`), `Top/AccBar2.lean` (`acc_bar2`: every MMA/ld/st follows a
barrier-2 event of its lane, via `soft_acc`/`corr_acc` and `Top/Bar2Soft.lean`,
`Top/Bar2Corr.lean`) and `Top/MmaEntry.lean`. `TmemAccessFacts` now holds `ldstDealloc` and `done`.

Plan for `ldstDealloc` (each `tcgen05.ld`/`st` waited on before the deallocation): the
deallocation follows the MMA lane's second barrier-2 sync, so `of_bar_upTo` with bound 2 and
consumers the warp-12 lanes (all syncs) orders every softmax or correction event of barrier-2
count at most 1 before it; producers' exit condition (two barrier-2 events before an exit) from
the `RefQ` counts at the exit sites (as `tc_bar2`). The wait itself: correction loads are followed
by their wait at once (`rld → rldw` with `k = 1`, `fld → fwl`), stores wait at `rwait` after the
eighth store of a stage (`rst c → rld (c+1) → … → rwait`); softmax plain loads wait at the same
instruction's sub-step (`sldw`), first/bias loads at the first P store's sub-step (`pst r 0`,
`k = 0 → 1`), P stores at a later `wait::st`. Each needs a pending-region induction along the trace
(`Frame.stateAt_succ`, the role code's `next` on the region's sites), the same shape as
`mma_entered`: from a load at `f`, every later state up to the lane's `barEnd` is in the region
or past a wait.

### Round 4 (lane tmlfa4-safety, B2): `Tmem1.Life` is proved

`Top/LdstDealloc.lean` (`ldst_dealloc`) proves `Life`'s second field. Pieces: `Top/CorrWait.lean`
(`rldw_wait`, 33 s), `Top/CorrLdWait.lean` (`corr_ld_wait`), `Top/CorrStWait.lean`
(`corr_st_pend`), `Top/SoftStWait.lean` (`soft_st_pend`), `Top/SoftLdWait.lean`
(`soft_ld_pend`), `Top/PendNoBar.lean`, `Top/AccSite.lean`, `Top/MmaDealloc.lean`
(`pred_dealloc`, `mma_pred`, `dealloc_bar2`), `Top/Bar2Exit.lean` (`sc_exit_bar2`),
`Top/DeallocHand.lean` (`dealloc_handoff`). Each pending-region lemma is an induction on the
trace position with the role's `succ` on the region's sites (the `mma_entered` pattern); its
conclusion is "a wait, an undefined-behaviour event, or still in the region", and the caller rules
out the last two with `ub_last` and the region's lack of barrier-2 events.

`TmemAccessFacts` now holds only `done` (`Tmem1.MmaDoneDealloc`: every MMA is done, by an observed
commit, before the deallocation). It needs the commit → mbarrier → poll chain: an MMA's issuing
lane commits after it to the final O barrier, a correction lane's poll observes that phase before
its `barEnd` arrival, and `dealloc_handoff` carries the poll to the deallocation.
### Check cost of the softmax step files (round: split by site)

Measured alone with `lake env lean <file>`, CPU seconds, host load 70–80 (the numbers in the
task's list are wall clock from a full build at load 140–200, about 1.5–2× these).

- **Split by site, every statement unchanged.** The four scan families (`StepsScanFirst`,
  `StepsScanLoop`, `StepsScanSecond`, `StepsScanLoop2`) checked their eight sites in one theorem
  each; one site (`total`) was 90.7 s of `StepsScanLoop2`'s 139.9 s, and the family files were
  84–140 s. Each site now has its own file (`StepsScanLoop2Word.lean` …) and the family theorem
  dispatches over the `hs` disjunction; `Steps.lean` is unchanged. Same for `StepsScore` (the
  eight score loads `StepsScoreFirst0`…, the three implicit waits `StepsScoreWait0`…, the reading
  lemma and the `soft_sld`/`soft_sldw` overrides moved to `StepsScoreLib.lean`), `StepsSelect`
  (three sites), `StepsMid` (three families) and the two control families (polls and P part).
- **Measured after** (CPU s): scan `word` 3.3, `down` 26.4 (`StepsScanLoop2Down`), `up` 9.5–10.1,
  `total` 90.7; score loads 10–18, waits 19–23, `StepsScore` 1.4; select `vote` 8.9, `pre` 6.3,
  `tiles` 95; `mid0` 39, `bld1` 7.6, `bld2` 7.5; first round control poll 19 / store 33, bias
  poll 25 / store 53. Family files (dispatch only) 1.3–2.5 s. Before: `StepsScore` 137.0,
  `StepsSelect` 103.1, `StepsScanLoop` 97.3, `StepsScanFirst` 84.2, `StepsBiasCtl` 62.3,
  `StepsMid` 52.7, `StepsFirstCtl` 45.4, `StepsScanLoop2` 139.9.
- **What is still over budget**: the four `total` sites (66–98 s), the four `down` sites
  (25–42 s), `tiles` 95, and `StepsBiasCtlStore` 53. Their cost is not the walk's length (the
  pieces are 2–5 instructions) but the elaboration of every landing against the machine's state:
  `total`'s profile is `refine` 26.4 s in 30 calls, `seg_sym` 22.4 s in 6, `exact` 9.4 in 9,
  `seg_fp_core` 5.6 in 11, for six successor outcomes over four code branches.
  - Measured and rejected: (a) the control machine `code` instead of `codeD` makes the `total`
    site *slower* (149.4 s): the control table is no smaller, so the lift that took
    `StepsPlainCtl` from 271 to 40 s does not transfer to the scan sites without the rest of that
    lane's `Lift.lean` (region checks + `land_data`); (b) `site_norm` before `lands_auto`'s landing
    refine: 90 s, no change; (c) `seg_sym` before `seg_auto` in the role's `lands_auto`: 91 s, no
    change (kept: it matches the library's rule after lane L2's b3277a597 and costs nothing here).
  - The next cut, in order: state the successor's outcomes as one `Lands` lemma per target
    (`wend`/`vote`/`down`/`word`, six leaves) with the guards the walk splits on taken as
    hypotheses, so that the 30 refines and 19 landings are spread over six files; then the same
    for `down` and `tiles`.
- **The heartbeat budget was the cost** (the round's biggest find). The step files carried
  `set_option maxHeartbeats 40000000` (200× the default). A doomed alternative — `seg_auto` on a
  segment with a symbolic branch, a combinator tried before the right one, an `isDefEq` — runs
  until the budget is gone, so the file's check time is roughly *proportional to its budget*: the
  `total` site of `loop2` measures 90.7 s at 40M, 58.8 s at 1M, 32.7 s at 600k, 16.4 s at 300k
  heartbeats (`lake env lean`, same file, only the option changed). Each of the split step files
  now carries the smallest budget that still checks (400k: the scan `word`/`down`/`up`, score,
  mid, control sites; 1.2M: the four `total` sites, `tiles`, the bias/first control store
  halves), and `maxRecDepth 2000` on the `total` sites (100000 elsewhere): a shallower recursion
  limit makes the failing searches give up sooner. Measured after the tuning, alone with
  `lake env lean` (CPU s, load 70–80): `StepsScanFirstTotal` 35.6, `StepsScanSecondTotal` 50.8,
  `StepsScanLoopTotal` 53.0, `StepsScanLoop2Total` 58.5, `StepsScanFirstDown` 10.5,
  `StepsScanLoop2Down` 20.3, `StepsScanLoop2Word` 3.3, `StepsScanLoop2Up0` 9.5.
  - Caveat measured: `lake build` (which passes `-s512000`, a 512 MB thread stack) needs about
    three times the budget of `lake env lean` for the same proof (`StepsSelectTiles` checks at 500k
    standalone in 55 s but needs 1.2M under `lake build`, where it is 85 s). The budgets above are
    the `lake build` ones; a *file* may therefore measure faster alone than in a full build.
- **Still over budget**: `StepsSelectTiles` 85 s (build; 95 s alone at its budget) — its successor
  (`afterTiles`) is a `divOk` pair and one `D.ite`, so one lemma per outcome (two files) is the
  cut, together with the two `total` sites' remaining ~60 s. Both want the same tool: state the
  `Lands` landing per *outcome* with the guard hypotheses in hand, which `site_cases` cannot do
  today (its `using [h]` only sees hypotheses that exist before the event; these guards depend on
  the event's value). Recorded as requests in `machine-plan-status.md` for lane L2.

### Plan for `done` (lane tmlfa4-safety, B2 → D1)

Core accepts an MMA as done before the deallocation only through `AsyncObserved` (a successful
wait whose object history has the commit's notification before it: `UpdateBeforeWait`), so a
causality-only chain does not suffice. The barriers: the MMA warp's last two commits, `cm 10`
(object `sb + 144`) and `cm 11` (`sb + 152`), each once per CTA; the correction lanes poll them at
`fw 0 0` and `fw 1 0` (parity 0). Steps, in order:

1. **One-shot objects.** Objects 144 and 152 are initialized with count 1 (`initCnt`) and receive
   no thread arrival; their only notifications are `cm 10`/`cm 11` commits of the CTA's elected MMA
   lane. Phase 0 completes at that notification. Library: `Lemmas/Protocol/MbarOneShot.lean`
   (`Hist`, `invariant`, `completed_iff`), `MbarRing.Slot.updateBeforeWait_of_phase`
   (`Lemmas/Protocol/PollPhase.lean`); T1's `NoIncRing`/`PollLe.okPolls_le_phase`/`emptyObj`
   commit-only histories are the same pattern.
2. **The poll observes the commit.** A successful `fw 0 0` wait (parity 0) on 144 observes phase
   0, whose record is the commit's notification: `UpdateBeforeWait` by step 1's lemma.
3. **The commit covers every MMA of its lane.** `TracksMma i c` needs `i.1 = c.1`, `i.2 < c.2`.
   Same lane: the warp's elections have one winner (`elect_ordinal`, Inkling's
   `selected_elect_thread_unique` pattern), MMAs and commits are issued only by the winner. Order:
   a forward region lemma (the `corr_st_pend` pattern) from the `cm 10` state: the later states are
   `ce 11`, `cm 11`, the late scheduler pass (`passStart true`: word, down, up, total, vote, pre,
   tiles late), `relinq true`, `bar2 true`, `dealloc true`, `exit true`, none an issue site.
4. **The poll before the deallocation.** The correction lane's `fw 0 0` is before its `barEnd`
   arrival (ordinal 1), so `dealloc_handoff` gives `baseCausality wait d`.
5. **A correction lane polls whenever an MMA exists.** An MMA means the CTA picked a tile
   (`Epilogue.Picked`, one per CTA: `Picked.cta`), so a correction lane of the CTA takes its tile
   path, reaches `barEnd true` (member arrival, as in `dealloc_handoff`) and passes `fw 0 0` before
   it: another forward region lemma from the correction lane's first tile state to `barEnd true`.

Then `done` leaves `TmemAccessFacts`, and D1 is DONE.

#### Progress on the plan for `done`

- Step 1, the classification: `Top/OObj.lean` (`o_use`, 10 s). An event naming the final O
  barrier of stage `st` (offset `oOff st` = 144 or 152) is the MMA warp's commit at
  `cm (10 + st)` or a correction lane's parity-0 poll at `fw st 0`; helpers `mma_o`, `cm_o`,
  `mma_wt_le`, `corr_arrOff_o`, `corr_pollOff_o`, `cmO_o`.
- Step 3, the order: `Top/MmaPost.lean` (`post_next`, `post_states`). After the lane's state at
  `cm (10 + st)` every later state has `postSite st` (no issue site, no `cm (10 + st)`).
- Open in step 1: one stage commit per CTA (the `Hist`'s single arrival). Same lane: the post
  region excludes `cm (10 + st)`. Distinct lanes: only an election winner reaches a `cm` site
  (`RefCounts`: `site.ord ∈ cmQ → w = true`), and two winners of one election instance are one
  lane (`elect_ordinal` gives one instance per ordinal; a winner has `ld = laneOf`). For the
  MMA issuer (step 3, same lane as the commit), `cmQ` does not contain the issue sites' places,
  so `w = true` at `qk`/`pv` has to come from the election at `eq`/`ep` just before (the succ
  of `eq b`/`ep b` enters the issue only on `laneOf L g = ld`).
- Then `Hist` for object `oOff st` with `ras = [(.async c (.tcNotify rank), 0)]`, `cs = []`
  (records from `o_use`, `init_first` from `obj_initFirst` with `initCnt 18 = initCnt 19 = 1`,
  `no_inval`), and `MbarOneShot.Hist.observes_arrive` gives `UpdateBeforeWait`.
- Done since: `Top/MmaWin.lean` (`pred_win`, `win_states`, `won_elect`, `win_lane`: the issue
  sites, the winner's PV poll `mw b true` and the commits are entered only on a won election, and
  two winners of warp 12 are one lane, by Core's `elect_leader`); `Top/OHist.lean`
  (`commit_same`: one stage commit per CTA; `o_hist`: the object's `MbarOneShot.Hist` with that
  commit's notification as its one arrival).
- Next for `done`: (a) the commit from the poll: a successful parity-0 poll of a count-1 object
  is after its one arrival record (from `MBarrier.CheckedLog`: phase 0 completes only on the
  count's arrivals; the record's source is a `cm (10 + st)` commit by `o_use`); then
  `o_hist` + `observes_arrive` give `UpdateBeforeWait`, `TracksMma` from `win_lane` (same lane)
  and `post_states` (the MMA before the commit), `rank ∈ tcNotified` from the record's
  `objectAction`; (b) step 4: the poll at `fw 0 0` precedes the correction lane's `barEnd`
  (ordinal 1), so `dealloc_handoff` orders it before the deallocation; (c) step 5: a correction
  lane of the CTA reaches `fw 0 0` when an MMA exists (tile agreement, T1's `tile_agree`
  pattern, and a correction forward region from its first tile state to `barEnd true`).

### Round 5 (lane tmlfa4-safety): D1 is DONE

`noTmemAccess` takes no premise; the SafePremises field `tmemAccess` is removed (b2b8b22e7).
`Top/ODone.lean` (`mma_observed`: a successful final O poll of an MMA's CTA observes the MMA done)
and `Top/ODealloc.lean` (`dealloc_arrival`, `mma_picked`, `corr_arrival_poll`, `mma_done`). The
correction ledger's `.acquire 144` count at `barEnd true` (1, `acq144_barEnd`) gave the poll
without a correction region lemma, and `noPicked_exit` on the correction lane's `barEnd false`
gave the tile agreement without T1's `tile_agree`. Lesson: a ledger count conjunct at the target
site replaces a forward region lemma when the class counts exactly the event wanted.

### Plan for D2–D5 (lane tmlfa4-safety): the per-round Tensor Memory orders

Core's checks (`Core/Tc/TcMmaConflicts.lean`, `TcMmaOrder.lean`, `TcMmaRead.lean`):
`WritesSafe` (D2: every two writes of a cell ordered by `WriteBefore` = `Before` ∨
`StoreDoneBefore` ∨ a copy pipeline), `ReadsSafe` (D3: an MMA's C/A read and a write of its cell
ordered by `WriteBefore` or `ReadBefore`: `DoneBefore` or an MMA pipeline pair), `SourceSafe` (D4:
every load register and completed C/A read has a source write), `InstructionSafe` (D5, with the
operand values a named premise for Result work). The writers and readers per region:

- S of stage `st` (columns `tmS + 0..127`): MMA QK writes it; softmax loads it (`sld`) and stores
  P into columns 64..127 (`pst`); MMA PV reads P as its A operand from Tensor Memory.
- O of stage `st` (columns 256..511): MMA PV writes it (accumulating, so it also reads C); the
  correction warps load it (`rld`, `fld`) and store the rescaled O (`rst`).

The orders, per round `r` of a stage:
1. QK(r) → softmax loads and P stores of round `r`: QK's commit → the S-full barrier → softmax's
   successful poll (`DoneBefore` through `AsyncObserved`, the one-shot pattern of `mma_observed`,
   but on a ring: phase `r` of the barrier, `MbarRing`/`UnitRing` counts).
2. P stores (r) → PV(r)'s A read: softmax's `wait::st` → its arrival on the P-full barrier → the MMA's
   poll (`StoreDoneBefore`: the store's wait, a release arrival, the MMA's acquire poll), then the
   tcgen05 fence before the issue.
3. PV(r) → QK(r+1) on S: the A read is done before the next QK write (`ReadBefore .a`:
   `DoneBefore` via PV's commit polled by the MMA warp itself, or the MMA pipeline pair for one
   issuing thread: `Pipelined .aRead .dWrite`).
4. O: PV(r) ↔ correction `rld`/`rst` of round `r`: PV's commit → the O-ready barrier → correction
   poll, and correction's `wait::st` → arrival → the MMA's poll before PV(r+1).
5. Same-thread MMA pairs (QK/PV of one issuer) are ordered by the tcgen05 pipeline rules
   (`Pipelined`), MMA program order of the one winner lane (`win_lane`).

Library to reuse: `MbarRing.Unit`/`UnitRing` (T1's ready and credit rings), `NoIncRing`,
`PollLe.okPolls_le_phase`, T1's `MmaFullLag` (the MMA's lag behind the loader), the one-shot
`MbarOneShot` for the final barriers (done in `OHist`). Each region order is a ring hand-off of the
`Frame.Handoff.of_unit` shape plus the `AsyncObserved` step of `mma_observed`.

#### The barriers of D2–D5 (read off the shape tables)

- S-full of stage `st` (shared offset `80 + 8 st`, count 1): the MMA warp's commits `cm 0`/`cm 3`
  (stage 0) and `cm 1`/`cm 5` (stage 1) (`Mma.cmO`), polled by the stage's softmax lanes at
  `ws r` (offset `stS + 80`, parity `spar`, `Softmax.pollW`). A commit-only unit ring: the
  history of T1's `emptyObj`/`commitObj` (`NoIncRing.commitObj_phase_le_commits`), polls bounded
  by `PollLe.okPolls_le_phase`. Hand-off 1 (QK(r) → the round's softmax loads/P stores):
  softmax's `r`-th successful poll observes phase `r`, whose notification is the round-`r`
  commit, which tracks QK(r) (`TracksMma`: the winner lane, `win_lane`; QK before the commit by
  the MMA ledger's commit count `RefQ.com` at the QK site). The `AsyncObserved` step is
  `mma_observed`'s, with `updateBeforeWait_of_phase` for phase `r`.
- P-full of stage `st` (offsets `stS + 96`, `stS + 112`): softmax arrivals at `parr`/`parr2`
  (`Softmax.arrOff`), polled by the MMA warp at `wt 4/6/8/9` (offsets 96/104) and `mw b`
  (112/120). Hand-off 2 (P stores (r) → PV(r)): `StoreDoneBefore` via softmax's `wait::st` at
  `pwst`, its release arrival, the MMA's acquire poll.
- New per-role counts go in lane L's small-invariant constructor (`Lemmas/Kernel/SmallInv.lean`,
  b3b51315d), not in step files.

#### Hand-off 1: what the phase step needs (found while writing it)

`Top/SObj.lean` (`sfull_use`, `sfullObj`, 51 s): the S-full barriers are commit-only objects.

Core's `AsyncObserved` takes the notification whose phase equals the phase the poll observed
(`UpdateBeforeWait`: `phaseAt i = observedAt j`). With count 1, phase `q` is completed by the
`(q+1)`-th arrival record, but Core does not order one thread's commit notifications, so the
record completing phase `r` need not be round `r`'s commit. The argument that works:
1. Before the softmax lane's `r`-th successful poll, the MMA warp has made no stage commit of a
   round after `r`: its round `r+1` QK commit follows its poll of the P-full barrier, which the
   softmax lane arrives on only after that poll. This is the MMA's lag behind softmax: roadmap
   E2 (`mmaSoft`, the softmax half of MmaFullLag), on T1's `MmaFullLag` pattern.
2. So the first `r+1` arrival records are the notifications of commits `0..r`, and round `r`'s
   commit has phase `q ≤ r` (`card_unit_arrivals_phase`, `unit_arrival_phase`).
3. The softmax lane polls every phase in order (`PollLe.okPolls_le_phase` and its count of
   successful polls), so its `q`-th poll observes phase `q`: `AsyncObserved` for every MMA that
   commit tracks (`mma_observed`'s step), and that poll precedes the round-`r` loads in program
   order (`baseCausality`).
So hand-off 1's phase step and E2 are one piece of work: E2 first.

#### E2 and hand-off 1: the shared safety bound

E2's field (`mmaSoft : Progress.MmaLagFrom false`, `Progress/MmaPoll.lean`) is a progress fact:
at an MMA poll of a softmax-produced barrier whose phase parity equals the MMA's acquire count,
the lane is blocked (`Sched.Blk`). T1's loader half is `kv_lag` (`Top/MmaLagLd.lean`, 640 lines),
built on two safety bounds: `com_le_lane` (the MMA lane's commits to the K/V empty barriers are
bounded by the loader's acquires) and `kv_bound_lane` (the loader's arrive-on count against the
MMA's acquires). The softmax half needs the same two bounds with the softmax lanes as producers on
the P-full barriers (offsets `stS + 96`, `stS + 112`), and the S-full commits (80/88) bounded by
the softmax polls. The second bound, "the MMA's stage commit of round `r+1` follows the softmax
lane's `r`-th successful S-full poll", is exactly what hand-off 1's phase step needs (step 1 of
"Hand-off 1: what the phase step needs"). So the work order is: the softmax `com_le_lane` and
`kv_bound_lane` analogues (a file `Top/MmaLagSoft.lean`), then hand-off 1's phase step, then
`mmaSoft` from them on `kv_lag`'s pattern.

#### E2 step 2 (the softmax `kv_bound_lane`): what it needs

`Top/MmaLagSoft.lean` (`scom_le_lane`, 4.4 s) is step 1. Step 2 differs from T1's `kv_phase`:
- The P-full barriers (offsets 96, 104) have count 256 and two producer groups: the stage's 128
  softmax lanes (`parr`, `Softmax.arrOff`) and the correction warps' 128 lanes (`arr 0/1`,
  `Correction.arrOff`). `kv_phase` bounds a phase by one group's arrivals
  (`NoIncObject.phase_mul_le_units`, `units_le_sum`); here the bound must use the softmax group
  only, so it needs each phase to take one arrival from every softmax lane (per-lane arrival
  counts equal across the group, or `RecordCountPair`'s per-producer form).
- T1's per-lane bound `ld_arr_le_polls` counts the whole trace through `Frame.end_countP`, which
  needs the role's liveness (`succ = none` only at the exit: `Loader.role_live`,
  `Mma.role_live`). The softmax role has no `role_live` yet; it is a per-site lemma on
  `Softmax.succ` with the shape table (as `Mma.role_live` in `Top/MmaNoUb.lean`).
- With those, the per-lane bound is a site table: at every softmax site, the P-full arrivals
  before it are at most the S-full successful polls before it (`RefQ.cnt` for `.arrive 96` and
  `.acquire 80`, `passed`), checked by `decide` over `Softmax.allSites`.
- Softmax `role_live` (piece 1), the parts: `Softmax.succ` returns `none` (dies) on 21 branches:
  an event kind its site's shape excludes (closed by `fired_soft`'s `EvS` and `shape_destruct`),
  and a read whose bytes do not rebuild (`.error _ => none`: the scheduler reads `word`, `q0`,
  `q1`, `uk`, by `SmWarp.sexpect`/`expect_uk` and `Epilogue.next_none` as in `Mma.role_live`;
  the bias reads `bld`, by the data plane's read facts `SmWarp.fired_r`/`EvR`). The scheduler
  sites go through `Epilogue.next_none` exactly as `Mma.role_live`'s `hsc` branch
  (`mexpect_sched` ↔ `sexpect`, `mfits_main` ↔ `SFits`).
- Step 2, the per-lane table, is done: `Top/SoftArrPoll.lean` (`arr_acq_table`, `arr_le_acq`,
  `soft_arr_le_acq`, 4 s).
- The per-producer P-full phase bound, what it takes. The library bounds a phase by the arrivals:
  `n · phase ≤ arrivalUnits ≤ Σ_producers arrivals` (`NoIncRing.phase_mul_le_units`,
  `units_le_sum`, for arrive-on objects; T1's `MbarRing.Unit.Obj` with a producer list for thread
  arrivals, as `readyObj`). So `phase ≤ B` needs one bound `B` on every producer's arrivals. The
  P-full barriers (count 256) have two producer groups: the stage's 128 softmax lanes (bounded by
  `soft_arr_le_acq` and the S-full polls, `okPolls_le_phase`, `commitObj_phase_le_commits`) and the
  128 correction lanes (`arr 0/1`, offsets 96/104), whose arrivals need their own bound in the same
  terms (the correction ledger's `.arrive 96`/`.arrive 104` against its rounds). Pieces:
  (a) `pfull_use`: who names a P-full barrier (softmax `parr`, correction `arr`, the MMA's polls),
  on `sfull_use`'s pattern; (b) the P-full object as `MbarRing.Unit.Obj` with the 256 producers
  (`readyObj`'s pattern); (c) the correction lanes' arrival bound; (d) the phase bound from (b),
  (c) and `soft_arr_le_acq`.
- Proof architecture plan (adopted, `proof-architecture-plan.md` §4.2, S6, S7): `pfull_use` must be
  written in the H1 style (no `cases i with`), which needs S6's role tables: per role `offs` with
  `ev_offs` (from `Top/MbarUse.lean`'s per-role lemmas: `epi_site`, `corr_mbar2`, `soft_mbar`,
  `mma_obj`/`mma_o`, `ld_obj`, `start_mbar`), thread-level `TOffs` in `Common/View.lean`, and
  `table_ev`. A `cases`-style `pfull_use` (a copy of `sfull_use`) was written and not committed.
  The Tensor Memory hand-offs go to `Top/Hand/<Name>.lean` as H2 declarations.

### Softmax role liveness (E2)

`SmWarp/Live.lean` exports `role_live`. The fragment's existing `Softmax.next_ends`
already handles the successor branches, including coordinate division and byte rebuild.
`role_live` applies it to the event shape from `fired_soft` and the expected return value
from `SmSrc`. An event without undefined behaviour can end the role only by exiting.
Standalone check 3.22 s wall, strict target build 2.4 s for `Live`.

### Softmax check costs after the lane handover

The inherited split files build with the first-round steps re-exported by `Steps`.
The first bias barrier has a segment file and a step file. The first-round exponent
input kinds and arrival step each have a file. The plain row sum separates the add
tree's kind checks from its result. The first closing poll imports the segments for
the bias successor. The split reuses the original event-successor statements.

`ShapeBld` checks the decoded instruction at each bias site and uses `shape_ldAny`
once for every sub-step. `SafeBld` applies the sub-step-independent `ldShared4_ok`. The scan shape proof checks one scan per file and checks the
shared ballot and selection cases once.

The strict target build on the shared host measured the following wall times in seconds. `StepsPlainRs` 47,
`StepsPlainE2d` 42, `StepsPlainMax` 55, `StepsPlainMax2` 47, `StepsPlainE1b` 52,
`StepsNarr1b` 31, `StepsBarr1b` 46, `ShapeBld` 1.8, `SafeBld` 45, scan/selection
leaves 20–45. The corrected dispatcher and poll built in 7.1 and 14 s; `Fragment` built in 10 s.
The larger remaining pieces include `StepsNarr1` 89, `StepsBarr1Chain` 62,
`StepsBarrB` 73, `StepsPwEBias` 110 and `StepsPlainRs2` 99.

### Softmax check costs on the merged baseline

The first bias barrier's product segment carries its facts over the generated product run's
instruction slice. The rest of the barrier chain starts at pc 3850. The bias-round barrier
separates its segment from the two event steps. The first P publication and the plain-round
stores and row sum separate their generated checks and local steps. The final elements of
the bias loads check four consecutive vectors per file in each of the two passes.

The Tensor Memory waits and probability elections use the event lemmas for their decoded
instructions. The sub-step-zero score load dispatches to the immediate or delayed load
lemma. A wait-state at sub-step zero contradicts the machine invariant.

Strict wall times from the merged checkpoints were 49 s for the first product segment and
30 s for the rest of its chain, 32 s and 46 s for the plain probability unpack checks and
steps, and 39 s, 2.9 s and 59 s for the plain add tree's kinds, run and result. Its closing
poll's sum segment and step took 16 s and 57 s. `ShapePElect` took 2.6 s, the delayed load
and store shapes 53 s and 8.8 s, and the sub-step-zero load shape 58 s. `Fragment` took 5.6 s.
The shared host load varied substantially between the checks.

The 60 s goal remains open for several files. Examples include the bias load groups
(66–96 s) and the two bias successor walks `StepsPwEBiasMasked` and `StepsPwEBias`
(119 s and 103 s). The remaining single-site walks need smaller cuts with literal register
values at their boundaries.

The first exponent run's 14 cut tables now state each register kind by range or explicit
register list. `kNext` checks the tables against their incoming instruction slices. This removes
the nested `kList` evaluations across earlier cuts. `StepsNarr1Checks` went from 101 s to 24 s
in the strict target build and took 25.04 s standalone. That build checked `StepsPlainRs`,
`StepsPlainE2d` and `StepsPlainMax` in 37, 36 and 46 s. The two bias successor files took
76 and 79 s.

### A5/D17 after the bias byte proof

`SmWarp/BiasSrc.lean` proves that a fired bias read has a four-byte footprint
(`bias_read_size`, from the decoded load). Given the ordered tensor-copy writers of its
four bytes, `read_biasPairBytes` recovers both BF16 elements. `rebuild_biasPairBytes`
checks the packed result against `biasOk`, including the word containing two masks.

`Top/SmSrcHandoff.lean` assembles `SmSrc` from `BiasReadHandoff` and `ScorePayloadSrc`.
The former supplies the selected TMA bytes and the order of other covering writes
(C1 and the bias-slot acquire/reuse protocol). The latter supplies the `f32` result kind
at score loads (B2 and the S-full hand-off). `Top/SmSrc.lean` now obtains the warp bound
from the fired softmax state's code invariant, so deriving the scheduler words and
tile-count division rules is independent of the correction data-source premise.
The existing `smSrc_of_rest` entry point retains its signature.
The remaining copy and score sources keep D17 open.

Two new files (186 lines), one existing proof file edited. Strict build wall times
were 4.4 s for `BiasSrc`, 2.5 s for `SmSrc`, and 2.7 s for `SmSrcHandoff`.
**Lane 1b (phase 1), 2026-11-22: G1, `terminates` on Proof2.** `Bound/Softmax.lean` finishes the
softmax measure (`succ_rank`, `measure_step`, `nb_room`: the biased counter is `rb - nB - 1 ≤ -2`,
`measure_le` from `SFits`). `Bound/Assembly.lean` glues the six roles' measures (startup below
9181, a role state above it, the MMA warp's four startup states below its code states; a state
after undefined behaviour at `top`), proves every transition from a followed state keeps it and
every counted event raises it (`μ0_step`), and bounds it under `JR` (`μ0_le`); `top - μ` is the
rank of `Frame.count_le`, so every thread's counted events are at most `top + 2`.
Decisions: (1) `Bound.terminates` takes the four safety premises that following the softmax and
correction warps needs (`dataSrc`, `numAll`, `dataStore`, `smSrc`), which `correct2` already has
(`SafePremises`), so G1 is removed without a new premise; a premise-free bound would need a
measure that does not read the reference values (the scan's round bound is in `SFits`/`CFits`).
(2) The copies' width (`terminates_of_count`'s second premise) is the old tree's static code check
`actualCopyShape` (`Proof/GlobalWrites.lean`), imported as it is; it moves with the other static
checks of item H. `Top/Correct.lean` no longer imports `Proof/Termination.lean`.
### Lane 1a (phase 1): the Top skeleton, one file per premise class (2026-11-22)

- The uncommitted `wt-p4b` diff of `Top/QHyp.lean` (`Loader.succ_tc`, `ld_copy_won`) does not
  check (an `omega` at the copy's predecessor index and an unknown identifier `d`), and the file
  took 413 s with it. Dropped; the loader predecessor fact is redone in its own file with the Q
  ring items.
- Review step 0.3: `SafePremises.smSrc` became `smSrcRest` (`SmWarp.SmSrcRest`: bias and score
  loads); `Base.smSrc` derives the whole premise by `smSrc_of_rest`.
- S2: `Top/Base.lean` (`Base`: `dataSrc`, `numAll`, `dataStore`, `smSrcRest`; `Base.smSrc`,
  `goodR'`, `table_followed'`); `Common/View.lean` (`JR.softmax`, `JR.correction` (takes
  `warpIndex < 16`), `JR.mma`, `JR.epilogue`, `JR.loader`, `JR.not_stub`, `table_ev`). The
  structure fields of `Base` are its accessors; a proved premise becomes a theorem of the same
  name.
- S3: `Top/Safe/<Class>.lean` (12 classes), `Top/Prog/<Class>.lean` (11 classes) and
  `Top/Result/{Output,Lse}.lean`, each with `<Ns>.<Class>.Rest` and the class theorem
  (`Safe.<class> hp hB hR hX`, `Prog.<class> hp hB hs hR`, `Res.<item> hp hB hR hX hC`). The
  unused `hp`, `hB`, `hs` are named `_hp`, `_hB`, `_hs` until the class's proof uses them.
  `SafePremises` is `base` plus one `Rest` per class; `ProgressRest` one `Rest` per class;
  `ResultPremise` a structure of the two result `Rest`s. `safe`, `progress`, `correct2` are fixed
  dispatchers. Namespaces `Safe`, `Prog`, `Res` (not `Result`, which would shadow
  `TmlFa4Fwd.Result`).
- Progress no longer reads `SafePremises` (rule P3): `progress`, `thread_steps`, `mmaLagLoader`
  and `nonRest_steps` take `Base` and `SafeGoal`; the records' freedom from faults comes from
  safety (`noTma_of_safe`, `Top/Released.lean`). `Top/Released.lean` and the progress class
  files import no safety class, so proving a safety class rebuilds only `Top/Safety.lean` and
  `Top/Correct.lean`. The shared shapes `StepsAt`, `RelSteps`, `Loader.isWait` moved to
  `Top/Prog/Defs.lean`; each `RelSteps` class names its predicate `Prog.<Class>.At`.
- `next` is counted as its four parts (`Prog.Next.Rest`: `reads`, `readWf`, `words`,
  `allocLast`), so a lane removes one part at a time. The open-premise count is computed:
  `Tools/premise_count.py` (fields of `Base` and of every `Rest`), with
  `tests/test_premise_count.py` comparing it with the roadmap's number
  (`TXVERIFY_TMLFA4_ROADMAP`, or `tmlfa4-roadmap.md` beside the repository; skipped without
  one). Count after S3: 32 (was 29 by hand, with `next` as one).

**Lane 1b, 2026-11-22: `blocked` on the library's templates.** `Top/Prog/Blocked.lean` proves the
class from `Sched.thread_cases` with the code checks `kernel_noCluster`, `kernel_noAsyncWait` and
the templates `Sched.reg_steps`, `tc_steps`, `barGroup_sync_steps`, `barGroup_arrive_steps`. The
one opaque field becomes three narrower ones: `regMatch` (requests of a warp match, exits follow a
request: from `req_at`/`noRegister`'s first-request argument, not yet written), `times` (the time
table's facts per blocked kind and the named barriers' participant groups; taken as a hypothesis
while lane 1a redesigns `Progress/Time.lean`), `tmemBulk` (Tensor Memory resource operations and
bulk-group waits, still open). The premise count rises by two (32 → 34); the fields now name the
facts that close them. Not done this round: `async` (the `cp.async` copy/arrive-on drain is a new
in-order drain lemma, and the other cases need the protocols' source facts, so splitting the field
now only renames it), `start`, `epilogue`, `correction`, `mma`, `loaderOther` (their remaining
parts are warp collectives, which need the next-event classification in the progress interface,
and time facts).

**Lane 1b, 2026-11-22: the warp-collective class (`Top/Prog/WarpColl.lean`).** A released lane at
a warp collective (`CollAt`, in `Prog/Defs.lean`: an instruction in `Rest` of kind `warp`) steps by
`Sched.warpColl_steps`, with no mode vote (code check), no CLC request (`no_clc`, so every thread
launched and none canceled) and the assumptions on appended lanes and on a lane's undefined
behaviour (`Assumption.WfStep.quiet`) proved; the open part is the kernel's
`Sched.WarpCollFacts` (one field, with the time table's lag inside it until `Time.lean` lands).
`Top/Assembly.lean` dispatches `CollAt` states there before the role cases (line-local, approved
by the coordinator). `start` is removed: every startup instruction in `Rest` is a collective
(`start_code`, checked on the code; a startup state is never at its role entry by the glued
invariant), so `Prog.Start.Rest` is empty. `epilogue`, `correction`, `mma`, `loaderOther` and
`softmax` no longer cover collective states (their `At` asks `¬ CollAt`). Count: 33 (start −1,
warpColl `facts` +1).
### Lane 1a: the time table for all roles, designed once (review finding 3, step 1T)

`Progress/Time.lean` now times every role's states; the waits' "blocker earlier" inequalities
follow from the slot and band layout (the table in the file header), through the order lemmas
`clk_lt_of_slot`, `clk_lt_of_off`, `prime_lt_clk`, `clk_lt_tail`, `slotOf_le`.

- Slots are 4096 wide (`span`), after a prime region of 1024 (`primeBase`, `pipeBase`). A slot's
  bands: MMA `[0, 512)` (unchanged `Mm.pipeT`, place `q` at `2 q`), softmax stage `st`'s score part
  `bandS st = 1024 + 512 st`, the correction's stage-`st` part `bandC st = 1280 + 512 st`,
  softmax P parts `bandP st = 2048 + 256 st`, the loader `bandL = 3072`.
- Softmax (`Sm.time`): round `u` (its S-full polls `Softmax.Cnt.acquire 80`, less one past the
  poll) in slot `u`. Stage 1's closing credit poll of round `u` waits for correction credit
  arrival `u` on 200, which is round `u + 1`'s stage-0 part (or `farr0`), so it opens slot `u + 1`
  (`bandS 1 + 0`), and stage 1's final stores follow it there; stage 0's closing poll and final
  stores end its P part. The request's reads are in the prime region.
- Correction (`Cr.time`): a rescale round's or the final stage's site of stage part `st` in slot
  `n (.corr (.nb st))` (less one past the part's sync), `bandC st`. The start's syncs and credit
  arrival are slot 0 (generation 0); the final stage is slot `U` (the tile's rounds), before the
  tail, after the MMA warp's tail commits (band M of slot `U`). `Cr.round`, `Cr.tailOff` keep
  their meaning as site classes (`Ready.lean`, `ReadyArrive.lean` unchanged).
- Loader (`Ld.time`, defined, not yet used by `roleTime`): the first block (packets 0, 1, TMA
  groups 0 to 3) in the prime region; packet `k ≥ 2` (its commits, `Ld.idx`) in slot
  `(k - 2) / 2`, K packet at `bandL + 128`, groups 4 and 5 at `+384`, V packet at `+512`, group 6
  at `+0`; drain in the tail. `Ld.time_prime`, `Ld.time_pipe`, `Ld.bound`, `Ld.bound_le` give the
  K/V poll inequality (`Top/MmaLagLd.lean` uses them once the loader is switched).
- Slots read off ghost counts are clamped to `bmax p` (`slotOf`), so every pipeline time is
  before the tail without a count bound (`clk_lt_tail`).
- Decision: the loader keeps the placeholder `scanBase` in `roleTime` for now. With the loader on
  its table the MMA warp's Q polls are no longer below every pending loader lane: a loader lane
  can wait for packet 3 (after the MMA warp's release of index 0, `clk 0 32`) while the MMA warp
  is at a Q poll (`clk 0 2`). `q_lag` then needs the TMA groups' byte balance
  (`Sched.Lag.blk_tmaUnit`, now in the library), with three loader facts not yet in the tree: the
  TMA elections' won counts as placed counts (a lane wins `te t e` at most once), the copies to a
  Q barrier are the winner's `tc t c` (the predecessor lemma), and the drain's arrival excluded
  while the MMA warp is before place 63. They are loader facts on lane 1c's `Loader/Move.lean`
  (`Loader/Facts/`); the switch of `roleTime .loader` to `Ld.time` lands with them, together with
  the `kv_lag` change (`ld_short_time`: a loader lane short of packet `i` is before
  `Ld.bound p i`, which is below the K/V poll, written and checked on the branch).

### Lane X2: the real loader times, and the Q polls by the byte balance

- `Progress/Clock.lean` holds the phases and the order of their times; each role's times are in
  `<Role>/Export/Time.lean`; `Progress/Time.lean` dispatches (the loader's placeholder is gone) and
  `Progress/Order.lean` states the inequality of each wait.
- The entry of every role is at `scanBase` (register requests: a lane without one is no later), the
  first warp barrier just after. The scans count shuffles (and the pass's ballot) only, without the
  pipeline's (the loader's 32 per packet, the MMA warp's broadcasts). The end sites are at
  `doneBase` after the second scan (the loader's drain, whose last election follows the second
  scan's collectives, too), or before the pipeline without a tile (`endT`).
- `kv_lag`: a loader lane short of packet `i` is before `Ld.bound p i` (`Loader.ld_early`).
- `q_lag`: two copies complete on a Q stage at most (`Loader.q_copies`), a completed phase takes
  two (`TmaUnitObject.phase_le`), so the poll is blocked only in phase 0; the elected lane of
  warp 14 (`q_winner`) past the first groups made the arrival and both copies (`Loader.q_done`,
  from `group_hist`), before that it is before the pipeline. The drain's arrival needs no exclusion
  (it has no copies). `LdWarp/Hist.lean` is `fact_at` for predicates of the earlier events.
- `noWarpDivergence` is proved: the static facts (`Softmax/Export/Lands.lean`, one pass over the code
  by `pollPass`), and per role that two lanes polling at one position poll one barrier or are
  ordered (`<Role>/Export/Poll.lean`; the loader by its shuffles, which `LFits` already counts).
- `loaderOther`, `mma`, `epilogue` are proved: their instructions in `Rest` that are no waits and no
  warp collectives are the register request, the allocation with its address store, and the
  `cp.async` operations (`<Role>/Export/Kind.lean`, `Top/Prog/Issue.lean`, the library's
  `Lemmas/Kernel/Progress/Issue.lean`).
- `Sched.WarpCollFacts.last` does not hold of this kernel: lanes past the batch skip the read before
  the first collective of a pass, so a warp's last events before it differ (a register request or
  a named-barrier arrival on some lanes, a read on the others). `Prog.WarpColl.Rest` asks
  `Sched.WarpCollRel` instead: of two lanes at one collective, when one is released the other is or
  the execution has an extension.
- A delayed P store makes two `tcgen05` events at one site (the wait, then the store): the softmax
  time reads its sub-step, so that a lane is later after each (`Blocked.Times.tcAfter`).
- Open of `noAligned`: the Tensor Core and barrier classes; of `Blocked.times`: the Tensor Core and
  barrier facts (the register requests are proved, `Top/Prog/RegTime.lean`); `WarpColl.facts`.
  One engine serves the three: the times of the sites every lane of a CTA visits are a set `P` fixed
  by the CTA; per role, no step of a lane jumps over an element of `P` (an edge check over `nexts`
  in a slot, the round counts between slots) and an event at a site of the class moves past it. Then
  the `k`-th event of a class is at the `k`-th element of the class's part of `P`
  (`Nat.nth`), and no ledger class and no closed form of a count is needed.

### Lane X2: the lags on the real time table (mmaSoft, softmax, correction)

* **Short producers are early, per role** (`<Role>/Export/Lag.lean`, `Mma/Export/{At,CommitLag}`,
  `Epilogue/Export/Out`): the waiter's barrier gives a producer with at most `v` arrivals or commits,
  and the role's count closed forms with a site table give its time. The correction's table is one
  for the P-full and credit arrivals (`corrO`, `corrE`, `corrB`): a lane with `A` arrivals is before
  offset `corrB q` of slot `A + corrE q`. The MMA warp's commits are read on the lane that wins its
  elections (`warp_winner`, `mma_at`), so one lemma gives S-full, O and later K/V and Q empty.
* **Waits** go through `Sched.wait_site_steps` (`Lemmas/Kernel/Progress/WaitSite.lean`) and
  `wait_rel`: the poll's barrier and parity come from the role's `*_mbar_use`, applied in the
  execution with the failed poll appended, so they are not proved again at the end of a trace.
* **Slots are within `bmax`**: `mma_rounds_bmax` (`Lib/RoundsBound.lean`).
* **Softmax Bias-full and the loader's TMA waits** (the groups and the Q drain) are lane X1's:
  `TmaBytes` is proved (`Protocol/Q/Bytes.lean`, `tmaBytes`) and every lane of a stage's Bias polls
  observes its copies (`Protocol/Bias/Lanes.lean`, `bias_reach`). The K/V slot and drain polls are
  proved here (`ld_kv_wait`, `kvE_lag`).
* **The schedule engine, warp collectives** (`Lemmas/Kernel/Progress/WarpCollPair.lean`): the facts
  are of two lanes of a warp (`WarpPair`), so a warp is closed alone. The static part is a function
  of the state, not of the pc: the choice's two shuffles (`pre`, `tiles`) read lanes of the ballot,
  so two lanes also need one ballot. `WarpColl.Rest` is the pairs of the warps other than 13; its
  static parts `S` are existential, and a role supplies its own.
* **The output warp** (`Epilogue/Export/{Coll,CollPair}`): the site is a function of the CTA and the
  number of collectives (`Pos`, the pass by `Progress.Late`); a lane at a collective is released
  with the other since its last event is its register request (`not_regWait`, for every role) or
  does not block. A lane whose machine stopped has exited (`out_live`, as in `Epilogue/NoUb`).
* **The MMA warp** (`Mma/Export/{CollCount,CollPos,CollState,CollSite,CollPair}`): the number of a
  state is its shuffles, ballots and elections (`mma_cnt_eq`); `MCls` says where a state stands
  (number, time, collective), one constructor per phase, and the facts of two lanes are about `MCls`
  only (`MCls.order`: site and lag together, `MCls.lt_exit`). The pipeline's order is a table over
  the places at round 0 and 14 collectives per round (`place_lt`).
* **A stopped lane**: the MMA machine may stop at `ldAlloc`'s read without an exit, one tick before
  the broadcast, so the lag excludes stopped lanes; a stopped pending lane is released
  (`WarpPair.dead`) and steps to its undefined behaviour.
* **For the loader pair**: its ledger counts the won elections only, so the elections need a closed
  form by induction over the edges: 12 in the first block (groups 0 to 3), 6 per warm round, 3 for
  group 6 (when it is taken), one in the drain; the rest has the shape of `MCls`.
* **`Blocked.times`, `tcgen05` events**: the MMA warp's resource events are in the time table
  (`Mma/Export/TcTime`: `mma_tcLag`, `tc_next`; `Mm.startT` has the allocation's store after the
  request), the output and loader warps have no `tcgen05` event (`noTc_of_warp`). Open are the
  softmax and correction warps' loads, stores and waits.
* **`Blocked.times`, the startup barrier**: `bar_before` bounds a lane before barrier 0 by 174 (a
  stopped lane counts one more than its last site), and the waiter is at 173, so the lag needs the
  bound 173: a lane with no barrier event stopped at a site before the barrier's.
* **The loader's elections**: lane X1's `Loader/Facts/{BiasNum,ElectNum,SuPick}` and `LdWarp/StepAt`
  give the polls in closed form; with three elections per TMA poll the elections are `3 P` less the
  ones to come in the group, where the drain's poll counts one. Group 6 is taken when `Last` holds
  (more than ten blocks and a negative `r29`), not with every tile of two blocks.
* **`WarpColl` is proved for every warp** (`Top/Prog/WarpColl.lean`; `Rest` has no field). A warp's
  pair follows from one classification of its states (`Top/Prog/CollOfCls`: `CollCls`): the
  collective a state is at, and a relation of the number of collectives, the time and that
  collective, which orders the lanes. The loader's relation is `LCls`; the softmax and correction
  warps' is `SCls` (`Lib/CollSched`) with their rounds as a parameter (`Mid`).
* **The softmax pair** uses sites, places and the ledger: a round's warp barrier and election follow
  its P-full arrival, so the role's collectives are twice the P-full arrivals less the ones to come
  (`soft_coll_inv`), and warp 0 has the startup's sixteen elections before. The events that block a
  lane right before a collective (the barrier after the register request, the last arrival on the
  correction warps' barrier, the wait before the warp barrier) are ready for a lane when they are
  for another of its warp (`Lemmas/Kernel/Progress/WarpReady`, `Softmax/Export/CollReady`).
* **The correction pair**: the rescale ballots are full ballots of the ledger, two per round
  (`CFits`); no blocking event of the role leads to a collective.
