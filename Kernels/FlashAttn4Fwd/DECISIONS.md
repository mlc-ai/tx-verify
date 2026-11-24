<!-- SPDX-License-Identifier: Apache-2.0 -->

# FlashAttention-4 forward: decision record

Every entry is a decision that the PTX ISA 9.5 text (`ptx-isa-9.5.txt`) does not give
directly. Each states what was decided, its basis in the specification (or "no basis"), the
alternative, and its kind:

- **stricter**: rejects programs or executions the specification would allow;
- **hardware-dependent**: relies on behaviour the specification does not state; it is an
  Assumption declared in `Kernels/FlashAttn4Fwd/Assumptions.lean` (built from the constructors
  of `Assumption/`) and is listed in the FA4 theorems;
- **launch obligation**: a fact about the host launch, a premise of the theorems;
- **scope**: a choice of what the theorems cover.

## Scope

### D-SCOPE-SHAPE: symbolic shape
- Decided: the theorems hold for any batch `b`, any head count `h` with `h_q = h_kv`,
  `seqlen_q` a positive multiple of 512, `seqlen_k` a positive multiple of 128 (the two may
  differ), cluster 2, block 512. Invariants use `ceil(s_k / 128)` and `ceil(s_q / 256)`; the
  divisibility conditions are separate `Pre` fields so that arbitrary lengths can be added
  later.
- Basis: user decision. The PTX fixes head dimension 128, fp16, non-causal, no LSE output,
  `seqlen_q > 256` (2-CTA kernel) and no split-KV.
- Alternative: one fixed shape (the generation instance, batch 1, 8192, 32 heads).
- Kind: scope.

### D-SCOPE-LAUNCH: launch-determined quantities are premises
- Decided: every quantity fixed by the launch and not by the PTX (grid, tensor maps,
  parameter values and bytes, the scheduler's divmod parameters) is a field of `Pre`. No
  register count appears in `Pre`.
- Basis: user decision.
- Kind: scope.

## Decoding: new instruction forms

### DEC-PARAM-OBJECT: `ld.param` of a by-value parameter object (THREAD-MOVE, PROG-DECODE)
- Form: `ld.param{.v2,.v4}.t d, [obj]` or `[obj+off]`, where `obj` is declared
  `.param .align a .b8 obj[n]`. FA4 uses `ld.param.b32` at offsets 0 and +4, and
  `ld.param.v2.b8` at +8, of its scheduler parameters.
- Semantics source: §5.1.6.1 (kernel parameters are read-only variables read with `ld.param`),
  §9.7.10.8 (`ld`: variable-plus-offset addressing, wider destination registers), §6.4.1
  (`[var+immOff]`), §9.4.1 Table 28 (zero-extension into a wider destination).
- Decisions:
  1. The bytes of an object come from a new launch field `Launch.paramBytes`, kept apart
     from the 64-bit scalar `Launch.params`; EXT-LAUNCH gains the obligation that
     `paramBytes name k` is byte `k` of the host's argument. Basis: §5.1.6.1 says the values
     come from the host; the host layout is not ISA text. Alternative: one byte-level
     representation for all parameters (rewrites the scalar-parameter proofs). Kind:
     launch obligation.
  2. Multi-byte elements are little-endian: the existing reading EXT-ENDIAN. Kind:
     hardware-dependent (existing reading, already listed for kernels that pack bytes).
  3. Element `j` of a vector access is at `off + j·size` and goes to register `j`: the
     existing reading EXT-VECTOR-ELEM.
  4. An access past the end of the object, or at a negative offset, is rejected. Basis:
     none (the ISA gives no meaning). Kind: stricter.
  5. The access size must divide both the offset and the declared alignment. Basis: §5.4.5,
     §6.4.1 (misaligned access is undefined). Alternative: check the run-time base. Kind:
     stricter.
  6. A wider destination register is accepted only for bit-size types, up to 64 bits.
     Basis: §9.4.1 Table 28 zero-extends `bN` sources; for other types the outcome depends on
     the register's declared type, which the decoder does not keep. Kind: stricter.
  7. All destination registers of one access must have the same width. Basis: none. Kind:
     stricter.
  8. Elements wider than 64 bits, `.v4.b64` and `.v8` are rejected (64-bit limit: stricter;
     the vector limits follow §9.7.10.8).
  9. `[p+off]` on a scalar parameter is rejected; `[p]` keeps the scalar rule. A by-value
     object whose size equals the access width, read as `ld.param.bN [obj]`, now reads the
     object's bytes instead of `Launch.params obj`. No existing kernel uses that form and no
     generated file changed. Kind: change of an unused form's meaning (recorded here).

### DEC-REG-LIST: comma-separated register declarations (PROG-DECODE)
- Form: `.reg .t a, b, c;`. Each name is one register of type `.t`, numbered in source order
  and scoped like any other name.
- Semantics source: §9.3 ("predicate registers can be declared as .reg .pred p, q, r;") and
  the §5.4.1 examples.
- Decision: a list holds plain names only; a list mixing in `name<n>` is rejected. Basis: the
  examples show only plain names. Kind: stricter.

### DEC-PRED-LOGIC: predicate `and`, `or`, `xor`, `not` (THREAD-INT, PROG-DECODE)
- Form: `{and,or,xor}.pred d, a, b` and `not.pred d, a`; also `not.b16`/`.b32`/`.b64`. FA4
  uses `not.pred` (46) and `and.pred` (5).
- Semantics source: §9.7.9.1–§9.7.9.4 (`.type = { .pred, .b16, .b32, .b64 }`; "Allowed types
  include predicate registers."; `not`: "Invert the bits in a ."), §9.3.2 (predicates are
  manipulated with `and`, `or`, `xor`, `not`).
- Decisions:
  1. One representation: the existing `andB`/`orB`/`xorB` and a new `notB`, with width 1 for
     `.pred`. At width 1 the operands are read as predicates (`readPred`) and the result is a
     predicate; at other widths the existing bit rule is unchanged. Basis: the ISA lists
     `.pred` as a type of the same instructions. Kind: representation.
  2. A `.pred` operand must be a predicate register; a constant is rejected. Basis: the
     text allows "predicate registers" and gives no meaning to a constant predicate. Kind:
     stricter.
  3. A `.pred` operand register holding a non-predicate value is a type error (fault), an
     unwritten one is `uninitialized`, as for guards. Kind: stricter (existing THREAD-REG
     reading of unwritten registers).

### DEC-INT-FORMS: `mul.hi`, `mul.wide` of 16-bit types, signed `shr`, `min`/`max` (THREAD-INT)
- Form: `mul.hi.{u,s}{16,32,64}`, `mul.wide.{u,s}16` (beside the existing `.{u,s}32`),
  `shr.{b,u,s}{16,32,64}` (beside the existing `.u`), `{min,max}.{u,s}{16,32,64}`. FA4 uses
  `mul.hi.u32` (8), `shr.s32` (9), `mul.wide.u16` (6), `max.s32` (5).
- Semantics source: §9.7.1.3 (`mul`: "d = t<2n-1..n>; // for .hi variant"; `.wide` "is
  supported only for 16- and 32-bit integer types"), §9.7.9.9 (`shr`: "Signed shifts fill with
  the sign bit, unsigned and untyped shifts fill with 0 ."; "Shift amounts greater than the
  register width N are clamped to N ."), §9.7.1.13–§9.7.1.14 (`min`/`max`: "d = (a > b) ? a :
  b; // Integer (signed and unsigned)").
- Decisions:
  1. The existing `mulWide` and `shr` forms are generalized, not duplicated: `mulWide` gains a
     width argument (default 32) and `shr` a signedness argument (default unsigned), so every
     existing term and its meaning are unchanged. The production decoder cache of Fp16Gemm8192
     and its code table were regenerated: their only change is the printed default `false` of
     `shr`. Kind: representation.
  2. `min`/`max` reuse the `setp` comparison (`compare` with `.lt`/`.gt`); `mul.hi` and signed
     `mul.wide` read two's complement through `toSigned`. Basis: the cited semantics. Kind:
     none (equal).
  3. `max.relu`/`min.relu` and the packed types (`.u16x2`, `.s16x2`, `.u8x4`, `.s8x4`) are not
     decoded. Kind: scope.

### DEC-FLOAT-FORMS: packed `.f32x2` arithmetic, `sub.f32`, `min`/`max.f32`, floating `setp`, `ex2.approx`, `rcp.approx` (PROG-DECODE, ASM-IDEAL)
- Form: `{add,sub}{.rnd}{.ftz}.f32x2`, `fma.rnd{.ftz}.f32x2`, `sub{.rnd}{.ftz}.f32`,
  `{min,max}{.ftz}.f32 d, a, b{, c}`, `setp.CmpOp{.ftz}.f32 p, a, b` (ordered and unordered
  comparisons), `ex2.approx{.ftz}.f32`, `rcp.approx{.ftz}.f32`. FA4 uses `fma.rn.f32x2` (200),
  `add.rn.f32x2` (127), `sub.rn.f32x2` (48), `add.rm.f32x2` (24), `max.f32` (180, 123 of them
  with three inputs), `sub.f32` (3), `setp.{ge,lt,ne,neu}.f32` (7), `ex2.approx.ftz.f32` (209),
  `rcp.approx.ftz.f32` (2).
- Semantics source: §9.7.3.3, §9.7.3.4, §9.7.3.6 (`.f32x2`: "fA[0] = a[0:31]; fA[1] =
  a[32:63];", element-wise operation; "The default value of rounding modifier is .rn ."; `fma`:
  "Rounding modifiers (no default):"), §9.7.3.11–§9.7.3.12 ("Store the maximum of a , b and
  optionally c in d ."), §9.7.7.2 and §9.3.1.2 (Tables 23 and 24: an unordered comparison
  equals its ordered counterpart on non-NaN operands), §9.7.3.21 (`ex2`: "The maximum ulp
  error is 2 ulp from correctly rounded result across the full range of inputs."), §9.7.3.13
  (`rcp.approx`: "The maximum ulp error is 1 across the full range of inputs.").
- Decisions:
  1. Decoding only. Core gives none of these forms a rule (it has no floating semantics), as
     for the existing `add`, `mul`, `fma` forms. Kind: scope.
  2. The new arithmetic forms keep their rounding modifier (`FloatRound`);
     `Assumption.idealReal` has a `FloatForm` for them only at `.rn` (`subRn`, `addRnF32x2`,
     `subRnF32x2`, `fmaRnF32x2`), so a kernel's ideal-real assumption can give the exact real result only to
     `.rn`. `add.rm.f32x2` (and every `.rz`/`.rm`/`.rp` form of `sub` and of `.f32x2`
     `add`/`sub`/`fma`) has no `FloatForm` and stays `noRule` under every scope. Basis: FA4's
     software `exp2` adds `1.5 * 2^23` with `.rm` to take an integer part; an exact sum would
     give it a wrong meaning. Its meaning is left to a dedicated Assumption. Alternative: exact
     for every mode, as the existing forms `add`, `mul`, `fma` of `.f32` and `mulF32x2` are,
     whose decoder drops the modifier (RmsNorm's `mul.rz.ftz.f32x2` is exact under its
     assumption naming `mulF32x2`). Those existing forms are unchanged; the two treatments
     differ and should be reconciled in the Core audit. Kind: stricter.
  3. `.f32x2` rules share the element reading `f32x2Elems` (low half first) with the existing
     `mul.f32x2` rule, whose result is unchanged. Kind: representation.
  4. `max`/`min` of two or three values are the real maximum/minimum (forms `max`, `min`);
     floating `setp` is the real comparison, unordered and ordered alike (form `setp`). Basis:
     under an ideal-real assumption no operand is NaN (THREAD-NUM faults on NaN), and on
     non-NaN operands the tables agree. The `+0.0 > -0.0` rule of `max` does not arise for
     reals. Kind: none (follows the cited text on reals).
  5. A non-finite constant has no real value: `0fFF800000` (`-inf`) read by `max.f32`,
     `setp.f32` or any arithmetic faults (`badValue`, existing THREAD-NUM). FA4 writes `-inf`
     for masked scores and compares the row maximum with it, so its numeric proof needs an
     interpretation of these values; Core is not relaxed. Kind: stricter.
  6. `ex2.approx` and `rcp.approx` decode to their own forms and have no rule in Core, in
     `Assumption.idealReal` or `Assumption.approxExact` (no `FloatForm` or `ApproxForm`): their
     meaning will come from a dedicated Assumption (approximate `exp2`, reciprocal). Kind:
     scope.
  7. `.ftz` is accepted and has no effect on ideal reals (as for the existing forms); `.sat`,
     `max.NaN`, `.abs`, `.xorsign`, `setp` `num`/`nan` and `.BoolOp` forms, and `.f64` are not
     decoded. Kind: scope.

### DEC-TENSOR-CACHE-HINT: tensor load with `.L2::cache_hint` (THREAD-TENSOR-ISSUE, PROG-DECODE)
- Form: `cp.async.bulk.tensor.4d.shared::cluster.global.tile.mbarrier::complete_tx::bytes`
  `.L2::cache_hint.cta_group::2 [dst], [map, {c0, c1, c2, c3}], [mbar], policy`. FA4 uses it for
  all 10 Q, K and V loads, with `policy` a 64-bit register set to 0.
- Semantics source: §9.7.10.28.5.3 (syntax `...{.cta_group}{.level::cache_hint}... [mbar]
  {, ctaMask} {, cache_policy}`; "When the optional argument cache_policy is specified, the
  qualifier .level::cache_hint is required. The 64-bit operand cache_policy specifies the cache
  eviction policy that may be used during the memory access. cache_policy is a hint to the cache
  subsystem and may not always be respected. It is treated as a performance hint only, and does
  not change the memory consistency behavior of the program."; with `.cta_group::2` the mbarrier
  may be "either the same CTA as the shared memory destination dstMem or in its peer-CTA").
- Decisions:
  1. The load shares the existing tensor-load rule; the policy operand is kept in the
     instruction (`cpTensor`'s last field `cachePolicy`, `none` when absent), is read at issue as
     a defined 64-bit value and enters no event. One helper, `cachePolicyRead`, now reads the
     policy of loads, stores and prefetches; the store and prefetch rules keep their meaning.
     Basis: the quoted text (a performance hint only). Alternative: drop the operand at decoding,
     as for the suspend-time hint of `mbarrier.try_wait`; an undefined policy register would then
     go unnoticed, unlike for stores. Kind: stricter (an undefined policy register faults; the
     text says nothing about it).
  2. `.L2::cache_hint` is accepted before or after `.cta_group` (after an optional
     `.multicast::cluster`), each qualifier at most once; its operand comes last, after
     `ctaMask`. Basis: the syntax line lists `.cta_group` first; FA4's PTX, which ptxas
     assembles, writes the hint first; the text gives the qualifier order no meaning. Other
     orders (CUTLASS writes `.cta_group::2` right after `.2d`) stay rejected. Alternative: the
     syntax order only (rejects FA4). Kind: scope (one more spelling of the same instruction).
  3. The mbarrier operand keeps the existing `cta_group::2` routing (THREAD-TENSOR-ISSUE: the
     mbarrier is in the destination's CTA or its peer). FA4 computes it with
     `and.b32 x, a, -16777217` (bit 24 of a shared address cleared); Core gives `and` on a shared
     pointer no meaning, so that address needs an FA4 Assumption. Kind: none here.
  4. Representation: the production GEMM decoder cache prints one more `none` per tensor load
     (`Data/Decoded.lean`, `Flow/Code.lean` regenerated); no proof changed. Kind: representation.

### DEC-MMA-FORMS: `tcgen05.mma` without lane mask, constant `enable-input-d`, `[a-tmem+imm]` (THREAD-TC, PROG-DECODE, THREAD-TC-MMA-RESULT-LAYOUT)
- Form: `tcgen05.mma.cta_group::2.kind::f16 [d], a-desc, b-desc, idesc, en` (QK: 32 sites, `en`
  the constant 0 or 1) and `tcgen05.mma.cta_group::2.kind::f16 [d], [a-tmem + imm], b-desc,
  idesc, en` (PV: 32 sites, `imm` from 0 to 0x38, `en` a predicate register or 1). QK uses idesc
  `0x10200010` (M = 256, N = 128, FP16 in, FP32 out, K-major A and B); PV `0x10210010` (B
  transposed: MN-major V). Shared descriptors use the 128-byte swizzle, stride 1024, base offset
  0; Q and K advance by 32 bytes per K step inside the swizzle atom.
- Semantics source: §9.7.18.10.10.1 (syntax; "The operation of the form D = A*B is issued when
  the input predicate argument enable-input-d is false."; "If a bit in the mask is 1, then the
  corresponding lane in the Tensor Memory for the resultant matrix D will not be updated."),
  §9.7.18.8.5 and §9.7.18.12.1 (examples without a mask, e.g. "tcgen05.mma.cta_group::2.kind::tf32
  [taddr0], adesc, bdesc, idesc, p;"), §4.5.3 (predicate constants), §9.7.18.1.1 (Tensor Memory
  addresses), §9.7.18.10.5 (Layout A, Figures 211–212), §9.7.18.4.1 Tables 49–50, §9.7.18.4.2
  Table 51 (transpose B is bit 16), §9.7.18.3.3 and §9.7.18.10.6 Table 67 (canonical layouts,
  swizzle atoms), §9.7.18.6.2 (pipelined pairs, including A reads).
- Decisions:
  1. Without the lane-mask operand the mask is `4 * group size` zero words: every lane is
     written. Basis: the ISA's examples use the form, and only a 1 bit of a mask disables a lane.
     Kind: none (follows the cited text).
  2. `enable-input-d` is a predicate register (its value must be a predicate, as before) or an
     integer constant, false exactly when zero. One representation: the operand is an `Opnd` in
     `tcMma` and `tcMmaTs`, `.ws` included. Basis: §4.5.3 ("integer constants may be used as
     predicates"). Kind: representation; the production GEMM decoder cache and TcGemm's `Spec.lean`
     listing print `(.reg n)` for the predicate register `n`; the proof lines that spell the
     instruction out (two in `Fp16Gemm8192/Proof/Thread/InputOps.lean`, two in
     `TcGemm/Proof/Thread/Tmpl.lean`, the library lemma `tc_mma`) changed accordingly.
  3. `[a-tmem+imm]` is the register plus `imm` in the column field (THREAD-TC; `tcMmaTs` gains
     the field `aOff`). An offset that leaves the column field (and would change the lane field)
     faults. Basis: §9.7.18.1.1 ("Tensor Memory addresses are 32-bit wide and specify two
     components."; lane index bits 31-16, column index bits 15-0): an address has no byte unit,
     so the offset adds to the column. First recorded as the reading EXT-TMEM-ADDR-OFFSET; on
     2026-11-15 the user decided it is the plain reading of §9.7.18.1.1 and it became an
     ordinary Core rule. Kind: equal, with the carry case stricter. The destination
     `[d-tmem]` stays a register without offset (scope).
  4. A in Tensor Memory with `cta_group::2` and M = 256: the existing A cell map (`aCell`) puts
     row `i` in lane `i % 128` of the even CTA (`i < 128`) or the odd CTA, two FP16 elements per
     32-bit column, the lower-numbered one in the low half. EXT-TCFIG now states this case and
     its source (CUTLASS `SM100_MMA_F16BF16_2x1SM_TS`, `tmem_frg_2sm`); no probe checks it.
     Layout B (M = 128 with `cta_group::2`) has no A cells and is unsafe. Basis: the spec gives
     Layout A only as figures and says nothing of A's packing for 16-bit types. Kind: reading
     (EXT-TCFIG, to be disclosed by FA4).
  5. Reads of A from Tensor Memory are Tensor Memory reads with the existing rules: conflict
     checked against every write of the cell (ERR-TMEM-RACE), ordered after the write
     they read (DEP-TC-LOAD-VALUE `AReadSource`), before a later D write or copy of the same warp
     by the pipelined pairs of §9.7.18.6.2, and covered by ERR-TC-MMA. Unchanged.
  6. MN-major B with the 128-byte swizzle, and a descriptor start inside the swizzle atom with
     base offset 0, are the existing THREAD-TC-SHARED-ADDRESS rules (canonical offset, then the
     XOR on the absolute address). Table 50's formula `(pattern start addr >> 0x7) & 0x7` gives 0
     for a pattern starting at a 1024-byte boundary, which holds when Q, K and V lie 1024-byte
     aligned (FA4's shared buffer is declared `.align 1024`; a premise of the proof).
     `Tests/Tc/TcMmaForms.lean` checks that the bytes FA4's Q, K-step and V descriptors address are
     the bytes the 128-byte-swizzled tensor copies wrote. Kind: none (existing rules).
  7. `tcgen05.commit.cta_group::2.mbarrier::arrive::one.shared::cluster.multicast::cluster.b64`
     with mask 3 was already decoded (as in the GEMM). Kind: none.

### DEC-MBAR-STATE: non-cluster `mbarrier.arrive` with a state destination (THREAD-TMA, PROG-DECODE)
- Form: `mbarrier.arrive.shared.b64 state, [addr], count` (FA4: 10) and
  `mbarrier.arrive.expect_tx.shared.b64 state, [addr], txCount` (FA4: 7), `state` a `.b64`
  register. FA4 never reads any of these 17 registers.
- Semantics source: §9.7.15.16.16 ("mbarrier.arrive operation on an mbarrier object located in
  .shared::cta returns an opaque 64-bit register capturing the phase of the mbarrier object prior
  to the arrive-on operation in the destination operand state. Contents of the state operand are
  implementation specific."; "Sink symbol ‘_’ is mandatory for the destination operand for such
  cases." for `.shared::cluster`), §5.1.7 ("If no sub-qualifier is specified with the .shared
  state space, then it defaults to ::cta .").
- Decisions:
  1. One rule: the existing `mbarArrive` form gains a state destination (`state`, `none` for the
     sink), and the event is the existing `.arrive` event of the `.shared::cta` rule, with the
     same object, counts, `.release.cta` default and OBJ-MBAR-* / MEM-MBAR-SYNCHRONIZES rules. `.shared` is
     `.shared::cta`, as the decoder already treats `mbarrier.init` and `mbarrier.try_wait`.
     Kind: representation.
  2. The state register holds no value after the arrival (`mbarStateDest`): a later read of it is
     an `uninitialized` fault. Basis: the contents are implementation specific, so no use of them
     has a meaning in the model. Alternative: an opaque state value that `test_wait` could consume
     (no decoded instruction consumes one). Kind: stricter.
  3. A register destination with `.shared::cluster` is rejected, as the text requires the sink.
     Kind: equal.
- Effect on Consistent and Unsafe: none on executions without a state destination (every
  existing kernel uses the sink; the existing terms elaborate to `state := none` and their
  templates are unchanged). With a state destination the event, and so every execution
  constraint, is the one of the sink form; the only new unsafe case is a read of the state
  register (`HasUb` through the `uninitialized` fault).

### DEC-VOTE-BALLOT: `vote.sync.ballot.b32` (THREAD-VOTE, DEP-WARP-VOTE, PROG-DECODE)
- Form: `vote.sync.ballot.b32 d, {!}a, membermask` (FA4: 2, `membermask` -1, unguarded, `d`
  only compared with 0).
- Semantics source: §9.7.15.10 ("vote.sync will cause executing thread to wait until all
  non-exited threads corresponding to membermask have executed vote.sync with the same qualifiers
  and same membermask value before resuming execution."; "In this form, vote.sync.ballot.b32
  simply copies the predicate from each thread in membermask into the corresponding bit position
  of destination register d , where the bit position corresponds to the thread’s lane id. A
  thread not specified in membermask will contribute a 0 for its entry in vote.sync.ballot.b32 .";
  "The behavior of vote.sync is undefined if the executing thread is not in the membermask .").
- Decisions:
  1. A new event `vote mask a ballot` and Consistent field `VoteOk`: the `n`-th ballots of the
     lanes of a warp form an instance; every lane of the mask has its `n`-th ballot with the same
     mask or has exited before it; the ballot's bit of a lane of the instance is its predicate,
     of a lane outside the mask 0. Lanes may reach the instance from different source positions,
     as for `shfl.sync`. Kind: equal.
  2. Only the full member mask, in a CTA whose size is a multiple of 32, has a rule; other masks
     are `noRule`, as for `shfl.sync`. The `.all`, `.any`, `.uni` modes are not decoded.
     Kind: scope.
  3. The bit of a lane of the mask that exited before the instance is unconstrained. Basis: the
     text gives an exited thread no predicate to copy. Alternative: 0, as for a lane outside the
     mask. Kind: stricter (every value is kept).
  4. A guarded `vote.sync` needs a warp-uniform guard (ERR-NONUNIFORM-GUARD). Basis:
     the text does not say whether a predicated-off lane of the mask takes part. Kind: stricter.
  5. The instance is not a `Rendezvous`: no `Observed`/`Enables` edge relates one lane's ballot
     to another lane's return. Kind: stricter (more executions).
- Effect on Consistent and Unsafe: `Consistent` gains `vote : VoteOk`, which constrains only
  executions with ballot events (none in existing kernels): a ballot event exists only with its
  whole instance, and its value is fixed on the lanes that take part. No base causality,
  `SyncObserved`, `DepStep` or `FairRun` change. New unsafe cases: a guarded ballot whose lanes may
  disagree on the guard (`WarpDivergent`), and the `noRule`/type faults of THREAD-VOTE
  (`HasUb`).

### DEC-BAR-ARRIVE: `bar.arrive a, b` (THREAD-BAR, OBJ-CTA-BARRIER-SYNC, ERR-BARRIER-MISMATCH)
- Form: `bar.arrive a, b` (= `barrier.arrive.aligned a, b`) and `barrier.arrive a, b`. FA4:
  `bar.arrive %r682, 64` (3, register barrier) and `bar.arrive 2, 416` (2), which meet
  `bar.sync %r287, 64`, `bar.sync %r288, 64` and `bar.sync 2, 416`. Register barrier ids already
  worked for `bar.sync` (THREAD-BAR reads the operand with `readBits`).
- Semantics source: §9.7.15.1 ("barrier{.cta} instruction causes executing thread to wait for all
  non-exited threads from its warp and marks warps’ arrival at barrier."; "barrier{.cta}.arrive
  does not cause executing thread to wait for threads of other participating warps."; "The
  barrier{.cta}.sync or barrier{.cta}.red or barrier{.cta}.arrive instruction guarantees that when
  the barrier completes, prior memory accesses requested by this thread are performed relative to
  all threads participating in the barrier. The barrier{.cta}.sync and barrier{.cta}.red
  instruction further guarantees that no new memory access is requested by this thread before the
  barrier completes."; "Note that a non-zero thread count is required for barrier{.cta}.arrive .";
  "Different warps may execute different forms of the barrier{.cta} instruction using the same
  barrier name and thread count."; "Care must be taken to keep a warp from executing more
  barrier{.cta} instructions than intended ( barrier{.cta}.arrive followed by any other
  barrier{.cta} instruction to the same barrier) prior to the reset of the barrier.";
  "bar{.cta}.arrive is equivalent to barrier{.cta}.arrive.aligned ."), §8.9.4 ("A bar{.cta}.sync or bar{.cta}.red or
  bar{.cta}.arrive operation synchronizes with a bar{.cta}.sync or bar{.cta}.red operation
  executed on the same barrier.").
- Decisions:
  1. One barrier model: the existing `bar` event gets a form `BarMode` (`.sync`, `.arrive`), and
     an arrive is an ordinary warp arrival of the existing named resource (`CtaBarrier.arrive`,
     unchanged): it counts in the generation with the same count check, duplicate check and
     exit rule. `IsBarrier`/`CtaBarK` keep meaning a `bar.sync` arrival; `IsBarArrival` and
     `CtaBarArrivalK` are arrivals of either form. Kind: representation.
  2. Synchronization (`CtaBarSync`): the source arrival may be either form, the target must be a
     `bar.sync`; accesses of a thread after its `bar.arrive` are ordered by nothing.
     Basis: §8.9.4 and the "further guarantees" sentence (only sync/red). Kind: equal.
  3. Blocking: passing a `bar.arrive` needs no completed generation. The text's wait for the
     thread's own warp is kept only as an order on the resource history: a thread's `bar.arrive`
     arrivals are recorded before any of its later barrier operations (arrival or exit) are
     (`CtaBarBlocking`). A thread may pass its `bar.arrive` before the warp's record exists, and
     the warp wait is no `Rendezvous` (no `Observed`/`Enables` edge). Alternative: a full warp
     rendezvous. Kind: stricter (more executions).
  4. A zero count of `bar.arrive` is a `badBarrier` fault; a whole-CTA count is normalized to
     the omitted form, as for `bar.sync`. Kind: equal (zero) / representation (normalization).
  5. ERR-BARRIER-MISMATCH, new clause `BarArriveMismatch`: lanes of a warp at their `k`-th barrier
     instruction must agree on id, count and form (a warp arrival made of `bar.sync` and
     `bar.arrive` lanes has no meaning: stricter). Participants of one generation in different
     warps are not compared by position (EXT-BAR-PARTICIPANTS, 2026-11-15). The exit clause
     (ERR-ALIGNED-MISMATCH) counts aligned whole-CTA barriers of both forms.
     Kind: reading (EXT-BAR-PARTICIPANTS) / stricter (mixed warp).
  6. A guarded `bar.arrive` needs a uniform guard, as an aligned instruction. Kind: equal
     (existing ERR-NONUNIFORM-GUARD).
- Effect on Consistent and Unsafe:
  - Consistent: arrive events are history sources (`CtaBarSources`) and count in generations;
    `CtaBarSync` gains edges from accesses before a `bar.arrive` to accesses after a `bar.sync`
    of the same generation (base causality, hence `stageCausality`); a record pair lets a `bar.arrive`
    be a witness of a `bar.sync` return (`SyncObserved`, `DepStep`); the dependency layer gains the
    record-order need above; `ObjectOrder .ctaBar` orders arrive records like sync records.
    A `bar.arrive` is never a blocking return, so it adds no `GuardedBy` edge. `FairRun` and
    progress are unchanged in form; a `bar.arrive` is a counted event that is never blocked.
  - Unsafe: `CtaBarFault` now also fires for an arrival of either form that the resource cannot
    perform (count mismatch between a `bar.arrive` and a `bar.sync` of one generation; a warp
    arriving again on the same barrier before the generation completes); `BarArriveMismatch`
    (mixed forms in a warp); a zero count (`HasUb`); a divergent guard (`WarpDivergent`).
  - FA4: barrier 2 (count 416) is reached by `bar.sync` at four source positions (PTX lines
    715, 1505, 1619, 4521) and by `bar.arrive` at two (4513, 5704); barriers `%r287`/`%r288`
    and `%r682` (count 64) likewise. Under EXT-BAR-PARTICIPANTS warps of one generation may
    reach it from different positions.
  - Existing kernels: none has a `bar.arrive` event (`Kernel.NoBarArrive`, checked per kernel),
    so every new clause is vacuous and each kernel's Consistent and Unsafe are unchanged; their
    proofs use the `Fact kernel.NoBarArrive` instance to discharge the arrive cases.

## Assumptions (hardware-dependent, listed in the FA4 theorems)

Declared in `Assumptions.lean` (`Assumptions.all`); the constructors are in
`Assumption/`. Each new Core hook is off by default and consulted in one place, with a
Core theorem that the semantics is unchanged when no assumption selects the site.

### ASM-A0 `idealArith`: the forms read as exact real arithmetic (ASM-IDEAL)
- Decided: `Assumption.idealReal "fa4-fwd-ideal-arith"` with the float forms `add.f32`,
  `mul.f32`, `sub.rn.f32`, `add.rn.f32x2`, `sub.rn.f32x2`, `fma.rn.f32x2`, `mul.f32x2`,
  two- and three-input `max.f32`, floating `setp`, `setpInf` (a `setp` with an infinite constant
  operand, ASM-A1) and `cvt.rn.f16x2.f32`, and the MMA form `kind::f16` with f16 inputs and an
  f32 accumulator. Each selected instruction produces the exact real result (`.float fmt x`);
  the kernel's other floating instructions are read by `approx` and `swExp2` (ASM-A2, ASM-A3),
  and an instruction no assumption selects has no rule. The kernel has no `min.f32`, no scalar `fma.f32` and no `cvt.f32.f16`, so these forms are
  not selected. `add.rm.f32x2` (the rounding step of the software `exp2`) is not selected: it
  has no exact real meaning and is covered only inside `swExp2` (ASM-A3).
- Basis: the PTX rounds these operations (the floating-point instructions of §9.7.3: ".rn
  mantissa LSB rounds to nearest even"); `Post` states the exact real attention, so the theorem
  needs the operations read as exact. The scope is the list above and nothing else.
- Alternative: an error-bounded floating model (not available in Core; OPEN-NUM).
- Kind: not-conservative numerics (OPEN-NUM); no Core change.

### ASM-A1 `setpInf`: comparison with an infinite constant (ASM-IDEAL)
- Decided: `FloatForm.setpInf fmt` is the form of `setp.CmpOp{.ftz}.<fmt>` with an infinite
  `0f` constant operand (`0fFF800000`, `0f7F800000`). Under an `idealReal` scope that names it,
  the comparison is made in the extended reals (`erealCompare`), the constant read as that
  infinity and every other operand as its real (THREAD-NUM). Only constants are infinite: a
  register holding an infinity still faults. The plain `.setp` form excludes these
  instructions, so a scope naming only `.setp` gives them `noRule` (as before they faulted
  with `badValue`). FA4 uses it at pc 1860 and pc 2926 (`setp.neu.f32 p, x, 0fFF800000`).
- Basis: §4.5.2 (`0f` constants are IEEE 754 bit patterns, so `0fFF800000` is −∞);
  §9.3.1.2 ("If both operands are numeric values (not NaN ), then these comparisons have the
  same result as their ordered counterparts.").
- Alternative: reading `-inf` as a very negative real (changes the meaning of the program);
  or keeping the fault, which makes FA4 unprovable.
- Kind: hardware-dependent (ideal arithmetic; constructor extension, no Core change).

### ASM-A2 `ex2.approx` and `rcp.approx` as exact (ASM-APPROX)
- Decided: `ApproxForm.ex2 fmt` reads `ex2.approx{.ftz}.<fmt>` as the exact `2 ^ a`
  (`Real.rpow`); `ApproxForm.rcp fmt` reads `rcp.approx{.ftz}.<fmt>` as the exact `1 / a`,
  undefined (`badValue`) at `a = 0`. The ulp error (2 and 1 ulp) is ignored, and with `.ftz`
  a result the hardware flushes to zero (`2 ^ a` for `a` below about −126) is the exact
  positive value (OPEN-NUM).
- Basis: §9.7.3.21 ("Raise 2 to the power a ."; "The maximum ulp error is 2 ulp from
  correctly rounded result across the full range of inputs."; "ex2.ftz.f32 flushes subnormal
  inputs and results to sign-preserving zero."); §9.7.3.13 ("Compute 1/a , store result in d
  ."; "The maximum ulp error is 1 across the full range of inputs.").
- Alternative: a bounded-error interval semantics; or keeping `noRule`, which makes FA4
  unprovable.
- Kind: hardware-dependent (not-conservative numerics; constructor extension, no Core change).

### ASM-A3 `segmentRule` hook and `segmentExact` / `cuteExp2` (ASM-SEGMENT)
- Decided: a new `Assumption` field `segmentRule : Launch → Nat → TState → Option (Exec TState)`
  (default `none`), consulted at exactly one place, the start of `execLocalA` (THREAD-LOCAL),
  before the instruction rules: the first assumption that selects a segment at the thread's
  state gives the outcome of the straight-line code from its `pc` as one local step.
  `segmentExact K name T sites why` selects it at exactly `sites` where the code of `K`
  matches one of the template's shapes (unguarded instructions of the given forms, one
  register per slot, no register shared by two slots); the step writes each output with
  `.float .f32 (T.fn x)`, sets (defining shape) or checks (reusing shape) the constant
  registers with exactly the values Core's moves of those literals produce, clears every other
  register the code writes, and continues after it. `cuteExp2`
  ([Assumptions/Exp2Template.lean](Assumptions/Exp2Template.lean); 31-instruction defining shape,
  21-instruction reusing shape) has `fn x = 2 ^ x` (`Real.rpow`), the exact function, not
  `2 ^ max(x, −127)`: the clamp at −127 and the degree-3 polynomial error are recorded
  approximations (OPEN-NUM) and named in the template text.
- Basis: none in the ISA for reading code as a function; the instructions are §9.7.3.3
  (`.rm` "rounds toward negative infinity"), §9.7.3.6, §9.7.3.12, §9.7.9.8, §9.7.1.1,
  §9.7.10.3/4. Source: CuTeDSL `cute/math` software exp2.
- Alternative: `2 ^ max(x, −127)` (the closest exact reading of the code; it makes `Post`
  false for logits more than 127 below the row max, which `Pre` does not exclude); a
  directed-rounding Core rule for `add.rm` plus integer reasoning on float encodings (does not
  give `2 ^ x` in the ideal model).
- Kind: hardware-dependent (trust; not-conservative numerics); Core interface change (new
  field, `execLocalA` consults it).

### ASM-A4 `pairEvenAt`: the peer bit (ASM-PEER-BIT)
- Decided: through the same `segmentRule` hook, `pairEvenAt K name sites why` reads, at exactly
  `sites`, the unguarded `and.b32 d, a, -16777217` as: `a` holds an integer `x < 2^24` (a
  `.shared::cta` window address, `mov.b32 __dynamic_shmem__0` + offsets; Core reads it as the
  executing CTA's byte), the cluster size is even, and `d` receives
  `.sharedPtr 32 false cta even x` — the `.shared::cluster` address of byte `x` in the even
  CTA of the pair (`L.peerCta cta (rank / 2 * 2)`), with the executing CTA as producer.
  Otherwise the step faults. The `cta_group::2` tensor load reads its mbarrier operand with
  `mbarClusterLoc` → `readSharedAddress … generic := false, cluster := true`, which accepts
  exactly this pointer and gives `⟨.shared, even, x⟩`; so the odd CTA's copies signal the even
  CTA's barrier (for the even CTA, its own).
- Basis: §9.7.10.28.5.3 ("When .cta_group::2 is specified, the mbarrier object mbar can be in
  shared memory of either the same CTA as the shared memory destination dstMem or in its
  peer-CTA"); the ISA defines no bit encoding of `.shared::cluster` addresses (its conversion is
  `mapa`). Evidence: CUTLASS `Sm100MmaPeerBitMask = 0xFEFFFFFF`
  (`include/cute/arch/copy_sm100_tma.hpp`), applied to the mbarrier address of every SM100 2-SM
  TMA load.
- Alternative: Core's `and.b32` (integer result, the odd CTA's copies signal its own barrier:
  the leader's full barriers never complete); a Core encoding of cluster addresses (not in the
  ISA).
- Kind: hardware-dependent (address encoding).

### ASM-A5 `tcLdWait` hook and `tcLdDataflowAt` (ASM-TCLD-DATAFLOW)
- Decided: a new field `tcLdWait : Nat → Bool` (default false), consulted at exactly one place,
  the `tcgen05.ld` arm of `eventTmpl` (`tcLdTmpl`, THREAD-RUN): at a selected site the load
  (sub-step 0) continues at the same `pc` with sub-step 1, which performs the event of
  `tcgen05.wait::ld` (`.tc .waitLd`) without re-reading operands. All ordering then comes from
  Core's existing rules for `wait::ld` (`WaitBefore` in DEP-TC-LOAD-VALUE `LoadBefore`/
  `LoadStable` and in `TcMma.CompletedBefore` for the release of the allocation).
  `tcLdDataflowAt K name sites why` selects a site only when the decidable static check
  `ldConsumedAt K pc` holds: on the straight path after the load (no `bra`, no guard, no
  unclassified instruction), every destination register is read by a local instruction other
  than a move (`mov`, `pack`, `unpack`, unsigned `cvt`, `selp` pass the dependency on) before
  the thread's next instruction that is neither local nor a `tcgen05.ld`, and no pending value
  is overwritten first. FA4 pins `tcLdSites_consumed` by `decide +kernel`.
- Basis: §9.7.18.6.4.5 ("For tcgen05.ld , an intra-thread ordering through true register
  dependency will be respected regardless of the presence or absence of other forms of
  synchronization. This form of register dependency does not imply any other form of
  ordering."; "To enforce such memory orderings and avoiding anti-dependency hazards around
  tcgen05.ld , tcgen05.wait::ld must be used."). The assumption goes beyond it: consumption of
  the registers is taken as completion of the Tensor Memory read.
- Alternative: regenerate the PTX with `tcgen05.wait::ld` (removes the assumption); a Core
  rule ordering a load by its consumers (would change every kernel's semantics).
- Kind: hardware-dependent; Core interface change (new field, `eventTmpl` tcLd arm).

- Correction (after review): the implicit `tcgen05.wait::ld` (sub-step 1) first continued with
  `next t`, which kept sub-step 1, so the next listed load at the following pc fired only its
  wait and a vector store started at the wrong element. It now continues with
  `{ next t with sub := 0 }`, as every other multi-step instruction ends.

### ASM-A6 `dupStores` hook and `identicalStoresAt` (ASM-DUP-STORE): resolved by ERR-DATA-RACE
- Resolved (2026-11-15, user decision): the hook `dupStores`, the constructor
  `identicalStoresAt` (with `dupStoreSites`, contract ASM-DUP-STORE) and FA4's assumption
  `dupStore` are removed. Core's race rule itself does not count as a race two writes of the same
  bytes (the same footprint) with the same value (ERR-DATA-RACE `SameValueWrites`), for every write
  kind the model has; values are compared as byte lists, and a pair of which one write is not
  yet performed is compared in the executions that perform both. A read unordered with either
  write is still a race, and writes with different values or a partial overlap remain races
  (ERR-DATA-RACE, ERR-MIXED-SIZE). `Race` takes no assumption list again (`Race L X`).
- Basis: §8.7.2 ("But these axioms are sufficient to describe the behavior of a PTX program with
  only uniform-size data-races ."), §8.9.6 ("Two overlapping writes are unrelated in coherence
  order if they are in a data-race , which gives rise to the partial nature of coherence
  order ."), §8.10.1 and §8.10.6 (coherence and causality constrain a read by the writes that
  precede it, so it reads the common bytes from either write).
- Previously: FA4 named its four output tensor-store sites `[1169, 1171, 1177, 1178]`; at those
  sites the stores of one instruction execution by the lanes of one warp were exempt from
  `Race`, and an execution in which two of them wrote one byte with different values was
  undefined (the assumption's `ub`).
- FA4 now proves that the 32 lanes' stores of one element write the same byte
  (`Output.item_bytes_eq`), so O's conflicts are ordered but for identical-value pairs
  (`outputOrdered`). The final memory uses CORRECT-FINAL's agreeing co-maximal writes, unchanged
  (`IsFinal.of_identical_writers`, `Lemmas/Kernel/IdenticalWrites.lean`). The progress layer's
  `ReadsOrdered` no longer follows from the absence of races alone (the identical stores are
  unordered); it uses the order of the conflicts outside O (`Safety.outside_ordered`), which
  `Proof.correct` supplies to `progress_goal` from the safety layer's inputs.
- Kind: uniform-size race reading in Core (ERR-DATA-RACE, direction stricter for every other race),
  applies to every kernel.

### ASM-A8 `barSitesAt` (ASM-BAR-SITES): resolved by EXT-BAR-PARTICIPANTS
- Resolved (2026-11-15, user decision): the hook `barSameSite`, the constructor `barSitesAt` and
  FA4's assumption `barSites` are removed. Core reads "the same barrier{.cta} instruction" of
  different warps as the same barrier name and thread count, not the same program position
  (EXT-BAR-PARTICIPANTS, beside ERR-BARRIER-MISMATCH). ERR-BARRIER-MISMATCH compares the positions of
  the lanes of one warp only; across warps the barrier resource compares the count
  (`countMismatch`, `CtaBarFault`).
- Basis: §9.7.15.1 ("All threads in warp (except for those have exited) must execute
  barrier{.cta} instruction in convergence."; "Different warps may execute different forms of
  the barrier{.cta} instruction using the same barrier name and thread count.").
- Previously: FA4 named barrier 2's sites `[[544, 1207, 3755], [3749, 4895]]` as one
  instruction for the participants of a generation.
- Kind: reading (EXT-BAR-PARTICIPANTS), applies to every kernel with a CTA barrier.

### ASM-A9 `commitInOrder` hook and `commitOrderAt` (ASM-COMMIT-ORDER)
- Decided: a new field `commitInOrder : Nat → Bool` (default false). The Core relation that
  gains the edge is the enabling step of the lifetime order, ERR-SHARED-LIFETIME
  `LifetimeStep` (used by `LifetimeOrder` and `CompletedBefore`): a third arm
  `c.2 = true ∧ d.2 = false ∧ CommitNext A X c.1 d.1`, from the completion of the arrive-on at
  rank `r` of a commit at a selected site to the start of the arrive-on at rank `r` of the same
  thread's next commit (both performed). `Enables` and `EnablingCoherent` are unchanged, so the
  edge itself adds no constraint on executions; it lets a lifetime proof use the next commit's
  arrive-on. The edge needs the selected arrive-on to be performed, so `commitOrderAt` also sets
  its `wf` to `Assumption.commitPerformedAt sites`: when the issuing thread's next commit's
  arrive-on at rank `r` is performed, so is the selected commit's at rank `r` (an execution in
  which only the next one is performed is removed). FA4's `Lifetime.SelectedPerformed asms X`
  is this constraint (`Lifetime.selectedPerformed`, from `Consistent.asm` and
  `Assumptions.all_commitInOrder`). FA4: pc 995 (Q0-empty commit L1321; its next commit is pc
  999, observed by the loader tail wait L696). Litmus `Tests/Tc/CommitOrderLitmus.lean`.
- Basis: none; §9.7.18.12.1 ("Makes the mbarrier object track the completion of all prior
  async-tcgen05 operations initiated by the executing thread.") does not order two commits'
  arrive-ons. Hardware processes one thread's commits in order (CUTLASS producer-tail drains
  only the last stage).
- Alternative: an `Enables` edge (as first designed): it would also enter EnablingCoherent and
  break the proof device "every Enables edge is a `Waits` path" used by all extension and
  existence lemmas; an exit cluster barrier in the kernel (not in the frozen PTX). For the
  performance constraint: a Core field of `Consistent` consulting the hook (it would change every
  construction of `Consistent`); the assumption's own `wf` is the ASM-INTERFACE place for a
  condition on executions. A progress proof of FA4 must show the constraint of the executions it
  builds.
- Kind: hardware-dependent; Core interface change (`LifetimeStep`); the `wf` removes executions
  (only those in which the selected arrive-on is never performed while the next one is).

### ASM-A10 `regSitesAt` (ASM-REG-SITES): resolved by EXT-BAR-PARTICIPANTS
- Resolved (2026-11-15, user decision): the hook `regSameSite`, the constructor `regSitesAt` and
  FA4's assumption `regSites` are removed. Core reads "the same setmaxnreg instruction" of
  different warps as the same request (direction and count), not the same program position
  (EXT-BAR-PARTICIPANTS). ERR-SETMAXNREG compares the positions of the requests of one
  warp only; direction and count are compared across the warpgroup as before.
- Basis: §9.7.21.5 ("The same setmaxnreg instruction must be executed by all warps in a
  warpgroup ."; "The mandatory .sync qualifier indicates that setmaxnreg instruction causes the
  executing thread to wait until all threads in the warp execute the same setmaxnreg
  instruction before resuming execution.").
- Previously: FA4 named warpgroup 3's four `setmaxnreg.dec 72` sites `[[191, 194, 541, 1130]]`
  as one instruction.
- Kind: reading (EXT-BAR-PARTICIPANTS), applies to every kernel with `setmaxnreg`.

### ASM-A11 `uniRendezvous` hook and `warpRendezvousAt` (ASM-WARP-RENDEZVOUS): resolved by the generic EXT-DEPENDENCY-ORDER
- Resolved (2026-11-15, user decision): the hook `uniRendezvous`, the constructor
  `warpRendezvousAt` (contract ASM-WARP-RENDEZVOUS, reading EXT-WARP-RENDEZVOUS) and FA4's
  assumption `warpRendezvous` are removed, with `FullRendezvous`, `RendezvousBefore` and
  `RendezvousExempt`. ERR-NONUNIFORM-GUARD decides whether two executions of one position by two
  lanes may be executed together by the execution-dependency order (`DepBefore`, the transitive
  closure of MEM-BASE-CAUSALITY, program order and `Rendezvous`, MEM-OBJECT-ORDER-CAUSALITY), for every kernel and every
  guarded uniform instruction (EXT-DEPENDENCY-ORDER, beside ERR-NONUNIFORM-GUARD). It is used only
  by this check; it enters neither base causality, `stageCausality` nor any memory rule.
- Basis: §9.7.15.15 ("The mandatory .sync qualifier indicates that elect causes the executing
  thread to wait until all threads in the membermask execute the elect instruction before
  resuming execution."), §9.7.10.6 ("shfl.sync will cause executing thread to wait until all
  non-exited threads corresponding to membermask have executed shfl.sync with the same
  qualifiers and same membermask value before resuming execution."), and the other blocking
  sentences of `Rendezvous` (§9.7.15.1, §9.7.15.2, §9.7.15.3, §9.7.18.7.1, §9.7.18.8, §9.7.21.5);
  that executions so ordered are not "currently executing this instruction" together
  (§9.7.14.3) is the reading.
- Previously: FA4 selected the 16 poll branches of the loader's loop (262, 292, 322, 352, 383,
  423) and of the MMA warp's loop (596, 602, 671, 752, 755, 809, 877, 1004, 1007, 1058). The proof
  keeps them as the positions where it meets the rounds through the collectives (`rdvSites` in
  `Proof/Interface/WarpSync.lean`, no longer an assumption); `PollRoundsMet.of_collectives` now
  produces a `Rendezvous` edge (`rendezvous_of_coll`) followed by program order, a `DepBefore`
  path. Litmus `roundsElect_not_flagged` (`Tests/Sync/WarpUniformLitmus.lean`, no assumption).
- Kind: reading (EXT-DEPENDENCY-ORDER), applies to every kernel with a guarded `bra.uni`.

### ASM-A12 `pairAllocOrder` hook and `pairAllocOrderAt` (ASM-PAIR-ALLOC-ORDER): resolved by the generic EXT-PAIR-ALLOC-ORDER
- Resolved (2026-11-15, user decision): the hook `pairAllocOrder`, the constructor
  `pairAllocOrderAt` (contract ASM-PAIR-ALLOC-ORDER) and FA4's assumption `pairAlloc` are removed,
  with the thread fact `PairAllocFacts` that located the selected site. Core applies
  EXT-PAIR-ALLOC-ORDER to every paired `tcgen05.alloc.cta_group::2` (every pair in
  `Execution.tmemPairing`), without site selection: a covering allocation of the cell's CTA whose
  request is paired with the peer CTA's request covers an access when an event of the peer
  request happens before it (`Tmem.Pair.PairAllocBefore`, `CoversPaired`; OBJ-TMEM-PUBLICATION,
  `Core/Tmem/TmemPairLifetime.lean`). Own coverage or coverage through the peer is
  `Tmem.Pair.CoversWithPeer`, and `TcMma.AllocatedWithPeer` is `Allocated` with it. It is used in
  two rules:
  - ERR-TMEM-ACCESS-LIFETIME: the one access rule is `Tmem.Pair.AccessSafe L X` /
    `AccessUnsafe L X`, used by `Unsafe`. Its allocated-before-access conjunct is
    `AllocatedWithPeer`, and its release conjunct ranges over the records that cover the access
    by `CoversWithPeer`, so a record covering an access only through its peer is still released
    after the access completes.
  - DEP-TC-LOAD-VALUE: the source's allocation in `TcMma.ReadSource` is `AllocatedWithPeer` (a
    load's source MMA may be the leader's MMA on the loading CTA's cells). The load's own
    allocation, the source-liveness check (`SourceLive`) and the fresh-lifetime check
    (`FreshAfter`) use `Covers`. `AReadSource` checks no allocation and is unchanged.
  Read monotonicity (`TcMma.ReadPreserved`) keeps `pairings`: a new record must be in no pairing,
  since a pairing of allocations is recorded while its lanes are pending returns, which no
  base-causality edge leaves (`PairingReady.quiet`), so it publishes nothing to old loads.
- Basis: §9.7.18.7.1 ("When .cta_group::2 is specified, one warp from each of the peer CTAs must
  collectively perform the allocation and de-allocation."; "The mandatory .sync qualifier
  indicates that the instruction causes the executing thread to wait until all threads in the
  warp execute the same instruction before resuming execution."). The text does not state that
  the peer CTA's half is complete when the instruction returns in a warp; the leader CTA's first
  QK MMAs write the odd CTA's cells, connected to the odd CTA's allocation only through the
  collective allocation (`Tmem.Pair.Precedes` and the `Witness` edge of the dependency order, not in
  base causality).
- Previously: FA4 selected its only `tcgen05.alloc` (`cta_group::2`, pc 543) with
  `pairAllocOrderAt`; with no site selected, coverage was `Covers` only, and the access rule
  `AccessUnsafeA` took the assumption list.
- The GEMM proofs (Fp16Gemm8192, TcGemm) now discharge the release check also for records that
  cover an access through the peer: such a record is of the cell's CTA (`covers_key`) and every
  release of a record of the pair comes after the access completes (`release_done`). Litmus in
  `Tests/Tmem/TmemPairAllocation.lean`: the peer CTA's cell is not covered by its own allocation event
  for the issuer's access, is covered through the pairing with no assumption (`CoversPaired`,
  `CoversWithPeer`, `AllocatedWithPeer`), and an event that no event of the peer request happens
  before is covered by neither route.
- Kind: trust (EXT-PAIR-ALLOC-ORDER, `Direction: trust`), applies to every kernel with a
  `tcgen05.alloc.cta_group::2`.

### ASM-A13 `uniPollPhase` hook and `pollPhaseAt` (ASM-POLL-PHASE): replaced by `pollAgreeAt`
- Replaced (2026-11-15, user decision): the hook `uniPollPhase`, the constructor `pollPhaseAt`
  (contract ASM-POLL-PHASE, reading EXT-UNI-POLL-PHASE) and FA4's assumption `storePollPhase`
  are removed, with Core's reading EXT-UNI-POLL (`PollAgree`, which exempted the polls of one
  mbarrier with one parity for every kernel). Both are covered by one per-kernel assumption,
  `pollAgreeAt` (ASM-A14).
- Previously: `storePollPhase` selected the store warp's poll branches 1164 and 1174; the proof
  used it in `Cross.PollRest_store`, which now refutes the premise of `PollRest` with
  `Assumptions.pollAgree` (`store_wait_pollAgree`).
- Kind: hardware-dependent.

### ASM-A14 `uniPoll` hook and `pollAgreeAt` (ASM-POLL-AGREE)
- Decided (2026-11-15, user decision): a new field `uniPoll : Nat → Bool` (default false),
  consulted in ERR-NONUNIFORM-GUARD: `WarpDivergent` has the conjunct
  `¬ PollAgreeExempt K A pc vg vh i j`, which holds when an assumption selects `pc`, the
  instruction there is a `bra.uni` guarded by the predicate of the `mbarrier.try_wait` at
  `pc - 1`, and both lanes' records right before are that poll's events on one mbarrier, with any
  parities. `pollAgreeAt name sites why` selects exactly `sites`. FA4: `pollAgree` at
  `pollAgreeSites`, all 37 poll branches of the kernel, pinned by `pollAgreeSites_ops`
  (`Audit/AssumptionSites.lean`: each a guarded `bra.uni` on the predicate of the unguarded
  `try_wait` before it; the list is exactly the kernel's poll branches, `Kernel.pollBranch`, and
  exactly its guarded `bra.uni` instructions). Every warp that polls runs its polls on all 32
  lanes, so two lanes polling one phase in one round are never ordered: every poll branch needs
  the assumption (EXT-UNI-POLL used to supply this for every kernel). The store warp's lanes in
  different rounds are not ordered either (no collective between its rounds; see ASM-A13). The
  proof uses it through `poll_selected` (`Proof/Safety/WarpGuards.lean`) in
  `PollSynced.of_rounds` (two lanes in one round poll one object) and in `Cross.PollRest_store`.
  Polls of different objects are still ordered: the MMA warp's KV polls compute their ring slot
  from the item and trip, and lanes in different rounds are ordered through the collectives
  (EXT-DEPENDENCY-ORDER, ASM-A11). Litmus `sharedPoll_flagged` / `sharedPoll_exempt`,
  `phasePoll_flagged` / `phasePoll_not_flagged`, `rounds_hook_flagged`,
  `warpgroupMaxReg_hook_flagged` (`Tests/Sync/WarpUniformLitmus.lean`); no-change theorems
  `not_pollAgreeExempt`, `warpDivergent_noPoll`.
- Basis: §9.7.14.3 ("bra.uni is guaranteed to be non-divergent, i.e. all active threads in a warp
  that are currently executing this instruction have identical values for the guard predicate
  and branch target"), §9.7.15.16.19 ("Suspended thread resumes execution when the specified phase
  completes OR before the phase completes following a system-dependent time limit"): a poll may
  fail before its phase completes, so lanes can hold different predicates at the same branch.
  CUTLASS- and CuTe-generated wait loops are `try_wait P; @P bra.uni`; they rely on lanes of a
  warp spinning on such a poll staying converged and getting the same poll result, which the
  text does not state.
- Alternative: branch on the poll with a plain `bra`, or vote the result across the warp before
  a `bra.uni` (an upstream change to the kernel).
- Kind: hardware-dependent (trust); Core interface change (`WarpDivergent` consults `uniPoll`).

### ASM-A7 `clusterScopeMbarAt`: the pair's `.cta`-scoped handoffs (ASM-MBAR-SCOPE)
- Decided: `clusterMbar` widens to cluster scope exactly the 11 remote
  `mbarrier.arrive.shared::cluster` sites, the 9 waits on the barriers they reach, the 17
  waits on barriers fed by the leader's multicast `tcgen05.commit`, and the 6 waits of the
  leader's MMA warp on the Q and KV full barriers (`fullWaits`: pcs 595, 601, 670, 751, 808,
  1003; PTX 784, 797, 886, 990, 1078, 1335), 43 sites in all (pinned by `remoteArrives_eq` and
  `waits_are_cta_waits`).
- Why the full-barrier waits: the odd CTA's `cta_group::2` tensor loads complete on the leader's
  full barrier, so the release that the MMA warp's wait must observe is a complete-tx issued by a
  thread of the peer CTA. §9.7.10.28.5.3 (`cp.async.bulk.tensor`) gives it cluster scope ("the
  complete-tx operation on the mbarrier has .release semantics at the .cluster scope"), but the wait
  has the default `.cta` scope (§9.7.15.16.19: "If the .scope qualifier is not specified then it
  defaults to .cta"), and §8.7 makes two operations of different threads morally strong only if
  "each operation is strong and specifies a scope that includes the thread executing the other
  operation". The wait's ordering clause for bulk copies also covers only "the participating threads
  of the CTA". Without the widening the MMA operand reads of the odd CTA's half of a slot are not
  ordered after its copies, and a copy's completion is not caused before the leader's exit
  (`Lifetime.notify_caused`). The leader CTA's own copies need no widening.
- Basis: §9.7.15.16.16 (a missing `.scope` defaults to `.cta`); the existing constructor's
  statement cites CuTeDSL's documented default.
- Alternative: no widening, which gives the peer CTA no synchronization and makes FA4
  unprovable; or widening every mbarrier site.
- Kind: hardware-dependent.

## Readings

## Changes to existing Core rules

- ASM-INTERFACE (`Core/Data/Types.lean`): `Assumption` gains `segmentRule`, `tcLdWait`, `dupStores`,
  `barSameSite`, `commitInOrder`, `regSameSite`, `uniRendezvous`, `pairAllocOrder`,
  `uniPollPhase`, all defaulting to off. `pairAllocOrder` is removed again (2026-11-15, ASM-A12);
  `uniRendezvous` and `uniPollPhase` are removed and `uniPoll` is added (2026-11-15, ASM-A11,
  ASM-A13, ASM-A14).
- ERR-NONUNIFORM-GUARD (`Core/Sync/WarpUniform.lean`), 2026-11-15: `VisitBefore` orders two records
  by the execution-dependency order `DepBefore` (new `DepStep`, `DepBefore`; MEM-BASE-CAUSALITY, program
  order and `Rendezvous`) in place of MEM-BASE-CAUSALITY (new reading EXT-DEPENDENCY-ORDER). Core's reading
  EXT-UNI-POLL and `PollAgree` are removed, with EXT-UNI-POLL-PHASE, EXT-WARP-RENDEZVOUS,
  `PollPhaseExempt`, `FullRendezvous`, `RendezvousBefore`, `RendezvousExempt` and their no-change
  theorems. `WarpDivergent` has one exemption, `¬ PollAgreeExempt` (hook `uniPoll`, ASM-A14);
  no-change theorems `not_pollAgreeExempt`, `warpDivergent_noPoll`.
- OBJ-TMEM-PUBLICATION (`Core/Tmem/TmemPairLifetime.lean`, new entry), 2026-11-15:
  `PairAllocBefore`, `CoversPaired`, `CoversWithPeer` (own coverage or coverage through the
  peer), for every pair in `Execution.tmemPairing`, with no site selection and no assumption list
  (EXT-PAIR-ALLOC-ORDER, ASM-A12).
- DEP-TC-COMPLETION (`Core/Tc/TcMmaLifetime.lean`), 2026-11-15: new
  `TcMma.AllocatedWithPeer` (`Allocated` with `CoversWithPeer`) and `Allocated.withPeer`.
- DEP-TC-LOAD-VALUE (`Core/Tc/TcMmaRead.lean`), 2026-11-15: `ReadSource`'s source allocation is
  `AllocatedWithPeer L X`; the load's own allocation stays `Allocated`.
- ERR-TMEM-ACCESS-LIFETIME (`Core/Tmem/TmemPairAccess.lean`), 2026-11-15: one rule, `AccessSafe` /
  `AccessUnsafe` (allocation `AllocatedWithPeer`, release check over `CoversWithPeer`), used by
  `Unsafe` as `AccessUnsafe L X`; it takes no assumption list.
- THREAD-LOCAL (`Core/Thread/Local.lean`): the old `execLocalA` body is renamed
  `execLocalRule`; `execLocalA` first consults `segmentRule`. No-change theorem
  `execLocalA_noSegment`.
- THREAD-RUN (`Core/Thread/Run.lean`): `eventTmpl`'s `tcgen05.ld` arm is `tcLdTmpl`
  (with `Tmpl.thenWaitLd`). No-change theorem `eventTmpl_tcLd_noWait`.
- ERR-DATA-RACE (`Core/Assembly/Safety.lean`), 2026-11-15: new `SameValueWrites`; `Race L X` gains
  the conjunct `¬ SameValueWrites X e f a b` (two writes of the same bytes with the same value are
  not a race). With the hook `dupStores` gone, `Race` takes no assumption list again (`DupStore`,
  `not_dupStore`, `race_noDup` are removed).
- ERR-BARRIER-MISMATCH (`Core/Assembly/Safety.lean`), 2026-11-15: new reading
  EXT-BAR-PARTICIPANTS; the cross-warp position clauses of `BarMismatch` and
  `BarArriveMismatch` are removed (the barrier resource compares name and count), and with the
  hook `barSameSite` gone both take no assumption list again (`BarMismatch L K X`).
- ERR-SETMAXNREG (`Core/Thread/SetMaxNReg.lean`), 2026-11-15: requests of different warps
  are compared by direction and count only (EXT-BAR-PARTICIPANTS); with the hook `regSameSite`
  gone `SetMaxNReg.Unsafe L X` takes no assumption list again.
- ERR-UNSAFE (`Core/Assembly/Execution.lean`): `Unsafe` passed `A` to `Race`, `BarMismatch`,
  `SetMaxNReg.Unsafe` and `Tmem.Pair.AccessUnsafeA`; none of them takes it now (ERR-DATA-RACE,
  ERR-BARRIER-MISMATCH, ERR-SETMAXNREG, ERR-TMEM-ACCESS-LIFETIME above).
- ERR-SHARED-LIFETIME (`Core/Assembly/SharedLifetime.lean`): new `CommitNext`, `LifetimeStep`;
  `LifetimeOrder` and `CompletedBefore` use `LifetimeStep` in place of
  `Enables ∨ ObjectOrder`. No-change theorems `not_commitNext`, `lifetimeStep_noCommitOrder`.
- ASM-IDEAL: `FloatForm.ofOp` maps a `setp` with an infinite constant to `.setpInf` (not
  `.setp`); `execIdealFloat` compares such operands in the extended reals.
- ASM-APPROX: `ApproxForm` gains `.ex2`, `.rcp`.
- OBJ-CTA-BARRIER-SYNC (`Core/Sync/CtaBarrierExecution.lean`, `CtaBarBlocking`), the
  `bar.arrive` recording rule (from commit 35c72b0a):
  - What changed: a `bar.arrive` that is followed by any later event of its thread must be
    recorded in its CTA's barrier history (`e.2 + 1 < (X.tr e.1).length → e ∈ refs
    (X.barriers (e.1 / L.block))`). Before, it had to be recorded only before a later recorded
    barrier operation of its thread, which let a thread pass an unrecorded `bar.arrive`, then
    signal another thread whose `bar.sync` of the same generation is recorded: the arrival can
    then never be appended (a cycle with causality, or a broken extension order), so a maximal
    execution stays incomplete and progress is unprovable. New Core lemma
    `Consistent.arriveRecorded` (in `Core/Assembly/Execution.lean`) states the rule for a
    possible execution.
  - Spec basis: §9.7.15.1 ("barrier{.cta} instruction causes executing thread to wait for all
    non-exited threads from its warp and marks warps’ arrival at barrier."; "barrier{.cta}.arrive
    does not cause executing thread to wait for threads of other participating warps."): the
    warp's arrival is marked when the instruction executes; the thread does not wait for
    completion. (The sentence "barrier{.cta}.arrive does not cause any waiting by the executing
    threads; it simply marks a thread's arrival at the barrier" does not occur in PTX ISA 9.5.)
  - Alternative: the old, lazier rule (record before the thread's next barrier operation).
  - Kind: equal to the text; stricter than before on executions (fewer consistent executions:
    those with a passed, unrecorded `bar.arrive` are gone). Existing kernels have no
    `bar.arrive`, so their semantics is unchanged.
  - Library consequence: the extension lemmas need the snoc'd thread's last `bar.arrive` (if
    any) to be recorded (`ArriveRecordedLast`, new field `Step.Released.arrive`); kernels without
    `bar.arrive` discharge it by `Consistent.noBarArrive`.

- CORRECT-FINAL (`Core/Assembly/Correctness.lean`, `IsFinal`), co-maximal writes that agree:
  - What changed: new `CoMaximal X co l w` (`w` writes `l` and no write of `l` follows it in
    `co`); `IsFinal` keeps the greatest-write and launch-content clauses and adds a third: if
    some write of `l` is co-maximal and all co-maximal writes of `l` write the same byte `b`,
    then `m l = some b`. `final_exists` is reproved (the value the co-maximal writes agree on is
    unique, and a greatest write is the only co-maximal one). New library lemma
    `IsFinal.of_agree` (`Lemmas/Kernel/Memory.lean`: finitely many writers that all write `v`
    leave `v`); litmus `Tests/Memory/IdenticalWritesFinal.lean` (two unordered identical writes fix the
    byte; two unordered differing writes leave every value possible).
  - Spec basis: §8.9.6 ("Two overlapping writes are unrelated in coherence order if they are in a
    data-race , which gives rise to the partial nature of coherence order ."; footnote: "It may
    be observed indirectly by its use in constraining the set of candidate writes that a read
    operation may read from."), §8.10.6 ("If a write W precedes an overlapping read R in
    causality order , then for any byte accessed by both R and W, R cannot read from any write
    W’ that precedes W in coherence order ."): every write precedes a read after the kernel, so
    that read reads a co-maximal write, and when all of them agree it reads their value.
  - Alternative: leave `IsFinal` as it was; the bytes of FA4's identical epilogue stores are then
    unconstrained and FA4's result is unprovable.
  - Kind: closer to the text (the old rule was stricter than the text: it constrained a byte only
    when one write was greatest in `co`). Where one write is greatest, the new clause gives the
    same byte, so existing kernels' results are unchanged; their proofs use the first two clauses.

- THREAD-TC (`Core/Tc/TcThread.lean`, `tcTmpl`), the source values of `tcgen05.st`:
  - What changed: `tcgen05.st` reads each source register with `readValue` (the register's value
    unchanged, a literal as its 32-bit pattern) instead of `readBits … 32`, requires each value
    to be 4 bytes wide (else a `typeMismatch` fault), and records those values in its event. Before,
    it recorded `.bits 32` of each register's bit pattern. Library lemmas `fires_tcSt`
    (`Lemmas/Flow/EventCont.lean`) and `fires_tcSt_len` (`Lemmas/Flow/ElemAccess.lean`) keep their
    statements; their proofs follow the new template.
  - Spec basis: §9.7.18.8 ("The threads of the CTA can perform the loads and stores to the Tensor
    Memory of the CTA and move data between registers and Tensor Memory."), §9.7.18.8.4
    ("Instruction tcgen05.st asynchronously stores data from the source register r into the
    Tensor Memory"). `tcgen05.st` is data movement, and the model's rule for data movement is
    THREAD-LOCAL `readValue` ("Value read for data movement: registers unchanged; literals,
    including `0f` constants, are their `w`-bit patterns."), which `st.shared` already uses
    (`storeTmpl`: `readValue`, then the width check). With bits, a float payload became its
    encoding on the way into Tensor Memory: under the ideal-arithmetic assumption the PV MMA
    would read `round_f16(p)` from P and an accumulating MMA `round_f32(o · α)` from O, unlike the
    same values stored to shared memory.
  - Alternative: keep the bits and either add an FA4 assumption that `tcgen05.st` stores payloads
    unchanged, or state `Post` with rounded P and rescaled O. Both treat one data-movement
    instruction differently from the others.
  - Kind: equal to the text in what is stored (a register's 32 bits); the change is in the
    representation, which now matches `st.shared`. Two edge cases change as for `st.shared`: a
    64-bit source value is now a fault (before, its low 32 bits were stored), and a 32-bit shared
    or parameter pointer is now stored as that pointer (before, it had no rule). Only FA4 issues `tcgen05.st` (the GEMM kernels have none), so no
    other kernel's meaning changes. Downstream, a word stored as `.pair (.float .f16 x)
    (.float .f16 y)` gives the MMA A operand the bytes of `x` and `y` (`AReadOk`, `byteAt`), and a
    word stored as `.float .f32 y` is returned whole by `tcgen05.ld` (`WordContains`) and read
    as `y` by an accumulating MMA (`Result.accumulateStored`).

- Decoding representation changes (meanings unchanged): `shr` gains `signed`, `mulWide` gains
  `width` (DEC-INT-FORMS); `tcMma`/`tcMmaTs` take `enableD : Opnd` and a shared
  `cachePolicyRead` serves tensor loads, stores and prefetches (DEC-MMA-FORMS,
  DEC-TENSOR-CACHE-HINT); the GEMM decoder cache was reprinted, nothing else changed.
- EXT-TCFIG's text now covers `kind::f16` `cta_group::2` with A in Tensor Memory, and the new
  rule THREAD-TC gives `[a-tmem + imm]` (DEC-MMA-FORMS).
- The barrier event gains a form (`BarMode`), EXT-BAR-PARTICIPANTS now compares participants of
  the same form, and ERR-BARRIER-MISMATCH gains `BarArriveMismatch` (DEC-BAR-ARRIVE).

## Spec: why `Pre` and `Post` are written this way

`Spec.lean` states the theorems' premise `Pre` and conclusion `Post`; `Data/TensorMaps.lean`
gives the four tensor maps as functions of the shape. Fields not listed here mirror the
production GEMM's `Pre` (map and tensor alignment, ranges and disjointness, input bytes,
allocated output and shared memory).

### D-SPEC-SHAPE: `sq`, `sk` with separate divisibility and positivity fields
- Decided: `Params` holds `b`, `h`, `sq`, `sk`; `Pre` has `sqPos`, `sqDiv512`, `skPos`,
  `skDiv128`, and every count is written with ceilings (`Params.blocks = (sq + 511) / 512`).
  `bPos`, `hPos` are also required.
- Basis: D-SCOPE-SHAPE. `s_k = 0` makes the loader load KV block `-1` and the PTX selects this
  kernel only for `s_q > 256`; `b`, `h` and both lengths are tensor-map extents, which must be
  positive (`cuTensorMapEncodeTiled`, `TensorDescriptor.Valid`).
- Alternative: parametrize by block counts (`sq = 512 nq`), which would have to be undone to
  admit arbitrary lengths.
- Kind: scope.

### D-SPEC-RANGES: 31-bit lengths and schedule, 40-bit strides
- Decided: `sq < 2^31`, `sk < 2^31`, `b ≤ 2^32`, `256·h·sq < 2^40`, `256·h·sk < 2^40`, and
  `items + clusters ≤ 2^31` (`scheduleRange`).
- Basis: the kernel computes `ceil(s_k / 128)` with signed shifts of `s_k` (`shr.s32`,
  PTX 268-278), compares the work index with `param_13` signed (`setp.ge.s32`, 284) and
  advances it by `%nclusterid.x`, and passes row coordinates as `.s32` TMA coordinates; the
  driver limits extents to `2^32` and strides to `2^40` (EXT-TMA-GEOMETRY), which
  `encodeTiled_valid` turns into `TensorDescriptor.Valid`.
- Alternative: derive the bounds from a launch the driver accepts (no such Core notion).
- Kind: launch obligation.

### D-SPEC-PARAM-BYTES: parameter objects described only by the bytes the kernel reads
- Decided: `param_1` (the K tensor struct): bytes 0..3 are `sk` (little-endian), the only
  bytes read (PTX 41). `param_11`, `param_12`: bytes 0..9 are a `Divmod` (divisor, multiplier
  u32, two shift bytes; PTX 46-51). `param_13` (scalar) is `items = ceil(sq/512)·h·b`;
  `param_8` (scalar `.f32`) is a finite f32 pattern whose value is `scale`. Params 0, 2, 3, 9,
  10, 14 and the unread bytes are unconstrained.
- Basis: `Launch.paramBytes` (DEC-PARAM-OBJECT) and `Launch.params`; the field assignment
  follows `StaticPersistentTileScheduler.Params` (README "Why one PTX covers the scope"), whose
  order was not checked against the launch ABI.
- Alternative: describe the full CuTe tensor structs (their layout is CuTeDSL-internal).
- Kind: launch obligation.

### D-SPEC-FASTDIVMOD: the divmod objects as a property, not a formula
- Decided: `Divmod.Exact p d`: `p` stores divisor `d`, its fields fit their bytes, and
  `∀ n < 2^32, FastDivmod.quot p.mul p.shift1 p.shift2 n = n / d`, where `FastDivmod.quot` is
  the device instruction sequence (`mul.hi.u32`, `sub.s32`, `shr.u32`, `add.s32`, `shr.u32`).
  `param_11` divides by `ceil(sq/512)` (`num_block_cluster`), `param_12` by `h`. The bytes are not
  fixed to `FastDivmod.params d`.
- Basis: CuTeDSL's `FastDivmodDivisor` is compiled and its host formula cannot be read; the
  kernel needs only exact quotients. `Lemmas/Arith/FastDivmod.lean` proves `quot_params`: the
  premise is satisfiable for `1 ≤ d < 2^31` with the round-up magic numbers. `Tests/Kernel/Statements`
  admits `Lemmas.Arith.FastDivmod` (arithmetic definitions only) among the reviewed modules.
- Alternative: `bytes = FastDivmod.params d` — a guess at the host code, false if CuTeDSL uses
  another valid triple.
- Kind: launch obligation.

### D-SPEC-GRID: grid `2·clusters`, `clusters ≥ 1`
- Decided: `L.grid = 2 * P.clusters` with `0 < P.clusters`; `block = 512`, cluster 2. The
  host's grid (`min(SMs/2·2, 2·items)`) is not fixed: any number of clusters is in scope.
- Basis: README scope ("grid: any even number of CTAs"); `.reqntid 512, 1, 1`.
- Kind: scope.

### D-SPEC-LAYOUT: contiguous `(batch, seqlen, heads, 128)` tensors
- Decided: Q, K, V, O are contiguous in the order `(batch, row, head, d)`; `elementLoc` and
  the map strides (`256·h`, `256`, `256·h·rows` bytes) follow it. Functions `q k v` take
  `(batch, head, row, d)`.
- Basis: `gen_ptx.py` passes `torch.randn((b, s, h, d))`; `flash_attn_func` makes inputs with
  unit last stride and allocates `out` with `torch.empty((b, s_q, h, 128))`.
- Alternative: arbitrary input strides (`mark_layout_dynamic` admits them): strides as
  `Params` fields. Not taken: the strides only enter through the maps, and general strides add
  fields without changing the proof.
- Kind: scope.

### D-SPEC-SHARED: dynamic shared base aligned to 1024, below `2^18 - 232448`
- Decided: `L.sharedBase % 1024 = 0`, `L.sharedBase + 232448 ≤ 2^18`, all 232448 bytes
  allocated in every CTA.
- Basis: `__dynamic_shmem__0` is declared `.align 1024` and the O staging swizzle and the
  128-byte TMA swizzle agree only on 1024-aligned rows (fa4-structure §2); the MMA descriptors
  keep the start address in a 14-bit field of `addr >> 4` (PTX 717-720 and others), so every
  operand address must be below `2^18`.
- Kind: launch obligation.

### D-SPEC-POST: base-2 softmax, max-free
- Decided: for every `batch < b`, `head < h`, `row < sq`, `d < 128`, the f16 output is
  `attn = Σ_{j<sk} w_j V[j][d] / Σ_{j<sk} w_j` with `w_j = 2 ^ (scale · S_j)` (`Real.rpow`) and
  `S_j = Σ_{t<128} Q[row][t] K[j][t]`; every global byte outside O is unchanged.
- Basis: the kernel's scale parameter is `softmax_scale · log₂ e` and it exponentiates with
  `ex2`, so `Post` states what is computed and makes no claim about `e`. The running maximum and
  the lazy rescale are proof details: the result is independent of the reference maximum.
- Exactness rests on `idealArith` and on the approximation assumptions `approx` (`ex2.approx`,
  `rcp.approx` as exact) and `swExp2` (the software `exp2` as exact; OPEN-NUM). The software
  `exp2` clamps its argument at `-127`; read with the clamp it computes `2 ^ max(x, -127)`, which
  would make this `Post` false for very negative scaled logits. `cuteExp2` reads the clamp away:
  its function is `2 ^ x` (ASM-A3).
- Kind: scope.

### D-TMAP-BOX: boxes and swizzle from the PTX
- Decided: rank 4, dimensions (head dim, row, head, batch); boxes `64 x 128 x 1 x 1` for Q, V,
  O and `64 x 64 x 1 x 1` for K; 128-byte swizzle; f16; unit traversal.
- Basis (PTX): coordinates `{0|64, row, head, batch}` of all `cp.async.bulk.tensor.4d`; shared
  destinations 16384 bytes apart (Q 68608/84992, O staging, V one box per slot) and 8192 for K
  (`+134144`, `+142336`; row coordinate `128·blk + 64·rank`); `expect_tx` 65536 per Q stage
  (2 CTAs x 2 x 16384) and 32768 per K or V slot; the O staging written with the 128-byte XOR
  swizzle. Source: `flash_fwd_sm100.py` view transposes (`[1, 3, 2, 0]`, V `[1, 0, 2, 3]`) and
  `epi_tile = (128, 128)`.
- Kind: launch obligation.

### D-TMAP-UNKNOWN: OOB fill, L2 promotion, allocation class
- Decided: the fill mode and the allocation class of each map are `Params` fields,
  unconstrained; L2 promotion is not represented.
- Basis: `make_tiled_tma_atom` encodes the maps in compiled MLIR lowering
  (`atom_make_non_exec_tiled_tma_load`), so these arguments cannot be read. In scope every
  coordinate is in bounds, so the fill mode is never observed; the allocation class is a
  device attribute (as in GEMM); L2 promotion is a cache hint without memory-model effect.
  A run-time capture of the 128-byte maps (as GEMM's `gen_ptx.py --tensor-maps`) would
  replace the unconstrained fields by recorded values.
- Alternative: assume CUTLASS's C++ defaults (zero fill, 128B promotion).
- Kind: launch obligation.

## Proof method

### D-PROOF-NONFINITE: the role machines follow non-finite floating words
- Decided: the softmax and correction machines follow every word they load (`tcgen05.ld` of
  the scores and the output accumulator, `ld.shared` of the statistics words), finite or not.
  Their states hold the values the evaluator computes from those words: the ideal result under
  `idealArith` and `approx` where the operands are finite, and the Core rule's result where the
  assumption declines (a NaN operand, `∞ - ∞`, `0 · ∞`, an infinite operand of an
  approximation), using the generic outcome functions of `Lemmas/Flow/FloatOutcome.lean` and
  `Lemmas/Flow/Cvt.lean`. A word on which even the Core rule faults ends the thread, as before.
  The real-number readings of the machines' values are lemmas under the hypothesis that the
  loaded words are finite.
- Basis: the ideal assumption's text ("an infinite operand is read as that infinity, and an
  operation with a NaN operand, ∞ − ∞ or 0 × ∞ takes the Core rule"), so a non-finite word does
  not fault and the thread continues. A machine that stopped at such a word would need, inside
  the thread layer, the fact that the word is finite, which only the whole-execution value
  protocols give; following the word keeps the thread layer independent of them.
- Why it does not occur: every `tcgen05.ld` reads an MMA result, a real number under
  `idealArith` from the finite `f16` inputs of `Pre` and the finite `P` values
  (`Safety.LoadFloats`), and every statistics word is the last softmax store of a finite word
  (`Safety.StatsFloats`). These discharge the finiteness hypotheses at the end; they are proved
  facts, not premises.
- Alternative: stop the machine at a non-finite word and track the threads role by role (the
  MMA warp first, then softmax, then correction) so that the value protocols can be used inside
  the thread layer.
- Kind: scope (proof method; no change to `Pre`, `Post` or the assumptions).

### D-PROOF-SHAPE-STORE: the store warp's events from its shape table
- Decided: the store warp has an event-shape table over every firing (`Store.Ev`, proved by one
  `site_shape` call with the TMA sites by `Store.tma_event`), and its thread facts read the table
  (`Facts.store_ev`) instead of inverting the instruction at each site. The TMA site's shape is
  the store of its half of its stage of its item, so no shape is undefined behaviour and
  `Cross.SitesTmplOk_store` is `Code.Shape.not_ub`. `Store.code`'s invariant is the thread
  machine's (`setmaxnreg` or `Store.Inv`), as on `b1-fa4-site-cases`, so the shape lemma applies
  to the thread's states unchanged.
- Basis: machine plan task A1 (§5.4). The loader, MMA, softmax and correction roles already had
  shape tables over their continuing events (`site_event`); the store warp was the one role whose
  facts inverted the instruction by hand.
- Kind: proof method.

### D-PROOF-LOADER-STEPS: the loader's steps stay hand-written (pilot S-P)
- Decided: the loader's step obligations stay proved by the hand-written segment files
  (`LoaderStart`, `LoaderQ0` … `LoaderDrain`, `LoaderSound`).
- Basis: machine plan pilot S-P, criterion "no failure and CPU time ≤ 1.25 × 136 s". Measured on
  this branch: the hand-written files take 148 s CPU (user + sys, eleven files). The `site_cases`
  version of `b1-loader-wip` (`LoaderSound` with the rules `snext_w`, `pnext_w` for the ring's
  `selp`/`xor`, segments cut at the peer-bit masks and pointer additions; seven sites by hand),
  ported with the library pieces it needs (`Proof/Lib/Step{Kind,Cut,Guard}.lean`, kept on the local
  branch `fa4-a1-sp`, not merged), fails with 54 errors (`sym_close: the values differ` between the
  table's closed forms and the code's terms, `seg_sym: the local step at 366/398/437 does not
  evaluate`, `ld_close: no segment` at the wait sites, `site_kind` at the leader election) and
  takes 454 s CPU (404 s of it tactic execution), above the 170 s bound before the failures are
  fixed. A table that mirrors the code's `selp`/`xor` terms removes the value mismatches but not
  the evaluation time, and it changes the table every loader event and count file reads.
- Alternative: finish the `site_cases` version with the code's terms in the table; reopen when
  `seg_sym` evaluates a loader segment in a time comparable to the hand-written walk.
- Kind: proof method.
