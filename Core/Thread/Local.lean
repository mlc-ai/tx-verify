-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.Cluster
public import Core.Data.Types
public import Core.Data.Events
public import Core.Thread.Float
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# Thread semantics: local instructions

Instructions that read and write only this thread's registers and source position. Nothing here
mentions memory, other threads, or time.
-/

namespace PTX

noncomputable section

/-! ## THREAD-BITS — bit patterns
Statement: Every data value has a bit pattern: an integer's bits, a floating payload's encoding in
  its format, the halves of a packed pair concatenated with the low half first, or the bytes of a
  slice. Pointers, predicates and cancellation responses have none. A floating payload is kept as
  the number it denotes, and each finite pattern of a floating format decodes to an exact value,
  while NaN and infinities have none.

Defs: truncBits, toSigned, Value.bitPattern

Source:
- §5.2.1: "The bit-size type is compatible with any fundamental type having the same size. In
    principle, all variables (aside from predicates) could be declared using only bit-size types"
- §5.2.3: "the .f16 type indicates 5 bits reserved for exponent and 10 bits reserved for mantissa"
- §5.2.3: "bf16 data format: This data format is a 16-bit floating point format with 8 bits for
    exponent and 7 bits for mantissa. A register variable containing bf16 data must be declared with
    .b16 type."
- §5.2.3: "The e4m3 encoding does not support infinity and NaN values are limited to 0x7f and 0xff"
- §5.2.3: "e5m2 data format: This data format is an 8-bit floating point format with 5 bits for
    exponent and 2 bits for mantissa"
- §4.5.2: "To specify IEEE 754 double-precision floating point values, the constant begins with 0d
    or 0D followed by 16 hex digits."
- §9.7.10.4: "pack two 16-bit elements into .b32 d = a.x | (a.y << 16)"
- §9.7.3: "Instructions that support rounding modifiers are IEEE-754 compliant."
- EXT-FLOAT-BITS

Direction: reading

Applies: The bits of every data value: integer patterns, floating payloads, packed pairs and byte
  slices

Premises: A width and bit pattern, a format and bit pattern, or a value, as specified by the helper.

Effect: Local evaluation. The entry also defines truncation to a width and the signed interpretation
  of a bit pattern.
  A register holds a bit pattern; a floating payload is kept as the number it denotes so that
  arithmetic profiles can compute with it, and `Value.bitPattern` gives its bits. For a number
  representable in its format this is its IEEE encoding, exactly as PTX stores it (zero is `+0`).
  `0f` constants are kept as their 32-bit pattern (THREAD-REG), so `-0`, NaN and infinity encodings
  are never lost. The format layouts and their decoders are THREAD-FLOAT-FORMAT, and the bits of a
  payload, `FloatFmt.encode`, are the rounding of THREAD-FLOAT-ROUND.

### EXT-FLOAT-BITS — bits of an unrepresentable payload

Statement: A floating payload whose number is not representable in its format is read as bits by
  rounding the number to nearest, ties to even, as `cvt.rn` to that format would. The formats `f64`,
  `f32`, `f16` and `bf16` overflow to infinity, `e4m3` and `e5m2` saturate to the largest finite
  value, and zero is `+0`. `FloatFmt.encode` is this rounding: `Layout.round` of THREAD-FLOAT-ROUND
  with `.rn`, the overflow policy `FloatFmt.overflow` and a positive zero.

Review: A payload `.float fmt x` whose number `x` is not representable in `fmt` (only an ideal
  profile or an ideal input precondition produces one) has no PTX bit pattern. Its bits are read as
  `x` rounded to nearest, ties to even, as `cvt.rn` to `fmt` would: `.f64`, `.f32`, `.f16` and
  `.bf16` overflow to infinity (IEEE 754), `.e4m3` and `.e5m2` saturate to the largest finite value,
  as `cvt.rn.satfinite` does (§9.7.10.24: ".satfinite modifier is mandatory for such conversions";
  "If the absolute value of input (ignoring sign) is greater than MAX_NORM of the specified
  destination format, then the result is sign-preserved MAX_NORM of the destination format"). Zero
  is `+0`.

Evidence: PTX ISA §9.7.10.24 (cvt: ".rn rounding to nearest, with ties to even").

Direction: reading

Effect: The bits stored for such a payload are fixed by this rounding; if the program's code rounds
  differently, the stored bits differ from the ones proven. Disclosed by every kernel whose
  statement names `Assumption.idealReal` or `Value.float`: BlockSum, FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum.
-/

def truncBits (w : Nat) (x : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (x.toNat % 2 ^ w)

/-- Two's complement value of the low `w` bits. -/
def toSigned (w : Nat) (x : BitVec 64) : Int :=
  let n := x.toNat % 2 ^ w
  if n < 2 ^ (w - 1) then n else (n : Int) - 2 ^ w

/-- The bits of a data value, `8 * v.bytes` wide: an integer's bits, a payload's encoding,
a pair's halves (low half first), a slice's bytes. Opaque values and predicates have none. -/
def Value.bitPattern : Value → Option Nat
  | .bits _ x => some x.toNat
  | .float fmt x => some (fmt.encode x)
  | .pair lo hi => do
    let a ← lo.bitPattern
    let b ← hi.bitPattern
    pure (a % 2 ^ (8 * lo.bytes) + 2 ^ (8 * lo.bytes) * b)
  | .slice whole offset size => do
    let a ← whole.bitPattern
    pure (a / 2 ^ (8 * offset) % 2 ^ (8 * size))
  | .pred _ | .ptr .. | .clc _ | .policy | .nan _ => none

/-! ## THREAD-REG — registers and operands
Statement: Registers are private to a thread, and an instruction that completes advances the source
  position by one. Reading a register that was never written is undefined, where PTX gives an
  unspecified value. An integer operand is the low bits of a register's bit pattern, an immediate, a
  special register (THREAD-SREG), the address of a shared symbol or a `0f` constant read as its
  32-bit pattern. A write changes only the selected register of the thread.

Defs: readReg, setReg, next, readBits, readValue, readValue_sreg

Source:
- §5.1.1 (register state space)
- §5.1.2 (special registers)
- §4.5.2: "To specify IEEE 754 single-precision floating point values, the constant begins with 0f
    or 0F followed by 8 hex digits."
- §9.7.9.1: "Compute the bit-wise and operation for the bits in a and b"
- §9.7.9.1: "The size of the operands must match, but not necessarily the type"
- §9.7.9.1, example: "and.b32 sign,fpvalue,0x80000000;"

Direction: stricter

Applies: Thread-local operands and registers

Premises: The requested register exists and its value has a bit pattern.

Effect: Local evaluation and fault production. An invalid register operand is a fault.
  Registers are thread private. Reading a register that was never written is undefined
  (`uninitialized`), where PTX would give an unspecified value (Direction: stricter). An integer
  operand is the low `w` bits of a register's bit pattern (THREAD-BITS), whatever the value's type:
  an integer, a floating payload or a packed pair. It can also be an immediate, a special register,
  a shared symbol address (THREAD-ADDR) or a `0f` constant, read as its exact 32-bit pattern. Data
  movement reads a `0f` constant as that pattern (`.bits 32`); floating instructions decode it
  (THREAD-NUM). Symbolic pointers have no integer reading (THREAD-SHARED-POINTER). An instruction
  that completes advances `pc` by one (`next`).
-/

/-- The value of register `r`, or the `uninitialized` fault when it was never written. -/
def readReg (t : TState) (r : Nat) : Exec Value :=
  match t.regs r with
  | some v => pure v
  | none => throw .uninitialized

/-- Write `v` to register `r`. -/
def setReg (t : TState) (r : Nat) (v : Value) : TState :=
  { t with regs := Function.update t.regs r (some v) }

/-- Advance the source position by one. -/
def next (t : TState) : TState := { t with pc := t.pc + 1 }

/-! ## THREAD-SREG — special register values
Statement: `%tid`, `%ntid`, `%ctaid`, `%nctaid`, the cluster registers and `%is_explicit_cluster`
  have the values of the thread's position in the launch and of the launch's shape. `%laneid` and
  the lane masks follow from the thread's lane (EXT-WARP). A register that the driver or the
  machine fixes before launch has an unconstrained value that stays the same for the thread. A
  read of a register whose value changes while the thread runs is an event whose value stays open,
  within the register's width and the range the manual states. The performance counters have no
  rule.

Defs: sregValue, sregValue_isSome, sregValue_initial, sregValue_oneDim, SReg.readBound,
  substVarying, Op.withSregValues, sregTmpl

Source:
- §10.1: "%tid component values range from 0 through %ntid-1 in each CTA dimension."
- §10.1: "%tid.y == %tid.z == 0 in 1D CTAs."
- §10.2: "%ntid.y == %ntid.z == 1 in 1D CTAs."
- §10.3: "A predefined, read-only special register that returns the thread’s lane within the warp."
- §10.4: "Note that %warpid returns the location of a thread at the moment when read, but its value
    may change during execution"
- §10.5: "returns the maximum number of warp identifiers"
- §10.6
- §10.7
- §10.8: "%smid returns the location of a thread at the moment when read, but its value may change
    during execution"
- §10.8: "The SM identifier ranges from 0 to %nsmid-1 ."
- §10.9: "returns the maximum number of SM identifiers"
- §10.10: "initialized with the per-grid temporal grid identifier"
- §10.11: "initialized with the predicate value of whether the cluster launch is explicitly
    specified by user"
- §10.12–§10.17: "It is guaranteed that: 0 <= %cluster_ctarank < %cluster_nctarank"
- §10.18: "initialized with a 32-bit mask with a bit set in the position equal to the thread’s lane
    number in the warp"
- §10.19–§10.22
- §10.23: "Special register %clock and %clock_hi are unsigned 32-bit read-only cycle counters that
    wrap silently."
- §10.24: "Special register %clock64 is an unsigned 64-bit read-only cycle counter that wraps
    silently."
- §10.25: "Their behavior is currently undefined."
- §10.26
- §10.27: "These registers are initialized by the driver prior to kernel launch and can contain
    cta-wide or grid-wide values."
- §10.28: "When JIT-compiled to other targets, the value of these registers is unspecified."
- §10.29–§10.33
- §10.34 and §10.35: "Usage of this special register is valid only inside entry functions that also
    specify directive .minperctamemory ."
- §10.36: "For the lifetime of a cluster, all threads within that cluster always read the same
    value."
- §10.37
- EXT-WARP
- EXT-CLUSTER-RANK
- EXT-PREFERRED-CLUSTER

Direction: stricter

Applies: Every special register operand that the decoder accepts (PROG-ISA-SREG)

Premises: The register has a kind (`SReg.kind`). A register that changes while the thread runs is
  a source of an integer, move or conversion instruction.

Effect: Local evaluation for the fixed registers; an event with an open value for the registers that
  change; `noRule` for the others.
  `SReg.kind` (PROG-ISA-SREG) names how each register gets its value. `sregValue` gives the value
  of every register whose kind is not `varying` (`sregValue_isSome`).
  - Launch registers. Thread `g` is thread `g % block` of CTA `g / block` (PROG-LAUNCH). `%tid` is
    `Launch.tidOf`, the coordinates of the linear thread index in the CTA shape; `%ntid` and
    `%nctaid` are the launch's shapes; `%ctaid`, `%clusterid`, `%nclusterid`, `%cluster_nctaid` and
    `%cluster_ctaid` are those of the CTA's own cluster (PROG-CLUSTER, EXT-CLUSTER-RANK), which has
    the regular or the preferred shape (EXT-PREFERRED-CLUSTER); `%cluster_ctarank` is the CTA's rank
    and `%cluster_nctarank` the size of its cluster. `%is_explicit_cluster` is
    `Launch.explicitCluster`, and it is read as a `.pred` source (PROG-OPERAND). In a
    one-dimensional launch (`Launch.OneDim`) every launch register has the value of the
    one-dimensional model (`sregValue_oneDim`): the `.x` components and the ranks of
    EXT-CLUSTER-RANK, `.y` and `.z` components 0 and extents 1.
  - Lane registers. `%laneid` is the lane `laneOf` of the thread in its warp (EXT-WARP), and
    `%lanemask_eq`, `%lanemask_le`, `%lanemask_lt`, `%lanemask_ge` and `%lanemask_gt` are the 32-bit
    masks of the lane positions equal to, at most, below, at least and above it.
  - Initial registers. `%nwarpid`, `%nsmid`, `%gridid`, `%envreg<32>`, the reserved shared memory
    registers, `%total_smem_size`, `%aggr_smem_size`, `%dynamic_smem_size`, `%current_graph_exec`,
    `%locality_domain_id`, `%locality_domain_supplemental_sm`, `%perctamemoryoffset` and
    `%perctamemorysize` are set before the thread starts and do not change. Their value is
    `Launch.sregInit` of the thread and the register (`sregValue_initial`), which no premise of the
    model constrains, so a proof that quantifies over the launch holds for every value the machine
    may give. The two `%perctamemory` registers decode only in a kernel with a `.minperctamemory`
    directive (PROG-DECODE); the bounds §10.35 gives for `%perctamemorysize` are not used.
  - Registers that change. `%warpid`, `%smid`, `%clock`, `%clock_hi`, `%clock64` and the
    `%globaltimer` registers change while the thread runs, so two reads may differ. An integer, move
    or conversion instruction that reads one of them performs one event (`Tmpl.sreg`, `sregTmpl`)
    that records every such register it reads and a value for each. The value is any number below
    `SReg.readBound`: `2 ^ width`, and for `%smid` also the thread's `%nsmid`, since "The SM
    identifier ranges from 0 to %nsmid-1". A launch whose `%nsmid` is 0, which no hardware launch
    has, bounds a `%smid` read by its width only, so the read always has a value. The manual states
    no other relation: the sentence that `%clock64` is identical to `%clock` and `%clock_hi` in its
    halves relates registers at one moment, and two reads are two moments, so it constrains no pair
    of reads; a cycle counter wraps, so no order between two reads is stated. The instruction then
    executes with each such operand replaced by the value read (`Op.withSregValues`), and a fault of
    that execution is a pending fault of the thread. No proof can depend on a value read, because
    every value is possible. A changing register read by an instruction of another family has no
    rule.
  - Registers without a rule. The performance counters `%pm0`–`%pm7` and `%pm0_64`–`%pm7_64` have
    undefined behaviour. Reading one is `noRule`, which a kernel assumption may replace with a rule
    of its own (THREAD-LOCAL).
-/

/-- The value of a special register for thread `g` of the launch (THREAD-SREG), or `none` for a
register that changes while the thread runs or has no rule. -/
def sregValue (L : Launch) (g : Nat) : SReg → Option Nat
  | ⟨.tid, some d⟩ => some ((L.tidOf g).get d)
  | ⟨.ntid, some d⟩ => some (L.ntid.get d)
  | ⟨.ctaid, some d⟩ => some ((L.ctaidOf (g / L.block)).get d)
  | ⟨.nctaid, some d⟩ => some (L.nctaid.get d)
  | ⟨.clusterid, some d⟩ => some ((L.clusteridOf (g / L.block)).get d)
  | ⟨.nclusterid, some d⟩ => some ((L.nclusteridOf (g / L.block)).get d)
  | ⟨.clusterCtaid, some d⟩ => some ((L.clusterCtaidOf (g / L.block)).get d)
  | ⟨.clusterNctaid, some d⟩ => some ((L.clusterNctaidOf (g / L.block)).get d)
  | ⟨.clusterCtarank, none⟩ => some (L.rankOfCta (g / L.block))
  | ⟨.clusterNctarank, none⟩ => some (L.clusterSizeOf (g / L.block))
  | ⟨.isExplicitCluster, none⟩ => some (if L.explicitCluster then 1 else 0)
  | ⟨.laneid, none⟩ => some (laneOf L g)
  | ⟨.lanemaskEq, none⟩ => some (2 ^ laneOf L g)
  | ⟨.lanemaskLe, none⟩ => some (2 ^ (laneOf L g + 1) - 1)
  | ⟨.lanemaskLt, none⟩ => some (2 ^ laneOf L g - 1)
  | ⟨.lanemaskGe, none⟩ => some (2 ^ 32 - 2 ^ laneOf L g)
  | ⟨.lanemaskGt, none⟩ => some (2 ^ 32 - 2 ^ (laneOf L g + 1))
  | ⟨n, d⟩ => match SReg.kind ⟨n, d⟩ with
    | some .initial => some (L.sregInit g ⟨n, d⟩)
    | _ => none

/-- A special register has a value exactly when it has a rule (`SReg.rule`) and does not change
while the thread runs. -/
theorem sregValue_isSome (L : Launch) (g : Nat) (s : SReg) :
    (sregValue L g s).isSome = (s.rule.isSome && !s.varying) := by
  rcases s with ⟨n, d⟩
  cases n <;> rcases d with _ | ⟨_ | _ | _⟩ <;> rfl

/-- A register that the machine fixes before launch has the launch's unconstrained value. -/
theorem sregValue_initial {L : Launch} {g : Nat} {s : SReg} (h : s.kind = some .initial) :
    sregValue L g s = some (L.sregInit g s) := by
  rcases s with ⟨n, d⟩
  cases n <;> rcases d with _ | ⟨_ | _ | _⟩ <;> first | rfl | cases h

/-- In a one-dimensional launch (`Launch.OneDim`) the launch registers have the values of the
one-dimensional model: the `.x` components from the linear thread and CTA numbers and the cluster
of EXT-CLUSTER-RANK, `.y` and `.z` components 0 and extents 1. -/
theorem sregValue_oneDim {L : Launch} (h : L.OneDim) (g : Nat) :
    sregValue L g ⟨.tid, some .x⟩ = some (g % L.block) ∧
    sregValue L g ⟨.ntid, some .x⟩ = some L.block ∧
    sregValue L g ⟨.ctaid, some .x⟩ = some (g / L.block) ∧
    sregValue L g ⟨.nctaid, some .x⟩ = some L.grid ∧
    sregValue L g ⟨.clusterid, some .x⟩ = some (g / L.block / L.clusterSize.val) ∧
    sregValue L g ⟨.nclusterid, some .x⟩ = some (L.grid / L.clusterSize.val) ∧
    sregValue L g ⟨.clusterCtaid, some .x⟩ = some (g / L.block % L.clusterSize.val) ∧
    sregValue L g ⟨.clusterNctaid, some .x⟩ = some L.clusterSize.val ∧
    sregValue L g ⟨.clusterCtarank, none⟩ = some (g / L.block % L.clusterSize.val) ∧
    sregValue L g ⟨.clusterNctarank, none⟩ = some L.clusterSize.val ∧
    (∀ d, d ≠ .x → sregValue L g ⟨.tid, some d⟩ = some 0 ∧
      sregValue L g ⟨.ctaid, some d⟩ = some 0 ∧ sregValue L g ⟨.clusterid, some d⟩ = some 0 ∧
      sregValue L g ⟨.clusterCtaid, some d⟩ = some 0 ∧ sregValue L g ⟨.ntid, some d⟩ = some 1 ∧
      sregValue L g ⟨.nctaid, some d⟩ = some 1 ∧ sregValue L g ⟨.nclusterid, some d⟩ = some 1 ∧
      sregValue L g ⟨.clusterNctaid, some d⟩ = some 1) := by
  have ht := Launch.oneDim_tidOf h g
  have hcta := Launch.oneDim_ctaidOf h (g / L.block)
  have hcl := Launch.oneDim_clusteridOf h (g / L.block)
  have hr := Launch.oneDim_clusterCtaidOf h (g / L.block)
  have hncl := Launch.oneDim_nclusteridOf h (g / L.block)
  have hcn := Launch.oneDim_clusterNctaidOf h (g / L.block)
  have hco := Launch.oneDim_clusterOfCta h (g / L.block)
  have hra := Launch.oneDim_rankOfCta h (g / L.block)
  have hsz := Launch.oneDim_clusterSizeOf h (g / L.block)
  obtain ⟨hn, hg, -⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro d hd; cases d <;> first | exact absurd rfl hd |
        simp [sregValue, ht, hcta, hcl, hr, hncl, hcn, hco, hra, hn, hg, Dim3.get])
    | simp [sregValue, ht, hcta, hcl, hr, hncl, hcn, hco, hra, hsz, hn, hg, Dim3.get]

/-- The exclusive bound of a value read from a register that changes while the thread runs: the
register's width, and for `%smid` also the thread's `%nsmid` when it is positive (§10.8). -/
def SReg.readBound (L : Launch) (g : Nat) (s : SReg) : Nat :=
  match s.name with
  | .smid =>
    let n := L.sregInit g ⟨.nsmid, none⟩
    if n = 0 then 2 ^ 32 else min (2 ^ 32) n
  | _ => 2 ^ s.width

/-- REG: integer read of the low `w` bits of a thread-private register or operand. A register's
bits are its value's `bitPattern` (an integer's bits, `x`, directly). -/
def readBits (L : Launch) (g : Nat) (t : TState) (w : Nat) : Opnd → Exec (BitVec 64)
  | .reg r => do
    match ← readReg t r with
    | .bits _ x => pure (truncBits w x)
    | .ptr .. | .policy => throw .noRule
    | v => match v.bitPattern with
      | some n => pure (truncBits w (BitVec.ofNat 64 n))
      | none => throw .typeMismatch
  | .imm v => pure (truncBits w (BitVec.ofInt 64 v))
  | .f32imm b => if w = 32 then pure (BitVec.ofNat 64 b) else throw .typeMismatch
  | .sreg s => match sregValue L g s with
    | some v => pure (truncBits w (BitVec.ofNat 64 v))
    | none => throw .noRule
  | .sharedSym off => pure (truncBits w (BitVec.ofNat 64 (L.sharedBase + off)))
  | .localSym _ | .paramSym _ => throw .noRule

/-- Value read for data movement: registers unchanged; literals, including `0f` constants,
are their `w`-bit patterns. A `.pred` special register (`%is_explicit_cluster`) is a predicate. -/
def readValue (L : Launch) (g : Nat) (t : TState) (w : Nat) :
    Opnd → Exec Value
  | .reg r => readReg t r
  | .localSym off =>
    if w = 64 then pure (.bits 64 (BitVec.ofNat 64 (L.localBase + off))) else throw .typeMismatch
  | .paramSym name =>
    if w = 32 ∨ w = 64 then pure (.ptr w false (.param name) 0) else throw .typeMismatch
  | .sreg s =>
    if s.width = 1 then
      match sregValue L g s with
      | some v => pure (.pred (v % 2 = 1))
      | none => throw .noRule
    else return .bits w (← readBits L g t w (.sreg s))
  | o => return .bits w (← readBits L g t w o)

/-- A special register wider than a predicate is read for data movement as its bits, as before
the `.pred` special register existed. -/
theorem readValue_sreg {L : Launch} {g : Nat} {t : TState} {w : Nat} {s : SReg}
    (h : s.width ≠ 1) :
    readValue L g t w (.sreg s) = (return .bits w (← readBits L g t w (.sreg s))) := by
  simp [readValue, h]

/-! ## THREAD-TENSOR-MAP-ADDRESS — descriptor addresses from kernel parameters
Statement: The tensor map operand of a tensor instruction is either a numeric address or the
  symbolic generic address of a by-value parameter object that holds a full 128-byte descriptor. The
  address must be 64-byte aligned and name a descriptor that the host published, that is valid and
  that has the instruction's rank. In four-row mode the map must be 2D with box dimension 1 equal to
  1. Otherwise the instruction faults.

Defs: tensorMapAddress, TensorMode.transfer, TensorMode.rowCoordinates, tensorMap

Source:
- §5.1.6.1
- §9.7.10.23
- §9.7.10.28.5.3
- CUDA Driver API CUtensorMap (128-byte object)
- EXT-TMA-GEOMETRY (64-byte alignment)

Direction: scope

Applies: Numeric generic descriptor addresses and symbolic generic base addresses of by-value
  parameter objects; the tensor map operand of every tensor load, store, reduction and prefetch

Premises: A symbolic address has 64-bit generic representation and offset 0; its actual launch
  binding has the matching name, contains the full 128-byte descriptor, respects the declaration
  alignment and fits the address width.

Effect: Address resolution using immutable launch metadata. Parameter offsets and device-side
  descriptor mutation are outside this rule.
  The resolved address is the object's generic base, which stays distinct from the object's
  contents. `tensorMap` applies the map checks for tensor loads, stores and prefetches, and
  `TensorMode.transfer` and `TensorMode.rowCoordinates` give the transfer descriptor and the row
  coordinates of a mode.
-/
/-- The address of the tensor map named by operand `map`: a numeric address, or the generic base
of a by-value parameter object that holds a full descriptor. -/
def tensorMapAddress (L : Launch) (g : Nat) (t : TState) (map : Opnd) : Exec Nat := do
  match ← readValue L g t 64 map with
  | .ptr w generic (.param name) off =>
    unless w = 64 ∧ generic = true ∧ off = 0 do throw .badValue
    let some (decl, base) := L.paramObjects name | throw .badParam
    unless decl.name = name ∧ 128 ≤ decl.bytes ∧ 0 < decl.alignment ∧
      base % decl.alignment = 0 ∧ base + decl.bytes ≤ 2 ^ 64 do throw .badParam
    pure base
  | _ => pure (← readBits L g t 64 map).toNat

/-- The transfer descriptor of a copy in `mode`: the map's, or its four-row box. -/
@[simp] def TensorMode.transfer {outer : Nat} : TensorMode → TensorDescriptor.Descriptor outer →
    TensorDescriptor.Descriptor outer
  | .tile, d => d
  | .fourRows, d => d.fourRows

/-- The row coordinates a copy in `mode` records from its coordinate operands. -/
@[simp] def TensorMode.rowCoordinates : TensorMode → (Fin 4 → Int) → Option (Fin 4 → Int)
  | .tile, _ => none
  | .fourRows, ys => some ys

/-- The tensor map of a tensor instruction in `mode` with coordinates `cs`: its address (64-byte
aligned) and published descriptor, valid, of the instruction's rank (`TensorMode.coordinates`)
and, in four-row mode, 2D with box dimension 1 one (EXT-TMA-GATHER4, EXT-TMA-SCATTER4). -/
def tensorMap (L : Launch) (g : Nat) (t : TState) (map : Opnd) (cs : List Opnd)
    (mode : TensorMode) : Exec (Nat × (outer : Nat) × TensorDescriptor.Descriptor outer) := do
  let mapAddress ← tensorMapAddress L g t map
  unless mapAddress % 64 = 0 do throw .misaligned
  let some ⟨outer, descriptor⟩ := L.tensorMaps mapAddress | throw .noRule
  unless cs.length = mode.coordinates outer do throw .badValue
  unless TensorDescriptor.Valid descriptor do throw .badValue
  unless mode = .tile ∨ (outer = 1 ∧ descriptor.box.size 1 = 1) do throw .badValue
  pure (mapAddress, ⟨outer, descriptor⟩)

/-! ## THREAD-TENSORMAP-PREFETCH — tensormap prefetches
Statement: `prefetch.tensormap` takes a symbolic pointer to an allocated, aligned parameter object.
  It changes no register, reads no program value, writes no memory and publishes no descriptor, and
  it only advances the source position.

Defs: execTensorMapPrefetch

Source:
- §9.7.10.16 (prefetch.tensormap, generic addressing when unqualified)

Direction: scope

Applies: prefetch.tensormap of generic or explicit .param base addresses of immutable kernel
  parameter objects

Premises: The source is a symbolic parameter pointer with matching width/space and offset 0; its
  launch binding names an allocated, nonempty, aligned parameter object in range.

Effect: Local evaluation under the model's abstraction of caches. Constant-space addresses and
  device-updated descriptor caches need separate representation/rules. A tensor-data prefetch is an
  event (THREAD-TENSOR-PREFETCH).
-/
/-- `prefetch.tensormap`: checks its operand and advances the source position. -/
def execTensorMapPrefetch (L : Launch) (g : Nat) (t : TState) : Op → Exec TState
  | .prefetchTensorMap generic w src => do
    let .ptr pw pg (.param name) off ← readValue L g t w src | throw .noRule
    unless (w = 32 ∨ w = 64) ∧ pw = w ∧ pg = generic ∧ off = 0 do throw .badValue
    let some (decl, base) := L.paramObjects name | throw .badParam
    unless decl.name = name ∧ 0 < decl.bytes ∧ 0 < decl.alignment ∧
      base % decl.alignment = 0 ∧ base + decl.bytes ≤ 2 ^ w do throw .badParam
    pure (next t)
  | _ => throw .noRule

/-! ## THREAD-POINTER-OFFSET — arithmetic on symbolic addresses
Statement: Adding or subtracting an integer from a symbolic shared pointer, or from a generic local
  or constant pointer, changes its byte offset and keeps its representation, its target and the
  thread or CTA it belongs to. The new offset must stay within `[0, 2 ^ 32)` without wrapping,
  otherwise the instruction has no rule.

Defs: offsetPointer, offsetPointer_shared

Source:
- §6.4.1.1 (generic address windows)
- §9.7.1.1 (add)
- §9.7.1.2 (sub)

Direction: reading

Applies: Addition/subtraction of an integer displacement to a symbolic shared pointer or to a
  generic local or constant pointer (THREAD-CVTA)

Premises: The instruction width matches the pointer, and the resulting logical offset is
  representable without wrapping. A consumed pointer must still refer to allocated shared memory of
  its recorded target CTA.

Effect: Local pointer arithmetic. Arbitrary bit inspection, pointer-pair arithmetic and
  out-of-window targets are not modeled as new addresses in another CTA.
  The base of a generic window cancels in the offset calculation. A generic local or constant
  pointer moves inside its window in the same way as a shared pointer; an offset at or above
  `2 ^ 32` has no rule. A shared pointer whose offset is at or above `2 ^ 32` before the move has
  no rule either, and a parameter pointer has no offset arithmetic.
-/

/-- A symbolic shared, local or constant pointer moved by `delta` bytes; any other value has no
rule. A shared pointer must start below `2 ^ 32`. -/
def offsetPointer (w : Nat) (v : Value) (delta : Int) : Exec Value := do
  let .ptr pw generic sp offset := v | throw .noRule
  let startOk : Bool := match sp with
    | .shared .. => decide (offset.toNat < 2 ^ 32)
    | .param _ => false
    | .local _ | .const => true
  unless w = pw ∧ (w = 32 ∨ w = 64) do throw .noRule
  let result := (offset.toNat : Int) + delta
  unless startOk ∧ 0 ≤ result ∧ result < 2 ^ 32 do throw .noRule
  pure (.ptr w generic sp (BitVec.ofInt 64 result))

/-- A shared pointer moves as the shared pointer arithmetic did before the pointer forms were one
value. -/
theorem offsetPointer_shared {w pw : Nat} {generic : Bool} {issuer cta : Nat}
    {offset : BitVec 64} {delta : Int} :
    offsetPointer w (.ptr pw generic (.shared issuer cta) offset) delta = (do
      unless w = pw ∧ (w = 32 ∨ w = 64) do throw .noRule
      let result := (offset.toNat : Int) + delta
      unless offset.toNat < 2 ^ 32 ∧ 0 ≤ result ∧ result < 2 ^ 32 do throw .noRule
      pure (.ptr w generic (.shared issuer cta) (BitVec.ofInt 64 result))) := by
  simp [offsetPointer]

/-! ## THREAD-INT — integer instructions
Statement: An integer instruction computes exactly the result of its Semantics section on the low
  bits of its operands, read as two's complement for the signed types, and the result wraps at the
  destination width unless `.sat` clamps it. A result the manual leaves unspecified (division or
  remainder by zero, a quotient or remainder whose rounding the manual leaves open, a `mul24`
  operand that is not a 24-bit value) has no rule, and `fns` with a base above 31 is undefined.
  The extended-precision instructions add the carry flag `CC.CF` where their Semantics sections
  read it and write the carry-out or borrow-out to it under `.cc`; reading the flag before an
  instruction has written it has no rule.

Defs: execInt, compare, readPred, readPred_reg, setDst, BoolOp.eval, boolCombine, intOf, intBits,
  intSat, intLane, intOfLanes, bitsFrom, highBit, intDiv, intRem, int24, bfindBits, fnsBits,
  bfeBits, bfiBits, szextBits, bmskBits, lop3Bits, shfBits, prmtTable, prmtBits, clmulBits, dotBits,
  carryIn, setCarry, intResult

Source:
- §9.7.1.1 (add): "Saturation modifier: .sat limits result to MININT..MAXINT (no overflow) for the
    size and signedness of the operation."
- §9.7.1.1 (add): "Half-word operands are then added in parallel to produce .u16x2 , .s16x2 result
    in destination."
- §9.7.1.2 (sub): "d = a - b;"
- §9.7.1.3 (mul): "d = t<2n-1..n>; // for .hi variant"
- §9.7.1.3 (mul): "If .wide is specified, then d is twice as wide as a and b to receive the full
    result of the multiplication."
- §9.7.1.4 (mad): "d = t<2n-1..n> + c; // for .hi variant"
- §9.7.1.4 (mad): "If .wide is specified, then d and c are twice as wide as a and b to receive the
    result of the multiplication."
- §9.7.1.4 (mad): "Saturation modifier: .sat limits result to MININT..MAXINT (no overflow) for the
    size of the operation. Applies only to .s32 type in .hi mode."
- §9.7.1.6 (mul24): "Compute the product of two 24-bit integer values held in 32-bit source
    registers"
- §9.7.1.6 (mul24): "d = t<47..16>; // for .hi variant"
- §9.7.1.7 (mad24): "d = t<47..16> + c; // for .hi variant"
- §9.7.1.7 (mad24): "Saturation modifier: .sat limits result of 32-bit signed addition to
    MININT..MAXINT (no overflow)."
- §9.7.1.8 (sad): "d = c + ((a<b) ? b-a : a-b);"
- §9.7.1.9 (div): "Division by zero yields an unspecified, machine-specific value."
- §9.7.1.10 (rem): "The behavior for negative numbers is machine-dependent and depends on whether
    divide rounds toward zero or negative infinity."
- §9.7.1.11 (abs): "d = |a|;"
- §9.7.1.12 (neg): "d = -a;"
- §9.7.1.13 (min): "d = (a < b) ? a : b; // Integer (signed and unsigned)"
- §9.7.1.13 (min): "Saturation modifier: min.relu.{s8x4, s16x2, s32} clamps the result to 0 if
    negative."
- §9.7.1.14 (max): "d = (a > b) ? a : b; // Integer (signed and unsigned)"
- §9.7.1.15 (popc): "Count the number of one bits in a and place the resulting population count in
    32-bit destination register d ."
- §9.7.1.16 (clz): "Count the number of leading zeros in a starting with the most-significant bit"
- §9.7.1.17 (bfind): "For signed integers, bfind returns the bit position of the most significant 0
    for negative inputs and the most significant 1 for non-negative inputs."
- §9.7.1.17 (bfind): "bfind returns 0xffffffff if no non-sign bit is found."
- §9.7.1.18 (fns): "Operand base must be <= 31, otherwise behavior is undefined."
- §9.7.1.19 (brev): "d[i] = a[msb-i];"
- §9.7.1.20 (bfe): "d[i] = (i<len && pos+i<=msb) ? a[pos+i] : sbit;"
- §9.7.1.21 (bfi): "f[pos+i] = a[i];"
- §9.7.1.22 (szext): "d = (a & ~mask) | (sign_bit ? mask : 0);"
- §9.7.1.23 (bmsk): "d = mask0 & ~mask1;"
- §9.7.9.1–§9.7.9.4 (and, or, xor, not): "Allowed types include predicate registers."
- §9.7.9.1–§9.7.9.4 (not): "Invert the bits in a ."
- §9.7.9.5 (cnot): "d = (a==0) ? 1 : 0;"
- §9.7.9.6 (lop3): "ta = 0xF0; tb = 0xCC; tc = 0xAA; immLut = F(ta, tb, tc);"
- §9.7.9.6 (lop3): "p = (d != 0) BoolOp q;"
- §9.7.9.7 (shf): "Operand b holds bits 63:32 and operand a holds bits 31:0 of the 64-bit source
    value."
- §9.7.9.7 (shf): "For shf.l , the most-significant 32-bits of the result are written into d ; for
    shf.r , the least-significant 32-bits of the result are written into d ."
- §9.7.9.7 (shf): "u32 n = (.mode == .clamp) ? min(c, 32) : c & 0x1f;"
- §9.7.9.8 (shl): "Shift amounts greater than the register width N are clamped to N ."
- §9.7.9.9 (shr): "Signed shifts fill with the sign bit, unsigned and untyped shifts fill with 0 ."
- §9.3.2: "Predicate values may be computed and manipulated using the following instructions: and ,
    or , xor , not , and mov ."
- §9.7.10.7 (prmt): "The 3 lsbs of the selection value specify which of the 8 source bytes should be
    moved into the target position."
- §9.7.10.7 (prmt): "msb=0 means copy the literal value; msb=1 means replicate the sign."
- §9.7.1.5 (clmad): "tmp[127:0] = 0; // 128-bit result of carryless multiplication. for (i = 0; i <
    64; i++) { if ((a & (1 << i)) != 0) { tmp ^= b << i; } }"
- §9.7.1.5 (clmad): "if (.mode == .lo) { d = tmp[63..0]; } else { d = tmp[127..64]; } d ^= c; //
    carryless accumulation."
- §9.7.1.24 (dp4a): "Operand c has type .u32 if both .atype and .btype are .u32 else operand c has
    type .s32 ."
- §9.7.1.24 (dp4a): "Va = extractAndSignOrZeroExt_4(a, .atype); Vb = extractAndSignOrZeroExt_4(b,
    .btype); for (i = 0; i < 4; ++i) { d += Va[i] * Vb[i]; }"
- §9.7.1.25 (dp2a): "Va = extractAndSignOrZeroExt_2(a, .atype);"
- §9.7.1.25 (dp2a): "b_select = (.mode == .lo) ? 0 : 2; for (i = 0; i < 2; ++i) { d += Va[i] *
    Vb[b_select + i]; }"
- §9.7.2: "No other instructions access the condition code, and there is no support for setting,
    clearing, or testing the condition code."
- §9.7.2 (add.cc): "d = a + b; carry-out written to CC.CF"
- §9.7.2 (addc): "d = a + b + CC.CF; if .cc specified, carry-out written to CC.CF"
- §9.7.2 (sub.cc): "d = a - b; borrow-out written to CC.CF"
- §9.7.2 (subc): "d = a - (b + CC.CF); if .cc specified, borrow-out written to CC.CF"
- §9.7.2: "Behavior is the same for unsigned and signed integers."
- §9.7.2 (mad.cc): "t = a * b; d = t<63..32> + c; // for .hi variant d = t<31..0> + c; // for .lo
    variant carry-out from addition is written to CC.CF"
- §9.7.2 (madc): "d = t<63..32> + c + CC.CF; // for .hi variant d = t<31..0> + c + CC.CF; // for .lo
    variant if .cc specified, carry-out from addition is written to CC.CF"
- §9.7.7.1 (set): "If this result is True , 1.0f is written for floating-point destination types,
    and 0xffffffff is written for integer destination types. Otherwise, 0x00000000 is written."
- §9.7.7.1 (set): "If the result is True, 0xffff is written to the destination register at a
    bit-position corresponding to input half word values."
- §9.7.7.2 (setp): "t = (a CmpOp b) ? 1 : 0; p = BoolOp(t, c); q = BoolOp(!t, c);"
- §9.7.7.2 (setp): "The sink symbol ‘_’ may be used in place of any one of the destination
    operands."
- §9.3.1.1 (integer comparisons)
- §4.5.3: "For predicate-type data initializers and instruction operands, integer constants are
    interpreted as in C, i.e., zero values are False and non-zero values are True ."

Direction: stricter

Applies: The integer instructions whose rule is THREAD-INT (`IntInstr.rule`, PROG-ISA-INT)

Premises: Operands satisfy the register rules and the instruction's width restrictions; a `.pred`
  operand is a register holding a predicate.

Effect: Local evaluation; an unspecified result is `noRule`, and an `fns` base above 31 is
  `badValue`.
  Integers are exact bit vectors, and every result is truncated to its destination width
  (wraparound), as `neg` and `abs` of the most negative value are. A packed type such as `.u16x2`
  computes each lane of its own width and kind (`intLane`, `intOfLanes`), lane 0 lowest. `.sat`
  clamps the exact result to the range of the lane type (`intSat`); `.relu` clamps a negative `min`
  or `max` to 0. `mul.hi` keeps the upper half of the double-width product, `mul.wide` all of it;
  `mad` adds `c` to that half (of the width of `d` for `.wide`). `mul24` and `mad24` take
  `t<47..16>` or `t<31..0>` of the exact product. Shifts by the width or more give `0`, or for
  `shr.s` the sign bit in every position (the amount is clamped to the width). The bit instructions
  `popc`, `clz`, `bfind`, `fns`, `brev`, `bfe`, `bfi`, `szext`, `bmsk`, `lop3`, `shf` and `prmt`
  transcribe the loops and tables of their Semantics sections; `shf` shifts the 64-bit value `b:a`
  as its Description states, which gives `b` for `shf.l` by 0 and `a` by 32. A logic instruction of
  width 1 is the `.pred` type: it reads predicate registers and integer constants (zero is false,
  non-zero true; `readPred`) and writes a predicate; any other source value is a type error.
  `setp` writes `BoolOp(t, c)` to `p` and `BoolOp(!t, c)` to `q`, and
  `set` writes all ones (or `1.0f`, the bits `0x3F800000`, for an `.f32` destination) per true lane.
  The manual gives no result for division or remainder by zero, for a quotient that does not fit the
  type (the most negative value divided by -1), or for a signed quotient or remainder whose value
  depends on the rounding of the division: `intDiv` has no rule when the quotient is negative and
  inexact (where rounding toward zero and toward negative infinity differ), and `intRem` has none
  when an operand of a signed remainder is negative. A `mul24` or `mad24` operand that is not a
  24-bit value of its type has no 24-bit product, and has no rule. Each of these is `noRule`, so a
  kernel assumption may supply the machine's value; without one the execution is undefined
  (Direction: stricter). A `setp` whose `p` and `q` are the same register has no rule
  (`IntInstr.rule`), since the manual does not say which value the register keeps.
  `clmad` transcribes its Semantics loop (`clmulBits`). `dp4a` and `dp2a` extend the bytes or
  half-words of their operands by `.atype` and `.btype` and add the products to `c` read as `.u32`
  or `.s32` (`dotBits`); the sum wraps at 32 bits. The extended-precision instructions keep the
  carry flag `CC.CF` in the thread state (THREAD-STATE). The carry-in is `CC.CF` for `addc`, `subc`
  and `madc` and 0 for the others (`carryIn`). The carry-out of an addition of `n`-bit values is 1
  exactly when the unsigned sum of the bit patterns and the carry-in is at least `2^n`, which is the
  same for signed and unsigned types; the borrow-out of `a - (b + CC.CF)` is 1 exactly when the
  unsigned `a` is below `b + CC.CF`. `mad.cc` and `madc` take the half `t<2n-1..n>` or `t<n-1..0>`
  of the product read by the type, as `mad.hi` does, and add `c` as unsigned bit patterns. The flag
  is written only under `.cc` (`setCarry`). The manual gives the flag no initial value, so an
  instruction that reads `CC.CF` before any instruction of the thread has written it has no rule
  (`noRule`). Calls are not modeled, so the sentence that the flag is not preserved across calls
  does not apply.
-/

/-- The result of comparing `a` and `b` at width `w` under `cmp`, read as `ty`. -/
def compare (cmp : Cmp) (ty : IType) (w : Nat) (a b : BitVec 64) : Bool :=
  let (x, y) : Int × Int := match ty with
    | .s => (toSigned w a, toSigned w b)
    | _ => ((a.toNat : Int), (b.toNat : Int))
  match cmp with
  | .eq => x = y | .ne => x ≠ y | .lt | .lo => x < y
  | .le | .ls => x ≤ y | .gt | .hi => x > y | .ge | .hs => x ≥ y

/-- A `.pred` operand: a register holding a predicate, a `.pred` special register
(`%is_explicit_cluster`, THREAD-SREG), or an integer constant (zero is false, non-zero true,
§4.5.3). -/
def readPred (L : Launch) (g : Nat) (t : TState) : Opnd → Exec Bool
  | .reg r => do
    match ← readReg t r with
    | .pred b => pure b
    | _ => throw .typeMismatch
  | .sreg s =>
    if s.width = 1 then
      match sregValue L g s with
      | some v => pure (v % 2 = 1)
      | none => throw .noRule
    else throw .typeMismatch
  | .imm v => pure (v ≠ 0)
  | _ => throw .typeMismatch

/-- A predicate register is read as before the special `.pred` source existed. -/
theorem readPred_reg (L : Launch) (g : Nat) (t : TState) (r : Nat) :
    readPred L g t (.reg r) = (do
      match ← readReg t r with
      | .pred b => pure b
      | _ => throw .typeMismatch) := rfl

/-- Write `v` to the destination `d`; the sink `_` (`none`) writes nothing. -/
def setDst (t : TState) : Option Nat → Value → TState
  | some r, v => setReg t r v
  | none, _ => t

/-- The `.BoolOp` of a comparison applied to two truth values. -/
def BoolOp.eval : BoolOp → Bool → Bool → Bool
  | .and, x, y => x && y
  | .or, x, y => x || y
  | .xor, x, y => x ^^ y

/-- The function `t ↦ BoolOp(t, c)` of a comparison: the identity without `.BoolOp`, otherwise
the operator applied with the predicate source `c`. -/
def boolCombine (L : Launch) (g : Nat) (t : TState) : Option BoolOp → List Opnd → Exec (Bool → Bool)
  | none, [] => pure id
  | some op, [c] => do
    let q ← readPred L g t c
    pure (fun x => op.eval x q)
  | _, _ => throw .noRule

/-- The integer the low `w` bits of `x` denote: two's complement for `.s`, unsigned
otherwise. -/
def intOf (k : IType) (w : Nat) (x : BitVec 64) : Int :=
  if k = .s then toSigned w x else ((x.toNat % 2 ^ w : Nat) : Int)

/-- The low `w` bits of the two's complement of `z`. -/
def intBits (w : Nat) (z : Int) : BitVec 64 := truncBits w (BitVec.ofInt 64 z)

/-- `z` clamped to the range of `w`-bit integers of kind `k` when `sat` (`.sat`), otherwise
`z`. -/
def intSat (sat : Bool) (k : IType) (w : Nat) (z : Int) : Int :=
  if !sat then z
  else if k = .s then max (-2 ^ (w - 1)) (min z (2 ^ (w - 1) - 1)) else max 0 (min z (2 ^ w - 1))

/-- Lane `j` of the `lw`-bit lanes of `x`, lane 0 lowest. -/
def intLane (lw j : Nat) (x : BitVec 64) : BitVec 64 := truncBits lw (x >>> (lw * j))

/-- The `n` lanes `f 0`, …, `f (n - 1)` of `lw` bits each, lane 0 lowest. -/
def intOfLanes (lw n : Nat) (f : Nat → BitVec 64) : BitVec 64 :=
  (List.range n).foldr (fun j acc => acc ||| (truncBits lw (f j) <<< (lw * j))) 0

/-- The `w`-bit number whose bit `j` is `f j`. -/
def bitsFrom (w : Nat) (f : Nat → Bool) : Nat :=
  (List.range w).foldr (fun j acc => if f j then acc + 2 ^ j else acc) 0

/-- The position of the most significant set bit among the low `w` bits of `x`. -/
def highBit (w x : Nat) : Option Nat := (List.range w).reverse.find? x.testBit

/-- `div` (§9.7.1.9): the quotient, rounded toward zero; no rule for a zero divisor, a quotient
outside the type, or a negative inexact quotient, whose rounding the manual leaves open. -/
def intDiv (k : IType) (w : Nat) (x y : BitVec 64) : Exec Int := do
  let a := intOf k w x
  let b := intOf k w y
  if b = 0 then throw .noRule
  if a.tmod b ≠ 0 ∧ (a < 0) ≠ (b < 0) then throw .noRule
  if k = .s ∧ a.tdiv b ≥ 2 ^ (w - 1) then throw .noRule
  pure (a.tdiv b)

/-- `rem` (§9.7.1.10): the remainder; no rule for a zero divisor or a negative operand of a
signed remainder. -/
def intRem (k : IType) (w : Nat) (x y : BitVec 64) : Exec Int := do
  let a := intOf k w x
  let b := intOf k w y
  if b = 0 then throw .noRule
  if k = .s ∧ (a < 0 ∨ b < 0) then throw .noRule
  pure (a.tmod b)

/-- A 24-bit operand of `mul24`/`mad24` held in a 32-bit register: its value when it is a 24-bit
value of kind `k`, otherwise no rule. -/
def int24 (k : IType) (x : BitVec 64) : Exec Int :=
  let a := intOf k 32 x
  if (k = .s ∧ -2 ^ 23 ≤ a ∧ a < 2 ^ 23) ∨ (k ≠ .s ∧ a < 2 ^ 24) then pure a
  else throw .noRule

/-- `bfind` (§9.7.1.17) of the `w`-bit value `x`. -/
def bfindBits (k : IType) (w : Nat) (shiftamt : Bool) (x : Nat) : Nat :=
  let msb := w - 1
  let a := if k = .s ∧ x.testBit msb then 2 ^ w - 1 - x else x
  match highBit w a with
  | none => 0xffffffff
  | some d => if shiftamt then msb - d else d

/-- `fns` (§9.7.1.18): the position of the `|offset|`-th set bit of `mask` from `base` upward
(downward for a negative offset), the bit `base` itself for offset 0, or `0xffffffff`. -/
def fnsBits (mask base : Nat) (offset : Int) : Nat :=
  if offset = 0 then (if mask.testBit base then base else 0xffffffff)
  else
    let ps := if offset > 0 then (List.range 32).filter (fun p => base ≤ p ∧ mask.testBit p)
      else ((List.range 32).filter (fun p => p ≤ base ∧ mask.testBit p)).reverse
    ps[offset.natAbs - 1]?.getD 0xffffffff

/-- `bfe` (§9.7.1.20) of the `w`-bit value `x` with start `pos` and length `len`. -/
def bfeBits (k : IType) (w x pos len : Nat) : Nat :=
  let msb := w - 1
  let sbit := if k ≠ .s ∨ len = 0 then false else x.testBit (min (pos + len - 1) msb)
  bitsFrom w fun i => if i < len ∧ pos + i ≤ msb then x.testBit (pos + i) else sbit

/-- `bfi` (§9.7.1.21): `b` with the low `len` bits of `a` inserted from bit `pos`. -/
def bfiBits (w a b pos len : Nat) : Nat :=
  bitsFrom w fun i => if pos ≤ i ∧ i - pos < len then a.testBit (i - pos) else b.testBit i

/-- `szext` (§9.7.1.22) of the 32-bit values `a` and `b`, signed when `s`. -/
def szextBits (s clamp : Bool) (a b : Nat) : Nat :=
  let ones := 2 ^ 32 - 1
  let b1 := b % 32
  let tooLarge := b ≥ 32 ∧ clamp
  let mask := if tooLarge then 0 else (ones <<< b1) % 2 ^ 32
  let signPos := (b1 + 31) % 32
  let signBit := if b1 = 0 ∨ tooLarge ∨ !s then false else a.testBit signPos
  (a &&& (ones ^^^ mask)) ||| (if signBit then mask else 0)

/-- `bmsk` (§9.7.1.23) of the 32-bit values `a` and `b`. -/
def bmskBits (clamp : Bool) (a b : Nat) : Nat :=
  let ones := 2 ^ 32 - 1
  let a1 := a % 32
  let b1 := b % 32
  let sum := a1 + b1
  let posOverflow := clamp ∧ a ≥ 32
  let widthOverflow := clamp ∧ b ≥ 32
  let mask0 := if posOverflow then 0 else (ones <<< a1) % 2 ^ 32
  let mask1 := if sum ≥ 32 ∨ posOverflow ∨ widthOverflow then 0
    else if b1 = 0 then ones else (ones <<< sum) % 2 ^ 32
  mask0 &&& (ones ^^^ mask1)

/-- `lop3` (§9.7.9.6): bit `i` of the result is bit `4 a[i] + 2 b[i] + c[i]` of `lut`, since
`immLut = F(0xF0, 0xCC, 0xAA)`. -/
def lop3Bits (lut a b c : Nat) : Nat :=
  let bit (x i : Nat) : Nat := if x.testBit i then 1 else 0
  bitsFrom 32 fun i => lut.testBit (4 * bit a i + 2 * bit b i + bit c i)

/-- `shf` (§9.7.9.7): the 64-bit value `b:a` shifted by the clamped or wrapped amount `c`; the
upper 32 bits for a left shift, the lower 32 bits for a right shift. -/
def shfBits (left clamp : Bool) (a b c : Nat) : Nat :=
  let n := if clamp then min c 32 else c % 32
  let v := b * 2 ^ 32 + a
  if left then v * 2 ^ n % 2 ^ 64 / 2 ^ 32 else v / 2 ^ n % 2 ^ 32

/-- The source bytes of `d.b3`, `d.b2`, `d.b1`, `d.b0` of a `prmt` mode for the selector
`c[1:0]` (§9.7.10.7, the table of modes). -/
def prmtTable : PrmtMode → Nat → List Nat
  | .f4e, 0 => [3, 2, 1, 0] | .f4e, 1 => [4, 3, 2, 1]
  | .f4e, 2 => [5, 4, 3, 2] | .f4e, _ => [6, 5, 4, 3]
  | .b4e, 0 => [5, 6, 7, 0] | .b4e, 1 => [6, 7, 0, 1]
  | .b4e, 2 => [7, 0, 1, 2] | .b4e, _ => [0, 1, 2, 3]
  | .rc8, 0 => [0, 0, 0, 0] | .rc8, 1 => [1, 1, 1, 1]
  | .rc8, 2 => [2, 2, 2, 2] | .rc8, _ => [3, 3, 3, 3]
  | .ecl, 0 => [3, 2, 1, 0] | .ecl, 1 => [3, 2, 1, 1]
  | .ecl, 2 => [3, 2, 2, 2] | .ecl, _ => [3, 3, 3, 3]
  | .ecr, 0 => [0, 0, 0, 0] | .ecr, 1 => [1, 1, 1, 0]
  | .ecr, 2 => [2, 2, 1, 0] | .ecr, _ => [3, 2, 1, 0]
  | .rc16, 0 => [1, 0, 1, 0] | .rc16, 1 => [3, 2, 3, 2]
  | .rc16, 2 => [1, 0, 1, 0] | .rc16, _ => [3, 2, 3, 2]

/-- `prmt` (§9.7.10.7): four bytes of `{b, a}`, chosen by the 4-bit selectors of `c` (the msb
replicates the sign of the byte) or by a mode's table. -/
def prmtBits (mode : Option PrmtMode) (a b c : Nat) : Nat :=
  let tmp := b * 2 ^ 32 + a
  let byte (j : Nat) : Nat := tmp / 2 ^ (8 * j) % 256
  let sel (k : Nat) : Nat := match mode with
    | none =>
      let ctl := c / 2 ^ (4 * k) % 16
      let v := byte (ctl % 8)
      if ctl < 8 then v else if v < 128 then 0 else 255
    | some m => byte ((prmtTable m (c % 4)).getD (3 - k) 0)
  sel 0 + 2 ^ 8 * sel 1 + 2 ^ 16 * sel 2 + 2 ^ 24 * sel 3

/-- The carryless product of the 64-bit values `a` and `b` (§9.7.1.5): the exclusive or of `b`
shifted left by `i` for every set bit `i` of `a`, 128 bits wide. -/
def clmulBits (a b : Nat) : Nat :=
  (List.range 64).foldl (fun acc i => if a.testBit i then acc ^^^ (b <<< i) else acc) 0

/-- `dp4a` and `dp2a` (§9.7.1.24, §9.7.1.25): `c` plus the products of the `n` lanes of `la` bits
of `a` (kind `ak`) with the `8`-bit lanes `first`, …, `first + n - 1` of `b` (kind `bk`). -/
def dotBits (ak bk : IType) (la n first : Nat) (a b c : BitVec 64) : BitVec 64 :=
  let ck : IType := if ak = .u ∧ bk = .u then .u else .s
  intBits 32 ((List.range n).foldl (fun acc i =>
    acc + intOf ak la (intLane la i a) * intOf bk 8 (intLane 8 (first + i) b)) (intOf ck 32 c))

/-- The carry-in of an extended-precision instruction (§9.7.2): `CC.CF` when the instruction
reads it, which has no rule before an instruction has written it, and 0 otherwise. -/
def carryIn (t : TState) (cin : Bool) : Exec Nat :=
  if cin then match t.cf with
    | some c => pure (if c then 1 else 0)
    | none => throw .noRule
  else pure 0

/-- `CC.CF` set to `c` when the instruction writes the carry flag (`.cc`). -/
def setCarry (t : TState) (cout c : Bool) : TState := if cout then { t with cf := some c } else t

/-- The value of an integer instruction with one destination, for every form outside the scalar
arms of `execInt`. -/
def intResult (L : Launch) (g : Nat) (t : TState) (i : IntInstr) : Exec Value := do
  let w := i.ty.width
  let some (k, lw, n) := i.ty.intLanes? | throw .noRule
  let fit (z : Int) : Int := intSat i.sat k lw z
  let lanes (f : Int → Int → Int) (a b : Opnd) : Exec Value := do
    let x ← readBits L g t w a
    let y ← readBits L g t w b
    pure (.bits w (intOfLanes lw n fun j =>
      intBits lw (f (intOf k lw (intLane lw j x)) (intOf k lw (intLane lw j y)))))
  let relu (r : Bool) (z : Int) : Int := if r then max z 0 else z
  let nat32 (o : Opnd) : Exec Nat := do pure (← readBits L g t 32 o).toNat
  match i.op, i.srcs with
  | .add, [a, b] => lanes (fun x y => fit (x + y)) a b
  | .sub, [a, b] => lanes (fun x y => fit (x - y)) a b
  | .min r, [a, b] => lanes (fun x y => relu r (min x y)) a b
  | .max r, [a, b] => lanes (fun x y => relu r (max x y)) a b
  | .mad .hi, [a, b, c] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b; let z ← readBits L g t w c
    pure (.bits w (intBits w (fit (intOf k w x * intOf k w y / 2 ^ w + intOf k w z))))
  | .mad .wide, [a, b, c] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b; let z ← readBits L g t (2 * w) c
    pure (.bits (2 * w) (intBits (2 * w) (intOf k w x * intOf k w y + intOf k (2 * w) z)))
  | .mul24 hi, [a, b] => do
    let p := (← int24 k (← readBits L g t 32 a)) * (← int24 k (← readBits L g t 32 b))
    pure (.bits 32 (intBits 32 (if hi then p / 2 ^ 16 else p)))
  | .mad24 hi, [a, b, c] => do
    let p := (← int24 k (← readBits L g t 32 a)) * (← int24 k (← readBits L g t 32 b))
    let z ← readBits L g t 32 c
    pure (.bits 32 (intBits 32 (fit ((if hi then p / 2 ^ 16 else p) + intOf k 32 z))))
  | .sad, [a, b, c] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b; let z ← readBits L g t w c
    pure (.bits w (intBits w (intOf k w z + |intOf k w x - intOf k w y|)))
  | .div, [a, b] => do
    pure (.bits w (intBits w (← intDiv k w (← readBits L g t w a) (← readBits L g t w b))))
  | .rem, [a, b] => do
    pure (.bits w (intBits w (← intRem k w (← readBits L g t w a) (← readBits L g t w b))))
  | .abs, [a] => do pure (.bits w (intBits w |intOf k w (← readBits L g t w a)|))
  | .clmad hi, [a, b, c] => do
    let p := clmulBits (← readBits L g t 64 a).toNat (← readBits L g t 64 b).toNat
    let half := if hi then p / 2 ^ 64 % 2 ^ 64 else p % 2 ^ 64
    pure (.bits 64 (BitVec.ofNat 64 (half ^^^ (← readBits L g t 64 c).toNat)))
  | .dp4a ak bk, [a, b, c] => do
    pure (.bits 32 (dotBits ak bk 8 4 0
      (← readBits L g t 32 a) (← readBits L g t 32 b) (← readBits L g t 32 c)))
  | .dp2a hi ak bk, [a, b, c] => do
    pure (.bits 32 (dotBits ak bk 16 2 (if hi then 2 else 0)
      (← readBits L g t 32 a) (← readBits L g t 32 b) (← readBits L g t 32 c)))
  | .popc, [a] => do
    let x := (← readBits L g t w a).toNat
    pure (.bits 32 (BitVec.ofNat 64 ((List.range w).filter x.testBit).length))
  | .clz, [a] => do
    let x := (← readBits L g t w a).toNat
    pure (.bits 32 (BitVec.ofNat 64 (match highBit w x with | none => w | some j => w - 1 - j)))
  | .bfind sa, [a] => do
    pure (.bits 32 (BitVec.ofNat 64 (bfindBits k w sa (← readBits L g t w a).toNat)))
  | .fns, [m, base, off] => do
    let x ← nat32 m; let p ← nat32 base; let o ← readBits L g t 32 off
    unless p ≤ 31 do throw .badValue
    pure (.bits 32 (BitVec.ofNat 64 (fnsBits x p (toSigned 32 o))))
  | .brev, [a] => do
    let x := (← readBits L g t w a).toNat
    pure (.bits w (BitVec.ofNat 64 (bitsFrom w fun j => x.testBit (w - 1 - j))))
  | .bfe, [a, b, c] => do
    let x := (← readBits L g t w a).toNat
    let pos := (← nat32 b) % 256; let len := (← nat32 c) % 256
    pure (.bits w (BitVec.ofNat 64 (bfeBits k w x pos len)))
  | .bfi, [a, b, c, d] => do
    let x := (← readBits L g t w a).toNat; let y := (← readBits L g t w b).toNat
    let pos := (← nat32 c) % 256; let len := (← nat32 d) % 256
    pure (.bits w (BitVec.ofNat 64 (bfiBits w x y pos len)))
  | .szext clamp, [a, b] => do
    pure (.bits 32 (BitVec.ofNat 64 (szextBits (k == .s) clamp (← nat32 a) (← nat32 b))))
  | .bmsk clamp, [a, b] => do
    pure (.bits 32 (BitVec.ofNat 64 (bmskBits clamp (← nat32 a) (← nat32 b))))
  | .cnot, [a] => do
    pure (.bits w (if (← readBits L g t w a) = 0 then 1 else 0))
  | .lop3 lut none, [a, b, c] => do
    pure (.bits 32 (BitVec.ofNat 64 (lop3Bits lut.toNat (← nat32 a) (← nat32 b) (← nat32 c))))
  | .shf left clamp, [a, b, c] => do
    pure (.bits 32 (BitVec.ofNat 64 (shfBits left clamp (← nat32 a) (← nat32 b) (← nat32 c))))
  | .prmt mode, [a, b, c] => do
    pure (.bits 32 (BitVec.ofNat 64 (prmtBits mode (← nat32 a) (← nat32 b) (← nat32 c))))
  | .setp c (some bop), [a, b, q] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b
    pure (.pred (bop.eval (compare c k w x y) (← readPred L g t q)))
  | .set c bop dst, a :: b :: cs => do
    let x ← readBits L g t w a; let y ← readBits L g t w b
    let f ← boolCombine L g t bop cs
    if n = 1 then
      let one : BitVec 64 := if dst = .float .f32 then 0x3F800000 else 0xFFFFFFFF
      pure (.bits 32 (if f (compare c k w x y) then one else 0))
    else
      pure (.bits w (intOfLanes lw n fun j =>
        if f (compare c k lw (intLane lw j x) (intLane lw j y)) then intBits lw (-1) else 0))
  | _, _ => throw .noRule

/-- Integer arithmetic, logic, shifts and comparisons. The scalar `add` and `sub` arms also move
symbolic pointers (THREAD-POINTER-OFFSET); every other one-destination form is
`intResult`. -/
def execInt (L : Launch) (g : Nat) (t : TState) (i : IntInstr) : Exec TState :=
  let w := i.ty.width
  let signed := i.ty.kind? == some .s
  match i.op, i.ty, i.sat, i.dsts, i.srcs with
  | .add, _, true, [some d], _ | .sub, _, true, [some d], _
  | .add, .packed _ _, _, [some d], _ | .sub, .packed _ _, _, [some d], _
  | .min false, .packed _ _, _, [some d], _ | .max false, .packed _ _, _, [some d], _ => do
    let v ← intResult L g t i
    pure (next (setReg t d v))
  | .add, _, _, [some d], [a, b] => do
    let va ← readValue L g t w a
    let vb ← readValue L g t w b
    match va, vb with
    | .ptr _ _ (.shared ..) _, .bits _ _ | .ptr _ _ (.local _) _, .bits _ _
    | .ptr _ _ .const _, .bits _ _ =>
      let delta ← readBits L g t w b
      let v ← offsetPointer w va (toSigned w delta)
      pure (next (setReg t d v))
    | .bits _ _, .ptr _ _ (.shared ..) _ | .bits _ _, .ptr _ _ (.local _) _
    | .bits _ _, .ptr _ _ .const _ =>
      let delta ← readBits L g t w a
      let v ← offsetPointer w vb (toSigned w delta)
      pure (next (setReg t d v))
    | _, _ =>
      let x ← readBits L g t w a; let y ← readBits L g t w b
      pure (next (setReg t d (.bits w (truncBits w (x + y)))))
  | .sub, _, _, [some d], [a, b] => do
    let va ← readValue L g t w a
    match va with
    | .ptr _ _ (.shared ..) _ | .ptr _ _ (.local _) _ | .ptr _ _ .const _ =>
      let delta ← readBits L g t w b
      let v ← offsetPointer w va (-(toSigned w delta))
      pure (next (setReg t d v))
    | _ =>
      let x ← readBits L g t w a; let y ← readBits L g t w b
      pure (next (setReg t d (.bits w (truncBits w (x - y)))))
  | .mul .lo, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b
    pure (next (setReg t d (.bits w (truncBits w (x * y)))))
  | .mad .lo, _, _, [some d], [a, b, c] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b; let z ← readBits L g t w c
    pure (next (setReg t d (.bits w (truncBits w (x * y + z)))))
  | .mul .hi, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b
    let p : Int := if signed then toSigned w x * toSigned w y else x.toNat * y.toNat
    pure (next (setReg t d (.bits w (truncBits w (BitVec.ofInt 64 (p / 2 ^ w))))))
  | .mul .wide, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b
    let r : BitVec 64 :=
      if signed then truncBits (2 * w) (BitVec.ofInt 64 (toSigned w x * toSigned w y))
      else BitVec.ofNat 64 (x.toNat * y.toNat)
    pure (next (setReg t d (.bits (2 * w) r)))
  | .min false, _, _, [some d], [a, b] | .max false, _, _, [some d], [a, b] => do
    let isMax := i.op == .max false
    let x ← readBits L g t w a; let y ← readBits L g t w b
    let first := compare (if isMax then .gt else .lt) (if signed then .s else .u) w x y
    pure (next (setReg t d (.bits w (if first then x else y))))
  | .shl, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let s ← readBits L g t 32 b
    let r := if s.toNat ≥ w then 0 else truncBits w (x <<< s.toNat)
    pure (next (setReg t d (.bits w r)))
  | .neg, _, _, [some d], [a] => do
    let x ← readBits L g t w a
    pure (next (setReg t d (.bits w (truncBits w (-x)))))
  | .and, _, _, [some d], [a, b] =>
    if w = 1 then do
      let x ← readPred L g t a; let y ← readPred L g t b
      pure (next (setReg t d (.pred (x && y))))
    else do
      let x ← readBits L g t w a; let y ← readBits L g t w b
      pure (next (setReg t d (.bits w (x &&& y))))
  | .or, _, _, [some d], [a, b] =>
    if w = 1 then do
      let x ← readPred L g t a; let y ← readPred L g t b
      pure (next (setReg t d (.pred (x || y))))
    else do
      let x ← readBits L g t w a; let y ← readBits L g t w b
      pure (next (setReg t d (.bits w (x ||| y))))
  | .xor, _, _, [some d], [a, b] =>
    if w = 1 then do
      let x ← readPred L g t a; let y ← readPred L g t b
      pure (next (setReg t d (.pred (x ^^ y))))
    else do
      let x ← readBits L g t w a; let y ← readBits L g t w b
      pure (next (setReg t d (.bits w (x ^^^ y))))
  | .not, _, _, [some d], [a] =>
    if w = 1 then do
      let x ← readPred L g t a
      pure (next (setReg t d (.pred (!x))))
    else do
      let x ← readBits L g t w a
      pure (next (setReg t d (.bits w (truncBits w (~~~x)))))
  | .shr, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let s ← readBits L g t 32 b
    if signed then
      let r := truncBits w (BitVec.ofInt 64 (toSigned w x / 2 ^ min s.toNat w))
      pure (next (setReg t d (.bits w r)))
    else pure (next (setReg t d (.bits w (if s.toNat ≥ w then 0 else x >>> s.toNat))))
  | .setp cmp none, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b
    pure (next (setReg t d (.pred (compare cmp (i.ty.kind?.getD .b) w x y))))
  | .setp cmp bop, _, _, [p, q], a :: b :: cs => do
    let x ← readBits L g t w a; let y ← readBits L g t w b
    let f ← boolCombine L g t bop cs
    let r := compare cmp (i.ty.kind?.getD .b) w x y
    pure (next (setDst (setDst t p (.pred (f r))) q (.pred (f !r))))
  | .addCarry cin cout, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b
    let s := x.toNat + y.toNat + (← carryIn t cin)
    pure (next (setCarry (setReg t d (.bits w (BitVec.ofNat 64 (s % 2 ^ w)))) cout
      (decide (2 ^ w ≤ s))))
  | .subCarry cin cout, _, _, [some d], [a, b] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b
    let s := y.toNat + (← carryIn t cin)
    pure (next (setCarry (setReg t d (.bits w (intBits w ((x.toNat : Int) - s)))) cout
      (decide (x.toNat < s))))
  | .madCarry hi cin cout, _, _, [some d], [a, b, c] => do
    let x ← readBits L g t w a; let y ← readBits L g t w b; let z ← readBits L g t w c
    let k := i.ty.kind?.getD .u
    let p := intOf k w x * intOf k w y
    let half := (intBits w (if hi then p / 2 ^ w else p)).toNat
    let s := half + z.toNat + (← carryIn t cin)
    pure (next (setCarry (setReg t d (.bits w (BitVec.ofNat 64 (s % 2 ^ w)))) cout
      (decide (2 ^ w ≤ s))))
  | .lop3 lut (some bop), _, _, [d, some p], [a, b, c, q] => do
    let x ← readBits L g t 32 a; let y ← readBits L g t 32 b; let z ← readBits L g t 32 c
    let r := lop3Bits lut.toNat x.toNat y.toNat z.toNat
    let s ← readPred L g t q
    pure (next (setReg (setDst t d (.bits 32 (BitVec.ofNat 64 r))) p
      (.pred (bop.eval (r != 0) s))))
  | _, _, _, [some d], _ => do
    let v ← intResult L g t i
    pure (next (setReg t d v))
  | _, _, _, _, _ => throw .noRule

/-! ## THREAD-NUM — numeric operand interpretation
Statement: A floating operand is read as a datum of the instruction's format: an opaque NaN of the
  format is NaN, and every other value, a payload included, is read through its bit pattern as a
  pattern of that format. A `0f` constant is its 32-bit pattern. The real-number reader of the
  assumptions takes a payload of the format as its number and rejects NaN and infinity, and a value
  of another width or without a bit pattern is a type error.

Defs: classify, FVal.finite, bitsAsFloat, bitsAsFloat_eq, valFloat, readFloat, classify_bits,
  classify_float_repr, valFloat_float, valFloat_of_classify, FVal.toValue, floatLane, unitValue,
  setResult, execFloat

Source:
- §5.2.1: "The bit-size type is compatible with any fundamental type having the same size."
- §6.1: "Operands having type different from but compatible with the instruction type are silently
    cast to the instruction type."
- §9.7.3 (add.f32x2): "fA[0] = a[0:31]; fA[1] = a[32:63];"
- §9.7.3: "Single-precision instructions return an unspecified NaN"
- §9.7.7.2: "p = BoolOp(t, c); q = BoolOp(!t, c);"
- §9.7.8.2: "p = BoolOp(t[0], c); q = BoolOp(t[1], c);"
- §9.7.7.1: "1.0f is written for floating-point destination types, and 0xffffffff is written for
    integer destination types. Otherwise, 0x00000000 is written."
- §9.7.8.1: "1.0 in target precision floating point format is written for destination type .f16 ,
    .bf16 ."
- §9.7.8.1: "} else if (dtype == .f16 || stype == .bf16) { t = (a CmpOp b) ? 1 : 0; d = BoolOp(t,
    c) ? 1.0 : 0.0; }"
- §9.7.8.1: "if (dtype == .f16x2 || stype == .bf16x2) { for (i = 0; i < 2; i++) { d[i] =
    BoolOp(t[i], c) ? 1.0 : 0.0; } }"

Direction: stricter

Applies: Floating operands of every format, and every floating instruction

Premises: The operand is an opaque NaN of the instruction's format, or a value with a bit pattern of
  the format's width.

Effect: Operand decoding and result encoding. `classify` is the only reading of floating data from
  bits (THREAD-FLOAT-FORMAT); THREAD-FLOAT and THREAD-CVT read their operands with it, so a payload
  `.float fmt x` whose number is not representable in `fmt` is read as the number its bits give
  (EXT-FLOAT-BITS), and a payload whose number is representable as that number
  (`classify_float_repr`). `valFloat`, the reader of the ideal assumptions (ASM-IDEAL) and of MMA
  and reduction elements, differs from it on a payload of the instruction's format only, which it
  reads as its number (`valFloat_float`); it reads every other value through `classify` and has no
  real for NaN and infinity (`badValue`, stricter than the ISA, which defines arithmetic on them).
  `bitsAsFloat_eq` states its reading of a value other than an opaque NaN as the finite decoder
  `FloatFmt.decode` of the value's bits. A value of another width or without a bit pattern is a type
  error. A result is written by `FVal.toValue`: a finite number or `+0` as the payload of the
  destination format, `-0`, an infinity and a NaN with a known pattern as its bits, and a NaN whose
  pattern the manual leaves unspecified as the opaque `Value.nan` (THREAD-VALUE). `execFloat` runs a
  floating instruction (THREAD-FLOAT): it reads each source at its type's width, classifies each
  lane in its format (`floatLane`), takes each lane's result from `FloatInstr.lane`, combines a
  comparison with `BoolOp` and `c` (`boolCombine`; `q` of a scalar `setp` is `BoolOp(!t, c)`, and
  `p`, `q` of a packed `setp` are the two lanes), and writes the results; `set` writes `1.0`/`0.0`
  in a floating destination and all ones/zero in an integer one (`setResult`), and a `set` with an
  integer source type compares as THREAD-INT does. Where the Semantics of §9.7.8.1 and its
  Description give different values (the Semantics tests "} else if (dtype == .f16 || stype ==
  .bf16) {" and "if (dtype == .f16x2 || stype == .bf16x2) {"), there is no rule: a `.bf16`
  destination with another source type, and an integer destination with a `.bf16` or `.bf16x2`
  source.
-/

/-- The floating datum a value denotes as format `fmt`: an opaque NaN of `fmt` is NaN with
unknown bits, and every other value is read through its bit pattern, which must have the format's
width (THREAD-FLOAT-FORMAT). This is the only reading of floating data from its bits. -/
def classify (fmt : FloatFmt) : Value → Exec FVal
  | .nan f => if f = fmt then pure (.nan none) else throw .typeMismatch
  | v => match v.bitPattern with
    | some n =>
      if v.bytes = fmt.bytes then
        match fmt.layout.decode n with
        | some x => pure x
        | none => throw .badValue
      else throw .typeMismatch
    | none => throw .typeMismatch

/-- The number of a finite datum, either zero being `0`; NaN and infinity have none
(`badValue`). -/
def FVal.finite : FVal → Exec ℝ
  | .zero _ => pure 0
  | .fin q => pure q
  | _ => throw .badValue

/-- The `fmt` number a value denotes (`classify`); NaN and infinity have none. -/
def bitsAsFloat (fmt : FloatFmt) (v : Value) : Exec ℝ := do (← classify fmt v).finite

/-- The reading of a value other than an opaque NaN, as the finite decoder of its bits. -/
theorem bitsAsFloat_eq {fmt : FloatFmt} {v : Value} (h : ∀ f, v ≠ .nan f) :
    bitsAsFloat fmt v = match v.bitPattern with
      | some n =>
        if v.bytes = fmt.bytes then
          match fmt.decode n with
          | some q => pure (q : ℝ)
          | none => throw .badValue
        else throw .typeMismatch
      | none => throw .typeMismatch := by
  have hc : classify fmt v = match v.bitPattern with
      | some n =>
        if v.bytes = fmt.bytes then
          match fmt.layout.decode n with
          | some x => pure x
          | none => throw .badValue
        else throw .typeMismatch
      | none => throw .typeMismatch := by
    cases v <;> first | exact absurd rfl (h _) | rfl
  rw [bitsAsFloat, hc]
  rcases v.bitPattern with _ | n
  · rfl
  · by_cases hb : v.bytes = fmt.bytes
    · simp only [hb, ite_true, FloatFmt.decode]
      rcases fmt.layout.decode n with _ | x
      · rfl
      · cases x <;> simp [FVal.finite, FVal.num, bind, Except.bind, pure, Except.pure, throw,
          throwThe, MonadExceptOf.throw]
    · simp [hb, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A float operand: a payload of format `fmt` is its number; every other value is read
through its bit pattern. -/
def valFloat (fmt : FloatFmt) : Value → Exec ℝ
  | .float f x => if f = fmt then pure x else bitsAsFloat fmt (.float f x)
  | v => bitsAsFloat fmt v

/-- Read operand `o` as a number of format `fmt`. -/
def readFloat (t : TState) (fmt : FloatFmt) : Opnd → Exec ℝ
  | .reg r => do valFloat fmt (← readReg t r)
  | .f32imm b => valFloat fmt (.bits 32 (BitVec.ofNat 64 b))
  | _ => throw .typeMismatch

/-- A pattern of the format's width that decodes to a datum classifies as that datum. -/
theorem classify_bits {fmt : FloatFmt} {n : Nat} {x : FVal} (hw : n < 2 ^ 64)
    (hd : fmt.layout.decode n = some x) :
    classify fmt (.bits (8 * fmt.bytes) (BitVec.ofNat 64 n)) = .ok x := by
  have hb : (Value.bits (8 * fmt.bytes) (BitVec.ofNat 64 n)).bytes = fmt.bytes := by
    simp [Value.bytes]
  have hn : (BitVec.ofNat 64 n).toNat = n := by simpa using hw
  simp [classify, Value.bitPattern, hb, hn, hd, pure, Except.pure]

/-- A payload whose number is representable in its format classifies as that number. -/
theorem classify_float_repr {fmt : FloatFmt} {x : ℝ} (h : fmt.representable x) :
    ∃ q : ℚ, (q : ℝ) = x ∧ classify fmt (.float fmt x) = .ok (FVal.ofRat q) := by
  obtain ⟨q, hq, hd⟩ := FloatFmt.decode_encode h
  exact ⟨q, hq, by simp [classify, Value.bitPattern, Value.bytes, hd, pure, Except.pure]⟩

/-- `valFloat` reads a payload of the instruction's format as its number. -/
theorem valFloat_float {fmt : FloatFmt} {x : ℝ} : valFloat fmt (.float fmt x) = .ok x := by
  simp [valFloat, pure, Except.pure]

/-- On a value that is not a payload, `valFloat` reads the finite number `classify` gives. -/
theorem valFloat_of_classify {fmt : FloatFmt} {v : Value} {x : FVal}
    (hv : ∀ f y, v ≠ .float f y) (h : classify fmt v = .ok x) :
    valFloat fmt v = x.finite := by
  have : valFloat fmt v = bitsAsFloat fmt v := by
    cases v <;> first | exact absurd rfl (hv _ _) | rfl
  rw [this, bitsAsFloat, h]
  rfl

/-- The register value of a floating result of format `fmt`: the payload of a finite number or of
`+0`, the opaque NaN for a NaN without a known pattern, and otherwise the bits of the datum
(`-0`, an infinity, a NaN with a known pattern). -/
def FVal.toValue (fmt : FloatFmt) : FVal → Value
  | .zero false => .float fmt 0
  | .zero true => .bits (8 * fmt.bytes) (BitVec.ofNat 64 fmt.layout.signPattern)
  | .fin q => .float fmt q
  | .inf neg => .bits (8 * fmt.bytes) (BitVec.ofNat 64 (fmt.layout.infPattern neg))
  | .nan none => .nan fmt
  | .nan (some n) => .bits (8 * fmt.bytes) (BitVec.ofNat 64 n)

/-! ## THREAD-SHARED-POINTER — shared addresses and peer mapping
Statement: A `.shared::cta` address is a number that names a byte of the executing CTA. A generic or
  `.shared::cluster` address is a symbolic pointer that records its target CTA, its offset and the
  CTA of the thread that produced it, and only a thread of that CTA can use it. `mapa` changes only
  the target CTA to a CTA of the same cluster, and `getctarank` gives the cluster rank of the CTA an
  address names.

Defs: readSharedAddress, execSharedAddress

Source:
- §5.1.7: "Additional sub-qualifiers ::cta or ::cluster can be specified on instructions with
    .shared state space to indicate whether the address belongs to the shared memory window of the
    executing CTA or of any CTA in the cluster respectively. The addresses in the .shared::cta
    window also fall within the .shared::cluster window."
- §5.1.7: "Variables declared in .shared state space refer to the memory addresses in the current
    CTA."
- §6.4.2: "Arrays of all types can be declared, and the identifier becomes an address constant in
    the space where the array is declared."
- §9.7.10.26 (mapa): "Destination register d will hold an address in CTA b corresponding to operand
    a"
- §9.7.10.27 (getctarank): "Write the destination register d with the rank of the CTA which contains
    the address specified in operand a ."
- §2.2.2 (cluster)
- §9.7.15.16.12
- §9.7.15.16.13
- §9.7.15.16.16
- §9.7.15.16.19
- §9.7.18.7.1: "If the address specified by addr does not fall within the address window of
    .shared::cta state space then the behavior is undefined."
- §9.7.18.7.1 (for `tcgen05.alloc` the same sentence with `dst`)

Direction: stricter

Applies: Shared addresses produced from local offsets, by THREAD-CVTA and by mapa, and read by
  cvta, mapa, getctarank and the shared-memory instructions; 32-bit or 64-bit address registers

Premises: Pointer representation matches the instruction; a symbolic pointer is read only by a
  thread of the CTA that produced it; a `.shared::cta` operand is not a `.shared::cluster` address,
  a generic operand converted to `.shared::cta` targets its own CTA, a cluster-qualified one uses a
  peer in the same cluster, and mapa's target rank is valid.

Effect: Register values keep their target and producer through moves, memory round trips and address
  conversion. Arbitrary bit inspection and manually encoded peer pointers are outside this
  representation.
  `getctarank` reads its operand as a `.shared::cluster` address (a cluster pointer or a number of
  the thread's own window) or, without `.shared::cluster`, as a generic shared pointer, and writes
  the rank of its target CTA.
  A `.shared::cta` window address means the same in every CTA: the executing CTA's byte (§5.1.7,
  §6.4.2: one address constant names each CTA's own copy of a shared variable), which is how a raw
  integer is read. The text does not say what a generic shared address or a `.shared::cluster`
  address (e.g. a mapa result) denotes when used by a thread of a CTA other than the one that
  produced it, so such a use has no rule (`noRule`); a value's meaning thus never depends on whether
  it is tagged as a pointer. The text gives the inclusion of the `.shared::cta` window in the
  `.shared::cluster` window only (§5.1.7), not the converse: a `.shared::cluster` address (a result
  of `mapa.shared::cluster` or `cvta.to.shared::cluster`) at a `.shared{::cta}` operand faults
  (`noRule`) even when it names the executing CTA. For `mbarrier.init`, `mbarrier.inval`,
  `mbarrier.arrive`, `mbarrier.test_wait`/`try_wait` and `tcgen05.alloc` the quoted sentence makes
  such a use undefined; for the other `.shared{::cta}` instructions the text gives it no meaning.
  Peer addresses are represented symbolically, not with an invented encoding of CTA-rank bits. This
  layer does not assert peer lifetime or allocation: actual accesses require separate checks.
-/

/-- Read a shared address operand of width `w` as a location in a CTA, checking that the thread
may use it. -/
def readSharedAddress (L : Launch) (g : Nat) (t : TState) (w : Nat)
    (generic cluster : Bool) (a : Opnd) : Exec Loc := do
  unless w = 32 ∨ w = 64 do throw .noRule
  let v ← readValue L g t w a
  let (cta, off) ← match v with
    | .ptr pw pg (.shared issuer cta) off => do
      unless pw = w ∧ pg = generic do throw .typeMismatch
      unless issuer = g / L.block do throw .noRule
      unless generic ∨ cluster do throw .noRule
      pure (cta, off)
    | .bits _ x =>
      if generic then throw .noRule else pure (g / L.block, truncBits w x)
    | _ => throw .typeMismatch
  unless g < L.threads ∧ cta < L.grid ∧
      L.clusterOfCta cta = L.clusterOfCta (g / L.block) ∧
      (cluster = true ∨ cta = g / L.block) do throw .badValue
  unless off.toNat < 2 ^ 32 do throw .noRule
  pure ⟨.shared, cta, off.toNat⟩

/-- The shared address instructions `mapa` and `getctarank`. -/
def execSharedAddress (L : Launch) (g : Nat) (t : TState) : AddrInstr → Exec TState
  | .mapa generic w d a rank => do
    let loc ← readSharedAddress L g t w generic true a
    let r ← readBits L g t 32 rank
    match L.mapShared (g / L.block) r.toNat loc with
    | none => throw .badValue
    | some peer =>
      pure (next (setReg t d
        (.ptr w generic (.shared (g / L.block) peer.cta) (BitVec.ofNat 64 peer.addr))))
  | .getctarank generic w d a => do
    let loc ← readSharedAddress L g t w generic true a
    pure (next (setReg t d (.bits 32 (BitVec.ofNat 64 (L.rankOfCta loc.cta)))))
  | _ => throw .noRule

/-! ## THREAD-CVTA — generic address windows: cvta and isspacep
Statement: `cvta` converts a const, parameter, global, local or shared address to a generic address
  and back, and `isspacep` says whether a generic address lies in the window of a state space. A
  generic address in the shared, parameter, local or constant window is a symbolic pointer that
  remembers the memory it maps to, and a global address is its own generic address. Converting a
  generic address that lies outside the window of the target space is a fault.

Defs: inWindow, execCvta, execCvta_global, execCvta_param, execCvta_shared

Source:
- §9.7.10.23 (cvta): "Convert a const , Kernel Function Parameters ( .param ), global , local , or
    shared address to a generic address, or vice-versa."
- §9.7.10.23 (cvta): "When converting a generic address into a const , Kernel Function Parameters (
    .param ), global , local , or shared address, the resulting address is undefined in cases where
    the generic address does not fall within the address window of the specified state space."
- §6.4.1.1: "A generic address maps to global memory unless it falls within the window for const ,
    local , or shared memory."
- §6.4.1.1: "Within each window, a generic address maps to an address in the underlying state space
    by subtracting the window base from the generic address."
- §5.1.5: "The local state space ( .local ) is private memory for each thread to keep its own data."
- §5.1.6.1 (addressable kernel parameters)
- §9.7.10.22 (isspacep): "Write predicate register p with 1 if generic address a falls within the
    specified state space window and with 0 otherwise."
- §9.7.10.22 (isspacep): "isspacep.global returns 1 for Kernel Function Parameters as .param window
    is contained within the .global window."
- §9.7.10.22 (isspacep): "ispacep.shared::cluster will return 1 for every shared memory address that
    is accessible to the threads in the cluster, whereas ispacep.shared::cta will return 1 only if
    the address is of a variable declared in the executing CTA."
- EXT-CVTA (the global window)

Direction: stricter

Applies: `cvta{.to}.global.u64`, `cvta{.to}` of the parameter, shared, local and constant spaces of
  32 or 64 bits, and `isspacep` (`AddrInstr.rule`); through THREAD-ADDR the generic accesses at the
  pointers these give, and through THREAD-POINTER-OFFSET their offsets

Premises: The source of a conversion to a generic address is an address of the state space: a number
  for the global, local and constant spaces, a parameter pointer of the instruction width for the
  parameter space, and a shared address that THREAD-SHARED-POINTER accepts for the shared spaces.
  The source of a conversion from a generic address is a generic pointer of the instruction width
  into the window of the target space, for local memory one of the thread itself, or a number for
  the global space. The operand of `isspacep` is a register.

Effect: Local register update. A generic pointer is a `.ptr` value with `generic = true`, and a
  state-space pointer one with `generic = false` (THREAD-VALUE). The window bases are not modeled:
  subtracting a base gives back the state-space address (§6.4.1.1), so a conversion changes only
  the representation and keeps the memory and the offset that the pointer names.
  Global space: `cvta.global` and `cvta.to.global` are the identity on 64-bit numbers (EXT-CVTA).
  Parameter space: `cvta.param` turns the parameter-space pointer of a kernel parameter object into
  its generic pointer, and `cvta.to.param` turns the generic pointer back. The conversion keeps the
  identity of the parameter object and loads none of its contents; any other source is a fault
  (`badValue`).
  Shared spaces: `cvta.shared{::cta}` and `cvta.shared::cluster` read their source by
  THREAD-SHARED-POINTER and give a generic shared pointer of the thread's CTA to the same location.
  `cvta.to.shared::cluster` gives the `.shared::cluster` pointer of the location, and
  `cvta.to.shared{::cta}` the number of its `.shared::cta` address, which must lie in the thread's
  CTA. The generic and state-space representations stay distinct.
  Local and constant spaces: `cvta.local` of the local address `x` of thread `g` is the generic
  pointer to byte `x` of the local memory of `g`, and `cvta.const` of the constant address `x` is
  the generic pointer to byte `x` of the constant memory. `cvta.to.local` of a generic local
  pointer of the thread itself is its offset, and `cvta.to.const` of a generic constant pointer is
  its offset. The text makes the result undefined for a generic address outside the window, so
  every other source value is a fault (`badValue`); a generic number is a global address
  (EXT-CVTA), so it is outside both windows. A generic local pointer of another thread has no rule:
  local memory is private to each thread and the text does not say which bytes another thread
  reaches through that address.
  `isspacep` (`inWindow`) answers for a generic shared pointer of the thread's CTA (in the
  `.shared::cluster` window; in the `.shared::cta` window when it targets the thread's CTA; outside
  the global and parameter windows, since a shared window address does not map to global memory
  and the parameter window lies in the global window) and for a generic parameter pointer (in the
  parameter and global windows, outside the shared, local and constant ones). It also answers for a
  generic local pointer of the thread (in the local window) and a generic constant pointer (in the
  constant window). The const, local and shared windows do not overlap: §6.4.1.1 maps a generic
  address to global memory unless it falls within one of them and maps an address within a window
  to an address of that window's state space, so a generic address that names a location of one of
  these spaces lies in no other of the three windows. A generic shared, local or constant pointer
  is therefore outside the other two of these windows, and `isspacep` answers 0 for them
  (§9.7.10.22: "with 0 otherwise"). A generic number may lie in any window, and a generic local
  pointer of another thread names local memory that the querying thread cannot address, so those
  queries have no rule (stricter).

### EXT-CVTA — generic and global addresses

Statement: The model takes the generic address of a global allocation to be its global address. Then
  `cvta.to.global` is the identity, and a generic pointer that the host passes can be used directly
  as a global address. The PTX ISA says that such a generic address maps to global memory and does
  not say that its value equals the global address.
  The generic address of a global allocation is its global address: `cvta.to.global` is the
  identity on it, and a kernel may use a generic pointer that the host passes (a device pointer)
  directly as a global address, in `ld.global`/`st.global` and as the global base of a tensor
  map. The generic address lies outside the const, local and shared windows (the model checks
  neither). A 64-bit number used as a generic load or store address is therefore a global address
  (THREAD-ADDR); a number in one of the windows names no allocated global byte of `mem0`, so the
  access is an access to unallocated memory in the model.

Evidence: PTX ISA §6.4.1.1 ("A generic address maps to global memory unless it falls within the
  window for const , local , or shared memory"; within a window the window base is subtracted);
  §9.7.10.23 (cvta) defines the instruction. Whether an address of a kernel's global allocation
  avoids the windows is a property of the launch, not checked.

Effect: §6.4.1.1 states that such a generic address maps to global memory, not that its value equals
  the global address; if the values differ, every global access through a host pointer reaches
  another location than the model's. Disclosed by every kernel whose statement names
  `AddrInstr.cvta`, `Space.global`, `Op.mem`, `Op.cpTensor`, `Op.cpTensorStore` or
  `Op.prefetchTensor`: AddOne, BlockSum, CopyDynamic, CopyLdg, FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum, TcGemm, TmaCopy.
-/

/-- Whether the generic address `v` falls in the window of state space `sp` (`isspacep`): a
generic shared pointer of the thread's CTA lies in the `.shared::cluster` window, in the
`.shared::cta` window when it targets the thread's CTA, and outside the global, parameter, local
and constant windows; a generic parameter pointer lies in the parameter and global windows and
outside the others; a generic local pointer of the thread lies in the local window and outside the
others; a generic constant pointer lies in the constant window and outside the others. Any other
value or space has no rule. -/
def inWindow (L : Launch) (g : Nat) (sp : StateSpace) (v : Value) : Exec Bool :=
  match v, sp with
  | .ptr _ true (.shared issuer cta) _, sp =>
    if issuer = g / L.block ∧ g < L.threads ∧ cta < L.grid ∧
        L.clusterOfCta cta = L.clusterOfCta (g / L.block) then
      match sp with
      | .shared .cluster => pure true
      | .shared .cta => pure (cta == g / L.block)
      | .global | .param | .local | .const => pure false
      | .paramFunc => throw .noRule
    else throw .noRule
  | .ptr _ true (.param _) _, .param | .ptr _ true (.param _) _, .global => pure true
  | .ptr _ true (.param _) _, _ => pure false
  | .ptr _ true (.local owner) _, sp =>
    if owner = g then match sp with
      | .local => pure true
      | .global | .param | .shared _ | .const => pure false
      | .paramFunc => throw .noRule
    else throw .noRule
  | .ptr _ true .const _, .const => pure true
  | .ptr _ true .const _, .global | .ptr _ true .const _, .param
  | .ptr _ true .const _, .shared _ | .ptr _ true .const _, .local => pure false
  | _, _ => throw .noRule

/-- `cvta` between a state space and the generic address space, window by window, and `isspacep`
(THREAD-CVTA). -/
def execCvta (L : Launch) (g : Nat) (t : TState) : AddrInstr → Exec TState
  | .cvta _ .global 64 d a => do
    let x ← readBits L g t 64 a
    pure (next (setReg t d (.bits 64 x)))
  | .cvta toParam .param w d a => do
    let .ptr pw generic (.param name) off ← readValue L g t w a | throw .badValue
    unless (w = 32 ∨ w = 64) ∧ pw = w ∧ generic = toParam do throw .badValue
    pure (next (setReg t d (.ptr w (!toParam) (.param name) off)))
  | .cvta toShared (.shared win) w d a => do
    let cluster := win == .cluster
    let loc ← readSharedAddress L g t w toShared cluster a
    if toShared && !cluster then pure (next (setReg t d (.bits w (BitVec.ofNat 64 loc.addr))))
    else pure (next (setReg t d
      (.ptr w (!toShared) (.shared (g / L.block) loc.cta) (BitVec.ofNat 64 loc.addr))))
  | .cvta false .local w d a => do
    unless w = 32 ∨ w = 64 do throw .noRule
    let x ← readBits L g t w a
    pure (next (setReg t d (.ptr w true (.local g) x)))
  | .cvta false .const w d a => do
    unless w = 32 ∨ w = 64 do throw .noRule
    let x ← readBits L g t w a
    pure (next (setReg t d (.ptr w true .const x)))
  | .cvta true .local w d a => do
    match ← readValue L g t w a with
    | .ptr pw true (.local owner) off =>
      unless pw = w do throw .badValue
      unless owner = g do throw .noRule
      pure (next (setReg t d (.bits w (truncBits w off))))
    | _ => throw .badValue
  | .cvta true .const w d a => do
    match ← readValue L g t w a with
    | .ptr pw true .const off =>
      unless pw = w do throw .badValue
      pure (next (setReg t d (.bits w (truncBits w off))))
    | _ => throw .badValue
  | .isspacep sp p a => do
    let v ← match a with
      | .reg r => readReg t r
      | _ => throw .noRule
    let b ← inWindow L g sp v
    pure (next (setReg t p (.pred b)))
  | _ => throw .noRule

/-- `cvta.global` and `cvta.to.global` copy the 64-bit number, as the data-movement rule did
before the windows had one rule. -/
theorem execCvta_global {L : Launch} {g : Nat} {t : TState} {b : Bool} {d : Nat} {a : Opnd} :
    execCvta L g t (.cvta b .global 64 d a) =
      (do let x ← readBits L g t 64 a; pure (next (setReg t d (.bits 64 x)))) := by
  cases b <;> rfl

/-- The parameter-space conversion, as the parameter-pointer rule gave it before the windows had
one rule. -/
theorem execCvta_param {L : Launch} {g : Nat} {t : TState} {toParam : Bool} {w d : Nat}
    {a : Opnd} :
    execCvta L g t (.cvta toParam .param w d a) = (do
      let .ptr pw generic (.param name) off ← readValue L g t w a | throw .badValue
      unless (w = 32 ∨ w = 64) ∧ pw = w ∧ generic = toParam do throw .badValue
      pure (next (setReg t d (.ptr w (!toParam) (.param name) off)))) := by
  cases toParam <;> rfl

/-- The shared-window conversion, as the shared-pointer rule gave it before the windows had one
rule. -/
theorem execCvta_shared {L : Launch} {g : Nat} {t : TState} {toShared : Bool}
    {win : SharedWindow} {w d : Nat} {a : Opnd} :
    execCvta L g t (.cvta toShared (.shared win) w d a) = (do
      let cluster := win == .cluster
      let loc ← readSharedAddress L g t w toShared cluster a
      if toShared && !cluster then pure (next (setReg t d (.bits w (BitVec.ofNat 64 loc.addr))))
      else pure (next (setReg t d
        (.ptr w (!toShared) (.shared (g / L.block) loc.cta) (BitVec.ofNat 64 loc.addr))))) := by
  cases toShared <;> rfl

/-! ## THREAD-PREFETCH — cache prefetch and eviction priority
Statement: `prefetch` and `prefetchu` without `.valid_addr` and `applypriority.global` change
  neither registers nor memory, so the thread only moves to the next instruction. `applypriority`
  at an address that is not aligned to 128 bytes is undefined.

Defs: addrValue, execPrefetch

Source:
- §9.7.10.16: "The prefetch instruction brings the cache line containing the specified address in
    global or local memory state space into the specified cache level."
- §9.7.10.16: "A prefetch to a shared memory location performs no operation."
- §9.7.10.17: "The applypriority instruction applies the cache eviction priority specified by the
    .level::eviction_priority qualifier to the address range [a..a+size) in the specified cache
    level."
- §9.7.10.17: "a must be aligned to 128 bytes."

Direction: equal

Applies: The instructions whose rule is THREAD-PREFETCH (`AddrInstr.rule`)

Premises: An `applypriority` address is a 64-bit integer or an absolute address.

Effect: Local step to the next instruction. The manual states undefined behaviour for
  `prefetch.valid_addr` when the location is not valid for the access and for a generic
  `prefetch.valid_addr` or `applypriority` whose address is outside the global window; these forms
  need a check of the memory at launch and have no rule. A prefetch states no undefined behaviour
  for any other address, so it does not read its address register.
-/

/-- The integer address of an `applypriority` operand: a 64-bit register or an absolute address,
plus the offset. -/
def addrValue (L : Launch) (g : Nat) (t : TState) (a : Addr) : Exec Int :=
  match a.base with
  | .reg r 64 => (fun x => (x.toNat : Int) + a.off) <$> readBits L g t 64 (.reg r)
  | .imm x => pure (x + a.off)
  | _ => throw .noRule

/-- A prefetch or `applypriority.global`: the next instruction, after the alignment check of
`applypriority`. -/
def execPrefetch (L : Launch) (g : Nat) (t : TState) : AddrInstr → Exec TState
  | .prefetch _ _ false _ => pure (next t)
  | .applypriority true a =>
    addrValue L g t a >>= fun x => if x % 128 = 0 then pure (next t) else throw .misaligned
  | _ => throw .noRule

/-! ## THREAD-CACHE-POLICY — cache eviction policies
Statement: `createpolicy` writes an opaque cache eviction policy to its destination register. A
  range-based policy needs a global address and a primary size at most the total size, and a
  fraction-based policy a fraction in `(0.0, 1.0]`; any other operand is undefined. A policy has
  no bit pattern, so an instruction that reads it as an integer has no rule.

Defs: execPolicy

Source:
- §9.7.10.21: "The createpolicy instruction creates a cache eviction policy for the specified cache
    level in an opaque 64-bit register specified by the destination operand cache_policy ."
- §9.7.10.21: "The value of primary-size must be less than or equal to the value of total-size ."
- §9.7.10.21: "If the specified address does not fall within the address window of .global state
    space then the behavior is undefined."
- §9.7.10.21: "The valid range of values for the operand fraction is (0.0,.., 1.0] ."
- §9.7.10.21: "If the operand fraction is not specified, it defaults to 1.0."
- §9.7.10.21: "The source operand access-property is a 64-bit opaque register."
- §9.7.10.8: "cache_policy is a hint to the cache subsystem and may not always be respected. It is
    treated as a performance hint only, and does not change the memory consistency behavior of the
    program."

Direction: stricter

Applies: `createpolicy` (`MiscInstr.rule`, PROG-ISA-MISC)

Premises: The operands are defined values of their types; the address of a range is a global
  address in a register or an absolute address.

Effect: Local register update; a primary size above the total size or a fraction outside
  `(0.0, 1.0]` is `badValue`.
  The policy is the value `Value.policy` (THREAD-VALUE), which records nothing: the manual describes
  its effect only as a performance hint, so no rule reads what it contains, and the instructions
  with `.level::cache_hint` accept it as their `cache_policy` operand. The address of a range-based
  policy is read as an integer (`addrValue`): a generic number is a global address (EXT-CVTA), and a
  shared, local, constant or parameter pointer has no integer reading and has no rule. The model
  rejects a generic parameter pointer although the `.param` window lies in the `.global` window,
  which is one reason the direction is stricter. `total-size` is a 32-bit operand, so it is always
  within the maximum of 4GB. A fraction is read as an `.f32` number (THREAD-NUM). The access
  property of `createpolicy.cvt` comes from the CUDA API, and the model requires only that it is a
  defined 64-bit value.
-/

/-! ## THREAD-NO-EFFECT — sleeping, performance monitor events and grid dependency control
Statement: `nanosleep`, `pmevent` and `griddepcontrol` change no state of the model and continue
  with the next instruction; `nanosleep` reads its delay operand. `griddepcontrol` has no effect
  because the launch has no prerequisite or dependent grid (EXT-GRIDDEP-SINGLE).

Defs: execMisc

Source:
- §9.7.21.2: "Suspends the thread for a sleep duration approximately close to the delay t ,
    specified in nanoseconds."
- §9.7.21.2: "The sleep duration is approximated, but guaranteed to be in the interval [0, 2*t] ."
- §9.7.21.3: "Triggers one or more of a fixed number of performance monitor events, with event index
    or mask specified by immediate operand a ."
- §9.7.21.3: "The relationship between events and counters is programmed via API calls from the
    host."
- §9.7.15.14 (griddepcontrol, as quoted in EXT-GRIDDEP-SINGLE)
- EXT-GRIDDEP-SINGLE

Direction: equal

Applies: `nanosleep`, `pmevent` and `griddepcontrol` (`MiscInstr.rule`, PROG-ISA-MISC)

Premises: The delay operand of `nanosleep` is a defined 32-bit value.

Effect: Local step to the next instruction. The model has no time, so a delay of `nanosleep` is a
  step of the thread that changes nothing; the other threads may take any number of steps meanwhile,
  as they may at every step. The performance counters that `pmevent` increments are read only
  through the `%pm` special registers, which have no rule (THREAD-SREG), so no instruction with a
  rule observes them.

### EXT-GRIDDEP-SINGLE — grid dependency control in a launch of one grid

Statement: The model takes the kernel to run as a single grid with no prerequisite grid and no
  dependent grid. Then `griddepcontrol.wait` returns at once and `griddepcontrol.launch_dependents`
  has no effect on the kernel's execution: both are local steps to the next instruction
  (`execMisc`).

Source:
- §9.7.15.14: ".launch_dependents modifier signals that specific dependents the runtime system
    designated to react to this instruction can be scheduled as soon as all other CTAs in the grid
    issue the same instruction or have completed."
- §9.7.15.14: ".wait modifier causes the executing thread to wait until all prerequisite grids in
    flight have completed and all the memory operations from the prerequisite grids are performed
    and made visible to the current grid."
- §9.7.15.14: "If the prerequisite grid is using griddepcontrol.launch_dependents , then the
    dependent grid must use griddepcontrol.wait to ensure correct functional execution."

Why it is not spec text: the instruction's behaviour depends on the grids the runtime designates
  as prerequisites and dependents, which are outside the PTX program. The text determines the result
  only once the launch is known: with no prerequisite grid in flight there is nothing to wait for,
  and with no designated dependent nothing is scheduled. That the launch has neither is the
  obligation of EXT-LAUNCH (no PDL-dependent launch, no conflicting outside access), not a fact the
  model checks.

Direction: reading

Effect: A kernel launched as a dependent grid, or whose dependents run concurrently through
  programmatic dependent launch, is outside the theorem: its `griddepcontrol.wait` may block and
  order memory operations of other grids, and the dependents may access memory concurrently.
  Disclosed by every kernel whose statement names `MiscInstr.gridDep`: FlashMlaSparseDecodeH64,
  InklingRelDecode.
-/

/-- `createpolicy` (THREAD-CACHE-POLICY): the opaque policy, after the operand checks. -/
def execPolicy (L : Launch) (g : Nat) (t : TState) (d : Nat) : PolicyKind → Exec TState
  | .range _ a primary total => do
    let _ ← addrValue L g t a
    let p ← readBits L g t 32 primary
    let n ← readBits L g t 32 total
    unless p.toNat ≤ n.toNat do throw .badValue
    pure (next (setReg t d .policy))
  | .fraction f => do
    if let some o := f then
      let x ← readFloat t .f32 o
      unless 0 < x ∧ x ≤ 1 do throw .badValue
    pure (next (setReg t d .policy))
  | .cvt a => do
    let _ ← readBits L g t 64 a
    pure (next (setReg t d .policy))

/-- A miscellaneous instruction: `createpolicy` (THREAD-CACHE-POLICY), `nanosleep` and `pmevent`
(THREAD-NO-EFFECT). -/
def execMisc (L : Launch) (g : Nat) (t : TState) : MiscInstr → Exec TState
  | .createPolicy d k => execPolicy L g t d k
  | .nanosleep o => do
    let _ ← readBits L g t 32 o
    pure (next t)
  | .pmevent .. | .gridDep _ => pure (next t)

/-! ## THREAD-MOVE — data movement
Statement: `mov`, `selp` and `slct` copy a value unchanged, and packing and unpacking keep the
  elements with the lowest first. `ld.param` reads a scalar kernel parameter, or the bytes that the
  host passed in a by-value parameter object named directly or by a register, little-endian and
  sign- or zero-extended into the destination register, and a byte the launch does not supply is a
  fault.

Defs: execMove, joinValue, splitValue, f32NonNeg, paramObjectBits, MemExt.extendBits,
  MemExt.extendBits_same, signExtendRegs, paramObjectOf, paramElem, paramElem_of_ne,
  loadParamObject

Source:
- §9.7.10.3 (mov): "Write register d with the value of a"
- §9.7.10.4 (mov pack/unpack): "pack four 16-bit elements into .b64 d = a.x | (a.y << 16) | (a.z <<
    32) | (a.w << 48)"
- §9.7.10.4 (mov pack/unpack): "unpack 32-bit elements from .b128 { d.x, d.y, d.z, d.w } = {
    a[0..31], a[32..63], a[64..95], a[96..127] }"
- §9.7.10.4 (mov pack/unpack): "the sink symbol '_' may be used for one or more elements"
- §9.7.7.3 (selp)
- §9.7.7.4 (slct): "If c >= 0, a is stored in d , otherwise b is stored in d ."
- §9.7.7.4 (slct): "The selected input is copied to the output without modification."
- §9.7.7.4 (slct): "For .f32 comparisons, negative zero equals zero."
- §9.7.7.4 (slct): "If operand c is NaN , the comparison is ordered and operand b is selected."
- §9.7.7.4 (slct): "slct.ftz.dtype.f32 flushes subnormal values of operand c to sign-preserving
    zero, and operand a is selected."
- §5.1.6.1 (kernel parameters): "These parameters are addressable, read-only variables declared in
    the .param state space. Values passed from the host to the kernel are accessed through these
    parameter variables using ld.param instructions."
- §9.7.10.8 (ld): "d = *(&a+immOff) // variable-plus-offset"
- §9.7.10.8 (ld): "A destination register wider than the specified type may be used. The value
    loaded is sign-extended to the destination register width for signed integers, and is
    zero-extended to the destination register width for unsigned and bit-size types."
- §9.7.10.8 (ld): "For ld.param::entry instruction, operand a must be a kernel parameter address,
    otherwise behavior is undefined."
- EXT-ENDIAN (byte order of a multi-byte element)
- EXT-VECTOR-ELEM (element `j` of a vector)

Direction: reading

Applies: The instructions whose rule is THREAD-MOVE: `mov` and its pack and unpack forms
  (`MoveInstr.rule`), `selp` and `slct` (`IntInstr.rule`) and `ld.param` (`MemAccess.rule`)

Premises: Operands satisfy the relevant type checks.

Effect: Local evaluation. `ld.param` of a scalar parameter reads the launch parameter. `ld.param` of
  a by-value parameter object reads the bytes the host passed (`Launch.paramBytes`): element `j` of
  an access of `n`-byte elements at byte `offset` is bytes `offset + j n` to `offset + (j + 1) n -
  1` (EXT-VECTOR-ELEM), assembled little-endian (EXT-ENDIAN), and is put into register `j`,
  sign-extended for a `.s` type and zero-extended otherwise when the register is wider
  (`MemExt.extendBits`); a byte the launch does not supply faults (`badParam`). A `.b128` element is
  two 64-bit halves, low half first, the value a 16-byte load from memory gives (`paramElem`,
  THREAD-BYTES). A register address `[r+off]` must hold the parameter-space address of a by-value
  parameter object (a `.ptr` to it in its state-space representation at offset 0), and the access
  must lie inside the object and be aligned to its size (`paramObjectOf`); any other value is not a
  kernel parameter address, which the text makes undefined (`badParam`). A scalar parameter through
  a register has no rule, since the launch gives its bits and not its width. `mov` copies a value
  unchanged, so its bit pattern (THREAD-BITS) is unchanged. A scalar `.pred` move writes its source
  read as a predicate (`readPred`). A scalar `mov.b64` of a declared local symbol writes its
  numeric state-space address (EXT-LOCAL-CONST-LAYOUT). Packing and unpacking keep the halves,
  low half first, and four elements are two halves of two halves; a sink `_` destination of an
  unpack is not written. `slct` copies `a` when `c ≥ 0` and `b` otherwise; an `.f32` `c` is read
  through its bit pattern, so `-0` selects `a` and a NaN or a negative subnormal selects `b`; with
  `.ftz` every subnormal `c` is flushed to a zero and selects `a`. Two integer halves of at most 32
  bits pack into one integer of twice the width (§9.7.10.4: the halves are concatenated). Packed
  floats and opaque payloads keep their components; the bit pattern of such a pair is the same
  concatenation, so later integer instructions read it. Unpacking a payload gives byte slices of it,
  whose bit patterns are the corresponding bits.
-/

/-- Concatenate low and high halves, recovering an unchanged opaque payload when
both slices cover that same payload exactly. Other pairs retain their actual bytes. -/
def joinValue (lo hi : Value) : Value :=
  match lo, hi with
  | .slice whole 0 n, .slice whole' off m =>
    if whole = whole' ∧ off = n ∧ whole.bytes = n + m then whole else .pair lo hi
  | .bits w x, .bits w' y =>
    if w = w' ∧ 2 * w ≤ 64 then .bits (2 * w) (x ||| (y <<< w)) else .pair lo hi
  | _, _ => .pair lo hi

/-- Extract halves without inventing a binary encoding for opaque payloads.
Raw integer halves use their actual bits; packed values retain their components. -/
def splitValue (w : Nat) (v : Value) : Value × Value :=
  match v with
  | .pair lo hi => (lo, hi)
  | .bits _ x =>
    (.bits (w / 2) (truncBits (w / 2) x),
      .bits (w / 2) (truncBits (w / 2) (BitVec.ofNat 64 (x.toNat / 2 ^ (w / 2)))))
  | _ => (.slice v 0 (w / 16), .slice v (w / 16) (w / 16))

/-- Whether the `.f32` bit pattern `n` is a number `≥ 0` (§9.7.7.4): `-0` is, a NaN is not, and
with `.ftz` a subnormal is flushed to zero, which is. -/
def f32NonNeg (ftz : Bool) (n : Nat) : Bool :=
  let mag := n % 2 ^ 31
  mag ≤ 0x7F800000 ∧ (n < 2 ^ 31 ∨ mag = 0 ∨ (ftz ∧ mag < 0x00800000))

/-- The little-endian value of `n` bytes of parameter object `name` from byte `off`. -/
def paramObjectBits (L : Launch) (name : String) (off : Nat) : Nat → Exec Nat
  | 0 => pure 0
  | n + 1 => do
    let some b := L.paramBytes name off | throw .badParam
    let rest ← paramObjectBits L name (off + 1) n
    pure (b.toNat + 256 * rest)

/-- A `w`-bit integer `x` in a destination register of extension `ext` (§9.7.10.8): its own width,
zero-extended, or sign-extended. -/
def MemExt.extendBits (ext : MemExt) (w : Nat) (x : BitVec 64) : Value :=
  match ext with
  | .same => .bits w (truncBits w x)
  | .zero dw => .bits dw (truncBits w x)
  | .sign dw => .bits dw (truncBits dw (BitVec.ofInt 64 (toSigned w x)))

@[simp] theorem MemExt.extendBits_same {w : Nat} {x : BitVec 64} :
    MemExt.same.extendBits w x = .bits w (truncBits w x) := rfl

/-- Sign-extend the `w`-bit integers in registers `ds` to `dw` bits. -/
def signExtendRegs (w dw : Nat) (t : TState) : List Nat → TState
  | [] => t
  | d :: ds => signExtendRegs w dw (match t.regs d with
    | some (.bits _ x) => setReg t d ((MemExt.sign dw).extendBits w x)
    | _ => t) ds

/-- The by-value parameter object a register names for `ld.param` (§9.7.10.8: "operand a must be
a kernel parameter address, otherwise behavior is undefined"): a parameter-space pointer to a
parameter object that the launch passes, with an access of `n` bytes at `off` inside it and
aligned to its size. -/
def paramObjectOf (L : Launch) (t : TState) (r : Nat) (off : Int) (n : Nat) :
    Exec String := do
  let .ptr _ false (.param p) o ← readReg t r | throw .badParam
  unless o = 0 do throw .badParam
  let some (decl, _) := L.paramObjects p | throw .noRule
  unless 0 ≤ off ∧ off.toNat + n ≤ decl.bytes do throw .badParam
  unless 0 < n ∧ off.toNat % n = 0 ∧ decl.alignment % n = 0 do throw .misaligned
  pure p

/-- A loaded `w`-bit parameter element with little-endian value `x` in a `dw`-bit register. A
128-bit element is two 64-bit halves, low half first, as a 16-byte load from memory gives it
(`rebuildBits`). A narrower element is the bit vector of the register width, zero-extended. -/
def paramElem (w dw x : Nat) : Value :=
  if w = 128 then .pair (.bits 64 (BitVec.ofNat 64 x)) (.bits 64 (BitVec.ofNat 64 (x / 2 ^ 64)))
  else .bits dw (BitVec.ofNat 64 x)

/-- An element of at most 64 bits is the zero-extended bit vector, as before 128-bit elements
had a rule. -/
theorem paramElem_of_ne {w dw x : Nat} (h : w ≠ 128) :
    paramElem w dw x = .bits dw (BitVec.ofNat 64 x) := by simp [paramElem, h]

/-- Load consecutive `w`-bit elements of parameter object `p`, from byte `off`, into the
`dw`-bit registers `ds`, one element per register in order. -/
def loadParamObject (L : Launch) (w dw : Nat) (p : String) (t : TState) :
    Nat → List Nat → Exec TState
  | _, [] => pure t
  | off, d :: ds => do
    let x ← paramObjectBits L p off (w / 8)
    loadParamObject L w dw p (setReg t d (paramElem w dw x)) (off + w / 8) ds

/-- Data movement: parameters, moves, packing, `selp` and `slct`. -/
def execMove (L : Launch) (g : Nat) (t : TState) : Op → Exec TState
  | .int i => match i.op, i.dsts, i.srcs with
    | .selp, [some d], [a, b, .reg p] => do
      let w := i.ty.width
      let .pred pick ← readReg t p | throw .typeMismatch
      let v ← readValue L g t w (if pick then a else b)
      unless v.bytes = w / 8 do throw .typeMismatch
      pure (next (setReg t d v))
    | .slct ct ftz, [some d], [a, b, c] => do
      let w := i.ty.width
      let x ← readBits L g t 32 c
      let pick := match ct with
        | .float .f32 => f32NonNeg ftz x.toNat
        | _ => decide (toSigned 32 x ≥ 0)
      let v ← readValue L g t w (if pick then a else b)
      unless v.bytes = w / 8 do throw .typeMismatch
      pure (next (setReg t d v))
    | _, _, _ => throw .noRule
  | .mem a => match a.addr.base, a.regs with
    | .param p false, [d] =>
      let w := a.elem.width
      match L.params p with
      | some x => pure (next (setReg t d (a.ext.extendBits w x)))
      | none => throw .badParam
    | .param p true, ds =>
      let w := a.elem.width
      match a.ext with
      | .sign dw => (fun u => next (signExtendRegs w dw u ds)) <$>
        loadParamObject L w w p t a.addr.off.toNat ds
      | .zero dw => next <$> loadParamObject L w dw p t a.addr.off.toNat ds
      | .same => next <$> loadParamObject L w w p t a.addr.off.toNat ds
    | .reg r _, ds => do
      let w := a.elem.width
      let p ← paramObjectOf L t r a.addr.off (w / 8 * a.vec)
      match a.ext with
      | .sign dw => (fun u => next (signExtendRegs w dw u ds)) <$>
        loadParamObject L w w p t a.addr.off.toNat ds
      | .zero dw => next <$> loadParamObject L w dw p t a.addr.off.toNat ds
      | .same => next <$> loadParamObject L w w p t a.addr.off.toNat ds
    | _, _ => throw .noRule
  | .move m => match m.kind, m.dsts, m.srcs with
    | .scalar, [some d], [a] => do
      let w := m.ty.width
      if m.ty = .pred then
        pure (next (setReg t d (.pred (← readPred L g t a))))
      else
        let v ← readValue L g t w a
        unless v.bytes = w / 8 do throw .typeMismatch
        pure (next (setReg t d v))
    | .pack, [some d], [a, b] => do
      let w := m.ty.width
      let x ← readValue L g t (w / 2) a; let y ← readValue L g t (w / 2) b
      unless x.bytes = w / 16 ∧ y.bytes = w / 16 do throw .typeMismatch
      pure (next (setReg t d (joinValue x y)))
    | .unpack, [some lo, some hi], [a] => do
      let w := m.ty.width
      let v ← readValue L g t w a
      unless v.bytes = w / 8 do throw .typeMismatch
      let (x, y) := splitValue w v
      unless x.bytes = w / 16 ∧ y.bytes = w / 16 do throw .typeMismatch
      pure (next (setReg (setReg t lo x) hi y))
    | .pack, [some d], [a, b, c, e] => do
      let w := m.ty.width
      let x ← readValue L g t (w / 4) a; let y ← readValue L g t (w / 4) b
      let z ← readValue L g t (w / 4) c; let u ← readValue L g t (w / 4) e
      unless x.bytes = w / 32 ∧ y.bytes = w / 32 ∧ z.bytes = w / 32 ∧ u.bytes = w / 32 do
        throw .typeMismatch
      pure (next (setReg t d (joinValue (joinValue x y) (joinValue z u))))
    | .unpack, [lo, hi], [a] => do
      let w := m.ty.width
      let v ← readValue L g t w a
      unless v.bytes = w / 8 do throw .typeMismatch
      let (x, y) := splitValue w v
      unless x.bytes = w / 16 ∧ y.bytes = w / 16 do throw .typeMismatch
      pure (next (setDst (setDst t lo x) hi y))
    | .unpack, [d0, d1, d2, d3], [a] => do
      let w := m.ty.width
      let v ← readValue L g t w a
      unless v.bytes = w / 8 do throw .typeMismatch
      let (lo, hi) := splitValue w v
      unless lo.bytes = w / 16 ∧ hi.bytes = w / 16 do throw .typeMismatch
      let (x0, x1) := splitValue (w / 2) lo
      let (x2, x3) := splitValue (w / 2) hi
      unless x0.bytes = w / 32 ∧ x1.bytes = w / 32 ∧ x2.bytes = w / 32 ∧ x3.bytes = w / 32 do
        throw .typeMismatch
      pure (next (setDst (setDst (setDst (setDst t d0 x0) d1 x1) d2 x2) d3 x3))
    | _, _, _ => throw .noRule
  | _ => throw .noRule

/-! ## THREAD-CVT — conversions
Statement: A conversion with a rule gives the result the manual defines: an integer conversion
  chops, sign-extends or zero-extends by its source type and clamps, `cvt.pack` clamps both
  sources and packs them, a floating source is read as a floating datum, and a floating
  conversion rounds the exact number, scaled by its scale factor, into the destination format and
  then applies `.ftz`, `.sat`, `.relu` and `.pzo`, with `.satfinite` saturating and NaN and
  infinity handled as the manual states. A result the manual leaves open, among them an overflow
  to `.f16`, a `-0` under `.sat` or `.relu`, and a NaN whose encoding is unstated in a format
  without a payload format, has no rule, and so has an infinite input converted from another type
  to `.f16` or `.bf16` without `.satfinite` or `.sat`: §6.5.1 speaks of numbers beyond the range
  and names no `.bf16` value (its "~131,000" for `.f16` is no datum of that format), while IEEE
  754, with which §9.7.3 makes `cvt` compliant, would keep the infinity; the model declines that
  reading, which makes the rule stricter than the text.

Defs: execCvt, cvtIntBits, cvtPackBits, lowBitsValue, lowValue, readCvtFloat, readCvtFloat_false,
  readCvtFloat_reg, cvtFloatDst, cvtFloatDst_same, CvtRnd.roundInt, CvtRnd.mode?, cvtIntOf,
  cvtIntOf_fin, reluFVal, pzoFVal, cvtFinish, satMaxNorm, cvtRound, cvtSpecial, cvtNum,
  widenElem, widenElem_fin, roundIntElem, cvtElem, cvtElem_fmt, cvtElem_ue8m0, packedElems,
  ue8m0Scale, ue8m0Scale_eq, cvtScales, scaledFlush, rsModes, cvtPack

Source:
- §6.5.1: "the u16 is zero-extended to s32 ."
- §6.5.1: "sext = sign-extend; zext = zero-extend; chop = keep only low bits that fit;"
- §6.5.1: "If the destination register is wider than the destination format, the result is extended
    to the destination register width after chopping."
- §6.5.1: "Conversions to floating-point that are beyond the range of floating-point numbers are
    represented with the maximum floating-point value (IEEE 754 Inf for f32 and f64 , and ~131,000
    for f16 )."
- §9.4.1 (Table 28): "The data are sign-extended to the destination register width for signed
    integer instruction types, and are zero-extended to the destination register width otherwise."
- §9.7.10.24: "For integer destination types, .sat limits the result to MININT..MAXINT for the size
    of the operation."
- §9.7.10.24: "For float-to-integer conversions, the result is clamped to the destination range by
    default; i.e, .sat is redundant."
- §9.7.10.24: ".rni round to nearest integer, choosing even integer if source is equidistant between
    two integers"
- §9.7.10.24: ".rzi round to nearest integer in the direction of zero .rmi round to nearest integer
    in direction of negative infinity .rpi round to nearest integer in direction of positive
    infinity"
- §9.7.10.24: "A floating-point value may be rounded to an integral value using the integer rounding
    modifiers (see Integer Notes)."
- §9.7.10.24: "The result is an integral value, stored in floating-point format."
- §9.7.10.24: "Floating-point rounding is required for float-to-float conversions that result in
    loss of precision, and for integer-to-float conversions."
- §9.7.10.24: ".rn rounding to nearest, with ties to even .rna rounding to nearest, with ties away
    from zero .rz rounding toward zero .rm rounding toward negative infinity .rp rounding toward
    positive infinity"
- §9.7.10.24: "Operation’s result is rounded in the direction toward zero or away from zero based on
    the carry out of the integer addition of the supplied random bits ( rbits ) to the truncated off
    (discarded) bits of mantissa from the input."
- §9.7.10.24: "When converting to .f16x2 , two 16-bit values are provided from rbits where 13 LSBs
    from upper 16-bits are used as random bits for operand a with 3 MSBs are 0 and 13 LSBs from
    lower 16-bits are used as random bits for operand b with 3 MSBs are 0."
- §9.7.10.24: "When converting to .bf16x2 , two 16-bit values are provided from rbits where upper
    16-bits are used as random bits for operand a and lower 16-bits are used as random bits for
    operand b ."
- §9.7.10.24: "Modifier .ftz may be specified to flush single-precision subnormal inputs and results
    to sign-preserving zero."
- §9.7.10.24: "Modifier .ftz can only be specified when either .dtype or .atype is .f32 and applies
    only to single precision ( .f32 ) inputs and results."
- §9.7.10.24: "For cvt.ftz.dtype.f32 float-to-integer conversions and cvt.ftz.f32.f32 float-to-float
    conversions with integer rounding, subnormal inputs are flushed to sign-preserving zero."
- §9.7.10.24: "For floating-point destination types, .sat limits the result to the range [0.0, 1.0].
    NaN results are flushed to positive zero. Applies to .f16 , .f32 , and .f64 types."
- §9.7.10.24: ".relu clamps the result to 0 if negative. NaN results are converted to canonical NaN
    ."
- §9.7.10.24: "if the input value is NaN , then the result is NaN in the specified destination
    format."
- §9.7.10.24: "For .e2m1x2 , .e2m3x2 , .e3m2x2 , .e2m1x4 , .e2m3x4 , .e3m2x4 , .s2f6x2 destination
    formats NaN results are converted to positive MAX_NORM ."
- §9.7.10.24: "If the absolute value of input (ignoring sign) is greater than MAX_NORM of the
    specified destination format, then the result is sign-preserved MAX_NORM of the destination
    format and a positive MAX_NORM in .ue8m0x2 and .ue5m3x2 for which the destination sign is not
    supported."
- §9.7.10.24: "When this qualifier is specified, it enforces the generation of positive zeros only
    in the output. In other words, if the result of the conversion produces -0.0 , it will be forced
    to +0.0 ."
- §9.7.10.24: "In float-to-integer conversions, depending upon conversion types, NaN input results
    in following value: Zero if source is not .f64 and destination is not .s64 , .u64 . Otherwise 1
    << (BitWidth(dst) - 1) corresponding to the value of ( MAXINT >> 1) + 1 for unsigned type or
    MININT for signed type."
- §9.7.10.24: "For cvt.f32.bf16 , NaN input yields unspecified NaN ."
- §9.7.10.24: "The lower n bits corresponding to the instruction-type width are used in the
    conversion."
- §9.7.10.24: "The result of conversion is sign-extended to the destination register width for
    signed integers, and is zero-extended to the destination register width for unsigned, bit-size,
    and floating-point types."
- §9.7.10.24: "two inputs a and b of .f32 type are converted into .f16 or .bf16 type and the
    converted values are packed in the destination register d , such that the value converted from
    input a is stored in the upper half of d and the value converted from input b is stored in the
    lower half of d"
- §9.7.10.24: "d[31:16] = convert(a); d[15:0] = convert(b);"
- §9.7.10.24: "d[15:8] = convert(a / scale-factor[7:0]); // scale-factor if present d[7:0] =
    convert(b / scale-factor[7:0]); // scale-factor if present } else { d[15:8] = convert(a[31:16] /
    scale-factor[7:0]); // scale-factor if present d[7:0] = convert(a[15:0] / scale-factor[7:0]);"
- §9.7.10.24: "d[15:8] = convert(a / scale-factor[15:8]); d[7:0] = convert(b /
    scale-factor[7:0]);"
- §9.7.10.24: "d[7:4] = convert(a / scale-factor[7:0]); // scale-factor if present d[3:0] =
    convert(b / scale-factor[7:0]);"
- §9.7.10.24: "d[15:14] = 0; d[13:8] = convert(a / scale-factor[7:0]); // scale-factor if present
    d[7:6] = 0; d[5:0] = convert(b / scale-factor[7:0]);"
- §9.7.10.24: "d[31:16] = convert(a[15:8]) * scale-factor[15:8]; // scale-factor if present for
    .bf16x2 dest type d[15:0] = convert(a[7:0]) * scale-factor[7:0];"
- §9.7.10.24: "Each 8-bit input value in operand a is converted to .f16 / .bf16 type."
- §9.7.10.24: "the value converted from the upper 8 bits of a is stored in the upper 16 bits of d
    and the value converted from the lower 8 bits of a is stored in the lower 16 bits of d"
- §9.7.10.24: "When converting from .e2m1x2 to .f16x2 / .bf16x2 , source operand a has .b8 type.
    Each 4-bit input value in operand a is converted to .f16 / .bf16 type."
- §9.7.10.24: "the value converted from the upper 4 bits of a is stored in the upper 16 bits of d
    and the value converted from the lower 4 bits of a is stored in the lower 16 bits of d"
- §9.7.10.24: "When converting from .e2m3x2 / .e3m2x2 to .f16x2 / .bf16x2 , source operand a has
    .b16 type. Each 8-bit input value with 2 MSB bits 0 in operand a is converted to .f16 / .bf16
    type."
- §9.7.10.24: "When converting from .s2f6x2 to .bf16x2 , source operand a has .b16 type."
- §9.7.10.24: "Operand scale-factor stores two packed scaling factors of type .ue8m0 ."
- §9.7.10.24: "For down conversion, inputs are divided by scale-factor and then conversion is
    performed."
- §9.7.10.24: "Inputs are converted to destination type and then multiplied by scale-factor ."
- §9.7.10.24: "If not specified explicitly, value of scale-factor will be assumed to be 0x7f7f ,
    that is, assumed as value 1 for both input scale factors."
- §9.7.10.24: "has type .b8 when used with qualifier .scaled::n1::ue8m0 qualifier. Default value of
    scale-factor is 0x7f in this case if not specified explicitly."
- §9.7.10.24: "When qualifier .scaled::n1::ue8m0 is specified, subnormal values for inputs a and b
    are flushed to zero before conversion."
- §9.7.10.25: "The inputs a and b are converted to values of type specified by .convertType with
    saturation and the results after conversion are packed into lower bits of d ."
- §9.7.10.25: "If operand c is specified then remaining bits of d are copied from lower bits of c ."
- §9.7.10.25: "td = tb ; for (i = size; i <= 2 * size - 1; i++) { td[i] = ta[i - size]; }"
- §9.7.10.25: ".sat modifier limits the converted values to MIN(convertType) .. MAX(convertedType)
    (no overflow) if the corresponding inputs are not in the range of datatype specified as
    .convertType ."
- §5.2.4: "s2f6 value = s8 value * 2^(-6)"
- §9.7.3: "Instructions that support rounding modifiers are IEEE-754 compliant."
- THREAD-FLOAT-ROUND
- EXT-UE8M0
- EXT-NARROW-FLOAT

Direction: stricter

Applies: The conversions whose rule is THREAD-CVT (`CvtInstr.rule`, PROG-ISA-CVT)

Premises: The operands satisfy the register rules (THREAD-REG) and their values have bit patterns
  of their formats' widths or are opaque NaN values of their formats (THREAD-NUM); the destination
  register has the width the decoding recorded.

Effect: Local evaluation; a result the manual leaves open is `noRule`.
  An integer conversion reads the low bits of its source as a value of the source type, clamps it to
  the destination type under `.sat`, and keeps the low bits of the destination width (`cvtIntBits`),
  which is chopping, sign extension of a signed source and zero extension of an unsigned one (Table
  15). The result fills a wider destination register by the extension the decoding recorded
  (`MemExt.extendBits`, Table 28). An unsigned conversion of a symbolic pointer (THREAD-VALUE) at
  its own width keeps the pointer, since the source and destination types are the same. An unsigned
  conversion of a state-space pointer from 32 to 64 bits keeps it too, since zero extension keeps
  the address, and so does one of a `.shared::cluster` pointer from 64 to 32 bits, whose address
  lies below `2 ^ 32` (THREAD-SHARED-POINTER). Any other conversion of a symbolic pointer has no
  rule. `cvt.pack` clamps `a` and `b` to the convert type and puts `b` in the low and `a` in the
  next `size` bits, with the low bits of `c` above them (`cvtPackBits`). The Semantics pseudocode
  clamps `a` from below and then overwrites that value with the clamp from above, which drops the
  lower clamp; the model follows the Description and the `.sat` text, which clamp both ways.
  A floating source is read by `classify` (THREAD-NUM) as a floating datum: a zero with its sign, a
  finite number, an infinity or NaN (`readCvtFloat`). A source of `cvt d, a` in a register wider
  than its format is read through its low bits (`lowValue`): the low half of a pair whose low half
  has the format's width, and otherwise the low bits of the register's bit pattern. A `.bf16`
  source is read at its exact width. A floating result is written by `FVal.toValue`: a payload for
  a number and for `+0`, the bit pattern of `-0` and of an infinity, and the opaque NaN of the
  format for a NaN result, whose encoding the manual leaves unspecified. In a wider destination
  register the result is in the low part with zero bits above it (`cvtFloatDst`), which is the zero
  extension of its bit pattern.
  A floating-to-integer conversion rounds the number by `.rni` (ties to even), `.rzi`, `.rmi` or
  `.rpi` (`CvtRnd.roundInt`) and clamps it to the destination range; an infinity clamps to the end
  of its sign; NaN gives `1 << (w - 1)` for an `.f64` source or a 64-bit destination and zero
  otherwise (`cvtIntOf`). `.ftz` first flushes an `.f32` subnormal to zero.
  A rounding to an integral value at the same format rounds the number by the integer rounding
  modifier; a zero produced by rounding a negative number is `-0`, as IEEE 754 roundToIntegral
  gives, and an infinity and a zero are unchanged (`roundIntElem`). A widening (`.f16`, `.bf16` to
  `.f32`; `.f16`, `.bf16`, `.f32` to `.f64`; the same format without a rounding modifier) keeps the
  datum (`widenElem`), except that its special values follow the rule of a rounded conversion
  below (`cvtSpecial`). NaN gives the opaque NaN in both.
  A conversion with a floating rounding modifier (`.rn`, `.rz`, `.rm`, `.rp`, `.rs`) multiplies the
  number by its scale factor, when there is one, and rounds the exact product into the layout of
  the destination type (`cvtNum`, `cvtRound`, THREAD-FLOAT-ROUND): the narrowings between `.f64`,
  `.f32`, `.f16` and `.bf16`, the integer-to-floating conversions, and the conversions of two `.f32`
  sources or of the elements of an `.f16x2` or `.bf16x2` source to a packed type. Under
  `.satfinite` a number above MAX_NORM in magnitude gives the MAX_NORM of its sign (positive for
  `.ue8m0` and `.ue5m3`), and so does an infinity (`satMaxNorm`); for `.s2f6` a negative input
  above MAX_NORM in magnitude has no rule, since its sign-preserved MAX_NORM can be read as
  `-1.984375` or as `-2.0`. Without `.satfinite` an overflow follows IEEE 754, which agrees with
  §6.5.1 for `.f32` and `.f64`. For `.f16` §6.5.1 gives "~131,000", which is no `.f16` value, and
  for `.bf16` it names no value, so without `.satfinite` and `.sat` an `.f16` result of a number
  above MAX_NORM in magnitude has no rule, and so has a `.bf16` result that IEEE 754 makes an
  infinity; a finite `.bf16` result of MAX_NORM is the IEEE 754 result and is kept. Under `.sat` the
  clamp decides an overflowing result. An infinite input converted from another type to `.f16` or
  `.bf16` without `.satfinite` and `.sat` has no rule: §6.5.1 speaks of numbers beyond the range
  and names no `.bf16` value (its "~131,000" for `.f16` is no datum of that format), while IEEE
  754, with which §9.7.3 makes `cvt` compliant, would keep the infinity; the model declines that
  reading, which makes the rule stricter than the text. An identity conversion (`cvt.f16.f16`,
  `cvt.bf16.bf16`) without `.satfinite` and `.sat`, whose source type or source element type is
  the destination type, is no conversion into a smaller range and keeps the infinity. For another
  destination an infinite input is the infinity of the destination when it has one, and has no
  rule otherwise. A zero keeps its sign; the one zero of `.s2f6` is `+0`. The
  unsigned `.ue8m0` and `.ue5m3` have no rule for a zero, a negative number in range, or a result
  below their smallest value, which for `.ue8m0` is the pattern `0` without a value (EXT-UE8M0).
  NaN under `.sat` gives `+0`; under `.satfinite` it gives the positive MAX_NORM for `.e2m1`,
  `.e2m3`, `.e3m2` and `.s2f6` and the NaN pattern `0xff` for `.ue8m0` and `.ue5m3`, which have no
  rule for NaN without `.satfinite`; every other NaN result, the canonical NaN of `.relu` included,
  is the opaque NaN of the destination.
  After rounding (`cvtFinish`), `.ftz` flushes a subnormal `.f32` result to the zero of its sign; an
  exact number below the smallest normal magnitude that rounds up to it has no rule, since the
  manual does not say whether a result is flushed before or after rounding. Then `.sat` clamps to
  `[0.0, 1.0]`, or `.relu` clamps a negative result to `+0`, reading its "0" as `+0`; whether they
  keep the sign of a `-0` the manual does not say, so a `-0` there has no rule, unless `.pzo`
  makes the result `+0` under both readings. Last, `.pzo` turns `-0` into `+0`.
  `.rs` takes its random bits from `rbits`, the upper half for `a` and the lower half for `b`: for
  `.f16x2` the 13 low bits of the half, and a half whose three high bits are not zero has no rule;
  for `.bf16x2` the whole half (`rsModes`). Its result is determined for normal results only
  (THREAD-FLOAT-ROUND), and an overflow without `.satfinite` has no rule.
  A scale factor is a `.ue8m0` number (EXT-UE8M0, `ue8m0Scale`); the patterns `0` and `0xff` have
  no rule. `.scaled::n1::ue8m0` gives one byte that divides both inputs, and `.scaled::n2::ue8m0`
  two, the upper byte for `a` or the upper element and the lower byte for `b` or the lower element;
  it divides the inputs of `.s2f6x2` and multiplies the elements of a widening to `.bf16x2`, whose
  product is then rounded once. Without the operand the factor is 1 (`cvtScales`). Which of the two
  a conversion has follows from its types, as the syntax gives one of them to each. With
  `.scaled::n1::ue8m0` a subnormal input is flushed to zero first; the manual does not give the
  sign of that zero, so a negative subnormal input has no rule unless `.pzo` makes the result `+0`
  under both readings (`scaledFlush`).
  The results are packed as the Semantics gives: from two `.f32` sources, `a`'s result is the upper
  element and `b`'s the lower; from a packed source, the result of the upper element is the upper
  element. An element of `.f16`, `.bf16`, `.e4m3` or `.e5m2` is written by `FVal.toValue` and the
  result is the pair of the two, low element first; the other formats have no payload format, and
  the result is the `.b8` (`.e2m1x2`) or `.b16` value of the two patterns (`Layout.encode`), each
  6-bit pattern with two zero bits above it (`cvtPack`). A result without a pattern (an opaque NaN
  of such a format) has no rule.
  The elements of a packed source are its two halves (`packedElems`). An `.e2m1x2` source is a
  `.b8` value whose low and high four bits are its elements; the 8-bit packed sources are `.b16`
  values of two bytes, and `.f16x2` and `.bf16x2` are 32-bit values of two halves. The elements of
  the payload formats are read by `classify`, and the others through the layouts of
  THREAD-FLOAT-FORMAT (`cvtElem`): `.ue8m0` by EXT-UE8M0, `.e2m1`, `.e2m3`, `.e3m2` and `.ue5m3` by
  EXT-NARROW-FLOAT, and `.s2f6` as the `.s8` value of the byte times `2^-6`. An `.e2m3` or `.e3m2`
  byte whose two most significant bits are not zero is an input the text does not convert, and has
  no rule. An element of `.e2m1`, `.e2m3`, `.e3m2`, `.ue5m3` or `.s2f6` is a number of at most
  seven significant bits, all at or above `2^-17`, so `.f16` and `.bf16` represent it exactly when
  it is at most MAX_NORM of the destination. A `.ue5m3` element with the exponent field 31 is at
  least `2^16`; its conversion to `.f16` overflows, where §6.5.1 gives no `.f16` value, and has no
  rule (`widenElem`). An unscaled widening of a number never exceeds MAX_NORM of a `.bf16`
  destination, so `.satfinite` does not change its numbers. An infinite `.e5m2` element is an
  infinite input as above: under `.satfinite` it gives the MAX_NORM of its sign, and without it it
  has no rule for both destinations. A NaN element gives the opaque NaN.
  The model has no rule for `.tf32` destinations, whose layout is implementation defined, for
  `.s2f6x2` from `.bf16x2`, whose Description and Semantics select different bits of `a`, and for
  `.rs` to the four-element formats (PROG-ISA-CVT).

### EXT-UE8M0 — values of the ue8m0 format

Statement: A `.ue8m0` pattern `e` between 1 and 254 denotes `2^(e-127)`, the pattern `0xff` is NaN,
  and the pattern `0` has no rule.

Why it is not spec text: The manual describes `.ue8m0` as "This data format is an 8-bit unsigned
  floating-point format with 8 bits for exponent and 0 bits for mantissa." and "The ue8m0 encoding
  does not support infinity. NaN value is limited to 0xff .", and it gives one value: "If not
  specified explicitly, value of scale-factor will be assumed to be 0x7f7f , that is, assumed as
  value 1 for both input scale factors." (§5.2.3, §9.7.10.24). It does not state the bias of the
  exponent or the value of the pattern `0`. The model reads a pattern as a power of two with the
  exponent bias that makes `0x7f` the value 1, and leaves the pattern `0` without a rule, since an
  IEEE-style format would make it a zero and the bias reading would make it `2^-127`.

Effect: A conversion of `.ue8m0x2` elements (`cvt.rn.bf16x2.ue8m0x2`), a conversion to
  `.ue8m0x2` and the scale factors of `.scaled::n1::ue8m0` and `.scaled::n2::ue8m0` use these
  values; if the hardware uses another bias, the proven values differ from the hardware's.
  Disclosed by every kernel whose statement names `FType.ue8m0`: FlashMlaSparseDecodeH64.

### EXT-NARROW-FLOAT — values of the e2m1, e2m3, e3m2 and ue5m3 formats

Statement: A pattern of `.e2m1`, `.e2m3`, `.e3m2` or `.ue5m3` denotes the number of the IEEE 754
  layout with the format's exponent and mantissa widths: exponent bias `2^(e-1) - 1`, a subnormal
  number when the exponent field is zero, a normal number for every other exponent field, and the
  sign bit above the fields for the three signed formats. The `.ue5m3` pattern `0xff` is NaN.

Why it is not spec text: The manual gives the widths and the special values of these formats: "e2m1
  data format: This data format is a 4-bit floating point format with 2 bits for exponent and 1 bit
  for mantissa. The e2m1 encoding does not support infinity and NaN ."; "e2m3 data format: This data
  format is a 6-bit floating point format with 2 bits for exponent and 3 bits for mantissa. The e2m3
  encoding does not support infinity and NaN ."; "e3m2 data format: This data format is a 6-bit
  floating point format with 3 bits for exponent and 2 bits for mantissa. The e3m2 encoding does not
  support infinity and NaN ."; "ue5m3 data format: This data format is a 8-bit unsigned
  floating-point format with 5 bits for exponent and 3 bits for mantissa. The ue5m3 encoding does
  not support infinity. NaN value is limited to 0xff ." (§5.2.3). It does not state the exponent
  bias, how a zero exponent field is read, or where the sign bit is. The model reads them as the
  IEEE 754 binary formats do (§9.7.3: "Instructions that support rounding modifiers are IEEE-754
  compliant."), as THREAD-BITS reads `.e4m3` and `.e5m2`: bias `2^(e-1) - 1`, subnormal numbers at
  the zero exponent field, the sign bit as the most significant bit of the element, and, since there
  is no infinity, a finite number at the largest exponent field except the `.ue5m3` NaN. A pattern
  with the sign bit set and a zero magnitude is `-0`. With this reading the largest `.e2m1` value is
  6, the largest `.e2m3` value 7.5, the largest `.e3m2` value 28 and the largest finite `.ue5m3`
  value 114688.

Effect: The conversions from and to these formats (`cvt.rn.f16x2.e2m1x2`, `cvt.rn.bf16x2.e3m2x2`,
  `cvt.rn.f16x2.ue5m3x2`, `cvt.rn.satfinite.e2m1x2.f32` and the others of THREAD-CVT) use these
  values; if the hardware uses another bias or another subnormal reading, the proven values differ
  from the hardware's. Disclosed by every kernel whose statement names `FType.e2m1`, `FType.e2m3`,
  `FType.e3m2` or `FType.ue5m3`: none.
-/

/-- An integer conversion (§6.5.1, §9.7.10.24): the source value of kind `sk` and `sw` bits,
clamped to the destination type under `sat`, in the low `dw` bits. -/
def cvtIntBits (sat : Bool) (dk : IType) (dw : Nat) (sk : IType) (sw : Nat) (x : BitVec 64) :
    BitVec 64 :=
  intBits dw (intSat sat dk dw (intOf sk sw x))

/-- `cvt.pack.sat` (§9.7.10.25): `a` and `b` read as `.s32` and clamped to the `w`-bit convert type
of kind `k`, `b` in the low `w` bits and `a` in the next `w` bits, and above them the low bits of
`c` when present. -/
def cvtPackBits (k : IType) (w : Nat) (a b : BitVec 64) (c : Option (BitVec 64)) : BitVec 64 :=
  let td := cvtIntBits true k w .s 32 b ||| (cvtIntBits true k w .s 32 a <<< w)
  match c with
  | some c => td ||| (truncBits (32 - 2 * w) c <<< (2 * w))
  | none => td

/-- The low `8 * n` bits of a value's bit pattern as an `8 * n`-bit value. -/
def lowBitsValue (n : Nat) (v : Value) : Exec Value :=
  match v.bitPattern with
  | some p => pure (.bits (8 * n) (BitVec.ofNat 64 (p % 2 ^ (8 * n))))
  | none => throw .typeMismatch

/-- The low `n` bytes of a value wider than `n` bytes (Table 27: chopped): the low half of a pair
whose low half has `n` bytes, otherwise the low bits of the value's bit pattern. -/
def lowValue (n : Nat) : Value → Exec Value
  | .pair lo hi => if lo.bytes = n then pure lo else lowBitsValue n (.pair lo hi)
  | v => lowBitsValue n v

/-- A floating source of `cvt` of format `fmt` as a floating datum (`classify`). With `wide`, a
register value wider than the format is read through its low `fmt.bytes` bytes (`lowValue`, Table
27); a `.bf16` source (`wide` false) is the register's value, which must have the format's width. A
`0f` constant is its 32-bit pattern. -/
def readCvtFloat (wide : Bool) (t : TState) (fmt : FloatFmt) : Opnd → Exec FVal
  | .reg r => do
    let v ← readReg t r
    if wide ∧ fmt.bytes < v.bytes then classify fmt (← lowValue fmt.bytes v)
    else classify fmt v
  | .f32imm b => classify fmt (.bits 32 (BitVec.ofNat 64 b))
  | _ => throw .typeMismatch

/-- A register read without `wide` is classified as it is. -/
theorem readCvtFloat_false {t : TState} {fmt : FloatFmt} {r : Nat} :
    readCvtFloat false t fmt (.reg r) = (do classify fmt (← readReg t r)) := by
  simp [readCvtFloat]

/-- A register whose value has the format's width is classified as it is. -/
theorem readCvtFloat_reg {wide : Bool} {t : TState} {fmt : FloatFmt} {r : Nat} {v : Value}
    (h : t.regs r = some v) (hb : v.bytes = fmt.bytes) :
    readCvtFloat wide t fmt (.reg r) = classify fmt v := by
  simp [readCvtFloat, readReg, h, hb]

/-- A floating result `v` in its destination register: `v` itself, or in a wider register
(`MemExt.zero`, Table 28) the pair of `v` as the low part and zero bits above it. -/
def cvtFloatDst (ext : MemExt) (v : Value) : Value :=
  match ext with
  | .zero rw => .pair v (.bits (rw - 8 * v.bytes) 0)
  | _ => v

@[simp] theorem cvtFloatDst_same {v : Value} : cvtFloatDst .same v = v := rfl

/-- The integer that an integer rounding modifier rounds `x` to: down for `.rmi`, up for `.rpi`,
toward zero for `.rzi`, and to nearest with ties to even for `.rni`. The other modifiers do not
reach it (`CvtInstr.exact`), and they round as `.rni` here. -/
def CvtRnd.roundInt (r : CvtRnd) (x : ℝ) : ℤ :=
  match r with
  | .rmi => ⌊x⌋
  | .rpi => ⌈x⌉
  | .rzi => if 0 ≤ x then ⌊x⌋ else ⌈x⌉
  | _ =>
    if x - ⌊x⌋ < 1 / 2 then ⌊x⌋
    else if 1 / 2 < x - ⌊x⌋ then ⌊x⌋ + 1
    else if ⌊x⌋ % 2 = 0 then ⌊x⌋ else ⌊x⌋ + 1

/-- The rounding mode (THREAD-FLOAT-ROUND) of a floating rounding modifier `.rn`, `.rz`, `.rm` or
`.rp`; the integer rounding modifiers, `.rna` and `.rs` have none. -/
def CvtRnd.mode? : CvtRnd → Option RoundMode
  | .rn => some .rn
  | .rz => some .rz
  | .rm => some .rm
  | .rp => some .rp
  | _ => none

/-- The integer of a floating datum converted by the integer rounding modifier `r` to an integer
type of kind `k` and `w` bits: the rounded number clamped to the destination range, an infinity
clamped to the end of its sign, and for NaN `2 ^ (w - 1)` (`1 << (w - 1)`) when the source is
`.f64` (`f64`) or the destination has 64 bits, zero otherwise. -/
def cvtIntOf (r : CvtRnd) (k : IType) (w : Nat) (f64 : Bool) : FVal → ℤ
  | .zero _ => 0
  | .fin q => intSat true k w (r.roundInt (q : ℝ))
  | .inf neg => intSat true k w (if neg then -2 ^ w else 2 ^ w)
  | .nan _ => if f64 || w == 64 then 2 ^ (w - 1) else 0

/-- A finite number converts as before infinities and NaN had a rule. -/
theorem cvtIntOf_fin {r : CvtRnd} {k : IType} {w : Nat} {f64 : Bool} {q : ℚ} :
    cvtIntOf r k w f64 (.fin q) = intSat true k w (r.roundInt (q : ℝ)) := rfl

/-- `.relu` of a floating result: a negative number or `-∞` becomes `+0`, and NaN the opaque NaN
(the canonical NaN, whose encoding is not stated). A `-0` has no rule, since the manual does not
say whether the clamp keeps its sign, unless `.pzo` (`pzo`) makes it `+0` either way. -/
def reluFVal (pzo : Bool) : FVal → Exec FVal
  | .nan _ => pure (.nan none)
  | .zero true => if pzo then pure (.zero false) else throw .noRule
  | .zero false => pure (.zero false)
  | .fin q => pure (if q < 0 then .zero false else .fin q)
  | .inf neg => pure (if neg then .zero false else .inf false)

/-- `.pzo` of a floating result: `-0` becomes `+0`. -/
def pzoFVal : FVal → FVal
  | .zero _ => .zero false
  | x => x

/-- The qualifiers applied to a converted datum of layout `D`, in this order: the `.ftz` flush
(`ftz`, for an `.f32` destination), `.sat` or `.relu`, and `.pzo`. -/
def cvtFinish (c : CvtInstr) (ftz : Bool) (D : Layout) (x : FVal) : Exec FVal := do
  let x := if ftz then D.flush x else x
  let x ← if c.sat then (match x.sat with
      | some v => pure v
      | none => throw .noRule)
    else if c.relu then reluFVal c.pzo x else pure x
  pure (if c.pzo then pzoFVal x else x)

/-- The `.satfinite` result of an infinite input of sign `neg`, which is above MAX_NORM in
magnitude: the MAX_NORM of its sign, positive in an unsigned layout; a negative input to a
fixed-point layout has no rule, as in THREAD-FLOAT-ROUND. -/
def satMaxNorm (D : Layout) (neg : Bool) : Exec FVal :=
  match D with
  | .binary _ _ signed _ => pure (.fin (if neg && signed then -D.maxNorm else D.maxNorm))
  | .fixed .. => if neg then throw .noRule else pure (.fin D.maxNorm)

open Classical in
/-- The datum of the exact nonzero number `x` converted to the type `df` of layout `D` by mode `m`
(THREAD-FLOAT-ROUND), with `Overflow.satfinite` under `.satfinite` and under `.sat`, whose clamp
decides an overflowing result, and IEEE 754 overflow otherwise. Without both, an `.f16` result of a
number above MAX_NORM in magnitude and a `.bf16` result that IEEE 754 makes an infinity have no rule
(§6.5.1). With `ftz`, a number below the smallest normal magnitude that rounds up to it has no
rule. -/
def cvtRound (c : CvtInstr) (df : FType) (D : Layout) (m : RoundMode) (ftz : Bool) (x : ℝ) :
    Exec FVal :=
  match D.round m (if c.satfinite || c.sat then .satfinite else .inf) x false with
  | none => throw .noRule
  | some r =>
    let over : Bool := match df, r with
      | .f16, _ => decide (((D.maxNorm : ℚ) : ℝ) < |x|)
      | .bf16, .inf _ => true
      | _, _ => false
    if !c.satfinite && !c.sat && over then throw .noRule
    else if ftz && decide (|x| < ((D.minNormal : ℚ) : ℝ)) &&
        (r == .fin D.minNormal || r == .fin (-D.minNormal)) then throw .noRule
    else pure r

/-- The special values of a floating datum `x` converted to the type `df` of layout `D`, and the
number `q` of a finite datum by `num q`: NaN gives `+0` under `.sat` (by `FVal.sat`), under
`.satfinite` the positive MAX_NORM in a signed layout without NaN and the all-ones NaN pattern in
an unsigned layout (no rule for these without `.satfinite`), and the opaque NaN otherwise; an
infinity is above MAX_NORM for `.satfinite` (`satMaxNorm`), is clamped by `.sat`, has no rule
otherwise for an `.f16` or `.bf16` destination whose type is neither the source type nor the
element type of a packed source (as an overflow in `cvtRound`), and stays itself in another
layout with infinities, the source type included; a zero keeps its sign, is `+0` in a
fixed-point layout and has no rule in an unsigned layout.
`cvtNum` and `widenElem` share it. -/
def cvtSpecial (c : CvtInstr) (df : FType) (D : Layout) (num : ℚ → Exec FVal) :
    FVal → Exec FVal
  | .nan _ =>
    if c.sat then pure (.nan none)
    else match D with
      | .binary _ _ true .none | .fixed .. =>
        if c.satfinite then pure (.fin D.maxNorm) else throw .noRule
      | .binary _ _ false _ =>
        if c.satfinite then pure (.nan (some (2 ^ D.width - 1))) else throw .noRule
      | .binary .. => pure (.nan none)
  | .inf neg =>
    if c.satfinite then satMaxNorm D neg
    else if c.sat then pure (.inf neg)
    else if (df = .f16 ∨ df = .bf16) ∧ c.src ≠ .float df ∧ c.src ≠ .packed (.float df) 2 then
      throw .noRule
    else match D with
      | .binary _ _ true .ieee => pure (.inf neg)
      | _ => throw .noRule
  | .zero neg =>
    match D with
    | .binary _ _ true _ => pure (.zero neg)
    | .binary _ _ false _ => throw .noRule
    | .fixed .. => pure (.zero false)
  | .fin q => num q

/-- A floating datum `x` converted to the type `df` of layout `D` by the rounding mode `m`, its
number first multiplied by the scale `s`: the special values by `cvtSpecial`, a number rounded by
`cvtRound`; then `cvtFinish`. -/
def cvtNum (c : CvtInstr) (df : FType) (D : Layout) (m : RoundMode) (ftz : Bool) (s : ℚ)
    (x : FVal) : Exec FVal := do
  let r ← cvtSpecial c df D (fun q => cvtRound c df D m ftz ((q : ℝ) * (s : ℝ))) x
  cvtFinish c ftz D r

/-- A floating datum widened exactly to the type `df` of layout `D`: the special values by
`cvtSpecial`, so that an infinity converted to `.f16` or `.bf16` from another type has no rule
without `.satfinite` and `.sat`, and the same number otherwise; a number above MAX_NORM of `D`
in magnitude has no rule, which only a `.ue5m3` element of at least `2^16` converted to `.f16`
reaches (§6.5.1); then `cvtFinish`. -/
def widenElem (c : CvtInstr) (df : FType) (D : Layout) (ftz : Bool) (x : FVal) : Exec FVal := do
  let r ← cvtSpecial c df D
    (fun q => if D.maxNorm < |q| then throw .noRule else pure (.fin q)) x
  cvtFinish c ftz D r

/-- A number within MAX_NORM widens to itself, as before the bound and NaN had a rule. -/
theorem widenElem_fin {c : CvtInstr} {df : FType} {D : Layout} {ftz : Bool} {q : ℚ}
    (h : |q| ≤ D.maxNorm) : widenElem c df D ftz (.fin q) = cvtFinish c ftz D (.fin q) := by
  simp [widenElem, cvtSpecial, not_lt.mpr h, bind, Except.bind, pure, Except.pure]

/-- A floating datum rounded to an integral value at its own format of layout `D` by the integer
rounding modifier `r`: a number rounded to zero gives the zero of its sign, as IEEE 754
roundToIntegral gives; a zero and an infinity are unchanged, and NaN gives the opaque NaN; then
`cvtFinish`. -/
def roundIntElem (c : CvtInstr) (r : CvtRnd) (D : Layout) (ftz : Bool) : FVal → Exec FVal
  | .fin q =>
    let z := r.roundInt (q : ℝ)
    cvtFinish c ftz D (if z = 0 then .zero (decide (q < 0)) else .fin (z : ℚ))
  | .nan _ => cvtFinish c ftz D (.nan none)
  | x => cvtFinish c ftz D x

/-- An element of a packed source of type `sf` as a floating datum: an element of a payload format
by `classify`, and one of the other formats from the pattern of a one-byte value through the layout
of its type (EXT-UE8M0, EXT-NARROW-FLOAT, §5.2.4). An `.e2m3` or `.e3m2` byte whose two most
significant bits are not zero and a pattern without a value (the `.ue8m0` pattern `0`) have no
rule. -/
def cvtElem (sf : FType) (v : Value) : Exec FVal :=
  match sf.fmt? with
  | some fmt => classify fmt v
  | none => match v.bitPattern, sf.layout? with
    | some e, some D =>
      if v.bytes ≠ 1 then throw .typeMismatch
      else if (sf = .e2m3 ∨ sf = .e3m2) ∧ 64 ≤ e then throw .noRule
      else match D.decode e with
        | some x => pure x
        | none => throw .noRule
    | _, _ => throw .typeMismatch

/-- An element of a payload format is classified. -/
theorem cvtElem_fmt {sf : FType} {fmt : FloatFmt} {v : Value} (h : sf.fmt? = some fmt) :
    cvtElem sf v = classify fmt v := by
  simp [cvtElem, h]

/-- A `.ue8m0` element pattern `e` from 1 to 254 is `2^(e-127)`, as before the layouts. -/
theorem cvtElem_ue8m0 {v : Value} {e : Nat} (h : v.bitPattern = some e) (hb : v.bytes = 1)
    (h0 : 0 < e) (h1 : e < 255) :
    cvtElem .ue8m0 v = .ok (.fin ((2 : ℚ) ^ ((e : ℤ) - 127))) := by
  have he : e % 256 = e := Nat.mod_eq_of_lt (by omega)
  have hne : e ≠ 255 := by omega
  have hz : e ≠ 0 := by omega
  simp [cvtElem, FType.fmt?, FType.layout?, h, hb, Layout.decode, Layout.width, Layout.fieldVal,
    Layout.magnitude, Layout.bias, he, hne, hz, Nat.mod_one, pure, Except.pure]

/-- The two elements (low, high) of a packed source of type `sf` (`cvtElem`): the low and high
four bits of a `.b8` value for `.e2m1`, the two halves of a 32-bit value for `.f16` and `.bf16`,
and the two bytes of a `.b16` value for the other types. -/
def packedElems (sf : FType) (v : Value) : Exec (FVal × FVal) :=
  match sf with
  | .e2m1 => do
    unless v.bytes = 1 do throw .typeMismatch
    let some n := v.bitPattern | throw .typeMismatch
    pure (← cvtElem .e2m1 (.bits 8 (BitVec.ofNat 64 (n % 16))),
      ← cvtElem .e2m1 (.bits 8 (BitVec.ofNat 64 (n / 16 % 16))))
  | .f16 | .bf16 => do
    unless v.bytes = 4 do throw .typeMismatch
    pure (← cvtElem sf (splitValue 32 v).1, ← cvtElem sf (splitValue 32 v).2)
  | _ => do
    unless v.bytes = 2 do throw .typeMismatch
    pure (← cvtElem sf (splitValue 16 v).1, ← cvtElem sf (splitValue 16 v).2)

/-- The number of a `.ue8m0` scale-factor pattern `e` through the layout of `.ue8m0`
(EXT-UE8M0); NaN (`0xff`) and the pattern `0` have no rule. -/
def ue8m0Scale (e : Nat) : Exec ℚ :=
  match FType.ue8m0.layout?.bind (·.decode e) with
  | some (.fin q) => pure q
  | _ => throw .noRule

/-- A scale-factor pattern from 1 to 254 is `2^(e-127)`. -/
theorem ue8m0Scale_eq {e : Nat} (h0 : 0 < e) (h1 : e < 255) :
    ue8m0Scale e = .ok ((2 : ℚ) ^ ((e : ℤ) - 127)) := by
  have he : e % 256 = e := Nat.mod_eq_of_lt (by omega)
  have hne : e ≠ 255 := by omega
  have hz : e ≠ 0 := by omega
  have he' : (e : ℤ) % 256 = e := by omega
  simp [ue8m0Scale, FType.layout?, Layout.decode, Layout.width, Layout.fieldVal, Layout.magnitude,
    Layout.bias, he, he', hne, hz, Nat.mod_one, pure, Except.pure]

/-- The scale factors of `a` or the upper element and of `b` or the lower element, from the
operands after the sources: with two packed factors (`n2`, `.scaled::n2::ue8m0`) the upper byte
and the lower byte of a `.b16` operand, with one (`.scaled::n1::ue8m0`) the `.b8` operand for
both, and `1` without the operand (the defaults `0x7f7f` and `0x7f`). -/
def cvtScales (L : Launch) (g : Nat) (t : TState) (n2 : Bool) : List Opnd → Exec (ℚ × ℚ)
  | [] => pure (1, 1)
  | [o] => do
    if n2 then
      let e := (← readBits L g t 16 o).toNat
      pure (← ue8m0Scale (e / 256 % 256), ← ue8m0Scale (e % 256))
    else
      let s ← ue8m0Scale (← readBits L g t 8 o).toNat
      pure (s, s)
  | _ => throw .noRule

/-- `.scaled::n1::ue8m0`: a subnormal input of source layout `S` is flushed to zero. The manual
does not give the sign of that zero, so a negative subnormal input has no rule unless `.pzo` makes
the result `+0` either way. -/
def scaledFlush (c : CvtInstr) (S : Layout) : FVal → Exec FVal
  | .fin q =>
    if S.subnormal q then (if q < 0 ∧ c.pzo = false then throw .noRule else pure (.zero false))
    else pure (.fin q)
  | x => pure x

/-- The `.rs` rounding modes of `a` and `b` from `rbits`: `a` takes the upper and `b` the lower
16-bit half; for `.f16` a half gives 13 random bits and must have its three high bits zero, for
`.bf16` the whole half gives 16. Any other destination has no rule. -/
def rsModes (df : FType) (rbits : BitVec 64) : Exec (RoundMode × RoundMode) :=
  let ha := rbits.toNat / 2 ^ 16 % 2 ^ 16
  let hb := rbits.toNat % 2 ^ 16
  match df with
  | .f16 => if ha < 2 ^ 13 ∧ hb < 2 ^ 13 then pure (.rs 13 ha, .rs 13 hb) else throw .noRule
  | .bf16 => pure (.rs 16 ha, .rs 16 hb)
  | _ => throw .noRule

/-- The register value of the converted elements `lo` and `hi` of the packed type `df` of layout
`D`: for a payload format the pair of their values (`FVal.toValue`), low element first; otherwise
the `.b8` value (a layout of at most four bits) or `.b16` value of their patterns
(`Layout.encode`), `hi` above `lo`. An element without a pattern has no rule. -/
def cvtPack (df : FType) (D : Layout) (lo hi : FVal) : Exec Value :=
  match df.fmt? with
  | some fmt => pure (.pair (lo.toValue fmt) (hi.toValue fmt))
  | none => match D.encode lo, D.encode hi with
    | some a, some b =>
      let w := if D.width ≤ 4 then 4 else 8
      pure (.bits (2 * w) (BitVec.ofNat 64 (a + 2 ^ w * b)))
    | _, _ => throw .noRule

/-- A conversion (THREAD-CVT). The first case of an integer source is the general one,
`cvtIntBits false dk dw .u sw x` with the destination's own width, written out as `truncBits`. -/
def execCvt (L : Launch) (g : Nat) (t : TState) (c : CvtInstr) : Exec TState :=
  match c.dst, c.src, c.srcs with
  | .int dk dw, .int sk sw, [a] => do
    let v ← readValue L g t sw a
    match v with
    | .ptr w generic sp off =>
      let narrows : Bool := match sp with
        | .shared .. => true
        | _ => false
      if sk = .u ∧ dk = .u ∧ c.sat = false ∧ c.ext = .same ∧ w = sw ∧
          (dw = sw ∨ (generic = false ∧ (dw = 32 ∨ dw = 64) ∧ (sw ≤ dw ∨ narrows))) then
        pure (next (setReg t c.d (.ptr dw generic sp off)))
      else throw .noRule
    | _ => do
      let x ← readBits L g t sw a
      match c.sat, sk, c.ext with
      | false, .u, .same => pure (next (setReg t c.d (.bits dw (truncBits dw x))))
      | sat, sk, ext =>
        pure (next (setReg t c.d (ext.extendBits dw (cvtIntBits sat dk dw sk sw x))))
  | .int dk dw, .int .s 32, [a, b] => do
    let x ← readBits L g t 32 a; let y ← readBits L g t 32 b
    pure (next (setReg t c.d (.bits 32 (cvtPackBits dk dw x y none))))
  | .int dk dw, .int .s 32, [a, b, e] => do
    let x ← readBits L g t 32 a; let y ← readBits L g t 32 b; let z ← readBits L g t 32 e
    pure (next (setReg t c.d (.bits 32 (cvtPackBits dk dw x y (some z)))))
  | .int dk dw, .float sf, [a] => do
    let some fmt := sf.fmt? | throw .noRule
    let some r := c.rnd | throw .noRule
    let x ← readCvtFloat (sf != .bf16) t fmt a
    let x := if c.ftz ∧ fmt = .f32 then fmt.layout.flush x else x
    pure (next (setReg t c.d
      (c.ext.extendBits dw (intBits dw (cvtIntOf r dk dw (fmt == .f64) x)))))
  | .float df, .float sf, [a] => do
    let some dfmt := df.fmt? | throw .noRule
    let some sfmt := sf.fmt? | throw .noRule
    let x ← readCvtFloat (sf != .bf16) t sfmt a
    let x := if c.ftz ∧ sfmt = .f32 then sfmt.layout.flush x else x
    let ftz := c.ftz && dfmt == .f32
    let y ← match c.rnd with
      | none => widenElem c df dfmt.layout ftz x
      | some r => match r.mode? with
        | some m => cvtNum c df dfmt.layout m ftz 1 x
        | none => roundIntElem c r dfmt.layout ftz x
    pure (next (setReg t c.d (cvtFloatDst c.ext (y.toValue dfmt))))
  | .float df, .int sk sw, [a] => do
    let some dfmt := df.fmt? | throw .noRule
    let some m := c.rnd.bind CvtRnd.mode? | throw .noRule
    let n := intOf sk sw (← readBits L g t sw a)
    let y ← cvtNum c df dfmt.layout m (c.ftz && dfmt == .f32) 1 (FVal.ofRat (n : ℚ))
    pure (next (setReg t c.d (cvtFloatDst c.ext (y.toValue dfmt))))
  | .packed (.float df) 2, .float .f32, a :: b :: rest => do
    let some D := df.layout? | throw .noRule
    let xa ← readCvtFloat false t .f32 a
    let xb ← readCvtFloat false t .f32 b
    let (hi, lo) ← match c.rnd, rest with
      | some .rs, [e] => do
        let (ma, mb) ← rsModes df (← readBits L g t 32 e)
        pure (← cvtNum c df D ma false 1 xa, ← cvtNum c df D mb false 1 xb)
      | some r, rest => do
        let some m := r.mode? | throw .noRule
        let (sa, sb) ← cvtScales L g t (df == .s2f6) rest
        let n1 := c.scaled && df != .s2f6
        let xa ← if n1 then scaledFlush c FloatFmt.f32.layout xa else pure xa
        let xb ← if n1 then scaledFlush c FloatFmt.f32.layout xb else pure xb
        pure (← cvtNum c df D m false sa⁻¹ xa, ← cvtNum c df D m false sb⁻¹ xb)
      | none, _ => throw .noRule
    pure (next (setReg t c.d (← cvtPack df D lo hi)))
  | .packed (.float df) 2, .packed (.float sf) 2, a :: rest => do
    let some D := df.layout? | throw .noRule
    let some S := sf.layout? | throw .noRule
    let w := if sf = .e2m1 then 8 else if sf = .f16 ∨ sf = .bf16 then 32 else 16
    let (xl, xh) ← packedElems sf (← readValue L g t w a)
    let (lo, hi) ← if sf = .f16 ∨ sf = .bf16 then do
        if df = .s2f6 then throw .noRule
        let some m := c.rnd.bind CvtRnd.mode? | throw .noRule
        let (s, _) ← cvtScales L g t false rest
        let xl ← if c.scaled then scaledFlush c S xl else pure xl
        let xh ← if c.scaled then scaledFlush c S xh else pure xh
        pure (← cvtNum c df D m false s⁻¹ xl, ← cvtNum c df D m false s⁻¹ xh)
      else if df = .f16 ∨ df = .bf16 then do
        let some m := c.rnd.bind CvtRnd.mode? | throw .noRule
        let (sh, sl) ← cvtScales L g t true rest
        let el ← if sl = 1 then widenElem c df D false xl else cvtNum c df D m false sl xl
        let eh ← if sh = 1 then widenElem c df D false xh else cvtNum c df D m false sh xh
        pure (el, eh)
      else throw .noRule
    pure (next (setReg t c.d (← cvtPack df D lo hi)))
  | _, _, _ => throw .noRule

/-! ## THREAD-BRANCH — branches and predication
Statement: A branch sets the source position to its target. `brx.idx` takes the target at the
  position of its index in its `.branchtargets` list, and an index outside the list is undefined.
  A guarded instruction runs when its guard predicate, or its negation, holds and is skipped
  otherwise, and a guard that is not a predicate is undefined.

Defs: execBranch, guardHolds

Source:
- §9.7.14.3 (bra): "if (p) { pc = tgt; }"
- §9.7.14.4 (brx.idx): "The index operand is a .u32 register."
- §9.7.14.4 (brx.idx): "It is accessed as a zero-based sequence using index ."
- §9.7.14.4 (brx.idx): "Behavior is undefined if the value of index is greater than or equal to the
    length of tlist ."
- §9.7.14.4 (brx.idx): "brx.idx.uni guarantees that the branch is non-divergent, i.e. all active
    threads in a warp that are currently executing this instruction have identical values for the
    guard predicate and the index argument."
- §9.3 (predicated execution)

Direction: stricter

Applies: Branches, predicates and instruction guards

Premises: A branch has a target; the index of `brx.idx` is below the length of its list; a present
  guard register contains a predicate.

Effect: Local control flow; an index outside the list is the `badValue` fault. A branch sets `pc` to
  its target. A guarded instruction runs when its predicate (or its negation) holds and is skipped
  otherwise; a guard that is not a predicate is undefined. The `.uni` qualifier does not change what
  one thread does; disagreement between the lanes of a warp is ERR-NONUNIFORM-GUARD. `brx.idx` reads
  its index as a 32-bit unsigned integer, and the decoder resolves the `.branchtargets` list to
  source positions (PROG-DECODE). `brx.idx.uni` has the rule of `brx.idx`; its guarantee covers
  the guard and the index, and ERR-NONUNIFORM-GUARD compares both between the lanes of a warp.
-/

/-- A branch sets the next source position: the target of `bra`, or the entry of the target
list at the index of `brx.idx`, which is undefined outside the list. -/
def execBranch (L : Launch) (g : Nat) (t : TState) : Op → Exec TState
  | .bra target _ => pure ({ t with pc := target })
  | .brx index targets _ => do
    let i ← readBits L g t 32 index
    match targets[i.toNat]? with
    | some target => pure ({ t with pc := target })
    | none => throw .badValue
  | _ => throw .noRule

/-- Whether the guard of an instruction holds: true without a guard, otherwise the predicate,
negated when requested. -/
def guardHolds (t : TState) : Option (Nat × Bool) → Exec Bool
  | none => pure true
  | some (p, negated) => do
    match ← readReg t p with
    | .pred b => pure (b != negated)
    | _ => throw .typeMismatch

/-- Lane `j` of a floating operand of type `ty`: the value itself for one lane, its low or high
half for two lanes (§9.7.3: "fA[0] = a[0:31]; fA[1] = a[32:63];"). -/
def floatLane (ty : FTy) (v : Value) (j : Nat) : Value :=
  if ty.lanes = 1 then v
  else if j = 0 then (splitValue (16 * ty.fmt.bytes) v).1
  else (splitValue (16 * ty.fmt.bytes) v).2

/-- `1.0` or `0.0` in format `fmt`. -/
def unitValue (fmt : FloatFmt) (b : Bool) : Value :=
  (if b then FVal.fin 1 else .zero false).toValue fmt

/-- The value `set` writes for the outcomes of its lanes in its destination type `dst`, with
`src` the floating source format (none for an integer source; §9.7.7.1, §9.7.8.1): `1.0` or `0.0`
in a floating format, all ones or zero in an integer type, and the two lane results packed in
16-bit halves of a 32-bit integer destination. `none` where the Semantics and the Description of
§9.7.8.1 give different values: a `.bf16` destination with another source type, and an integer
destination with a `.bf16` or `.bf16x2` source. -/
def setResult (dst : DType) (src : Option FloatFmt) : List Bool → Option Value
  | [b] => match dst with
    | .float .f32 => some (unitValue .f32 b)
    | .float .f16 => some (unitValue .f16 b)
    | .float .bf16 => if src = some .bf16 then some (unitValue .bf16 b) else none
    | .int _ w =>
      if src = some .bf16 then none
      else some (.bits w (BitVec.ofNat 64 (if b then 2 ^ w - 1 else 0)))
    | _ => none
  | [b0, b1] => match dst with
    | .packed (.float .f16) 2 => some (.pair (unitValue .f16 b0) (unitValue .f16 b1))
    | .packed (.float .bf16) 2 => some (.pair (unitValue .bf16 b0) (unitValue .bf16 b1))
    | .int _ 32 =>
      if src = some .bf16 then none
      else some (.bits 32 (BitVec.ofNat 64
        ((if b0 then 0xffff else 0) + (if b1 then 0xffff0000 else 0))))
    | _ => none
  | _ => none

/-- A floating instruction (THREAD-FLOAT): each source is read at its type's width and each lane
of it classified in its format (`classify`); THREAD-FLOAT's lane rule gives each lane's result;
`setp` and `set` combine the comparison with `BoolOp` and `c` (`boolCombine`), `setp` writes `p`
and `q`, `set` its encoded result (`setResult`), and every other operation writes the lanes'
results in the destination format (`FVal.toValue`, a pair low lane first). A `set` with an integer
source type compares as THREAD-INT does. -/
def execFloat (L : Launch) (g : Nat) (t : TState) (f : FloatInstr) : Exec TState := do
  let (fs, cs) := match f.op with
    | .setp _ (some _) | .set _ (some _) _ => (f.srcs.dropLast, f.srcs.drop (f.srcs.length - 1))
    | _ => (f.srcs, [])
  let bop := match f.op with
    | .setp _ b | .set _ b _ => b
    | _ => none
  let comb ← boolCombine L g t bop cs
  -- An integer `set` (§9.7.8.1 with an integer `.stype`).
  if let some (.int k w) := f.cmpTy then
    let .set (.ord c) _ dst := f.op | throw .noRule
    let [a, b] := fs | throw .noRule
    let x ← readBits L g t w a; let y ← readBits L g t w b
    let some v := setResult dst none [comb (compare c k w x y)] | throw .noRule
    let [some d] := f.dsts | throw .noRule
    return next (setReg t d v)
  let tys := if f.srcTys.isEmpty then fs.map (fun _ => f.ty) else f.srcTys
  unless tys.length = fs.length do throw .noRule
  let vs ← (tys.zip fs).mapM fun (ty, o) => readValue L g t (8 * ty.fmt.bytes * ty.lanes) o
  let outs ← (List.range f.ty.lanes).mapM fun j => do
    let xs ← (tys.zip vs).mapM fun (ty, v) => classify ty.fmt (floatLane ty v j)
    match f.lane xs with
    | some o => pure o
    | none => throw .noRule
  match f.op, outs, f.dsts with
  | .setp .., [.pred r], [some p] => pure (next (setReg t p (.pred (comb r))))
  | .setp .., [.pred r], [p, q] =>
    pure (next (setDst (setDst t p (.pred (comb r))) q (.pred (comb !r))))
  | .setp .., [.pred r0, .pred r1], [p, q] =>
    pure (next (setDst (setDst t p (.pred (comb r0))) q (.pred (comb r1))))
  | .set _ _ dst, rs, [some d] => do
    let bs ← rs.mapM fun | .pred b => pure (comb b) | .val _ => throw .noRule
    let some v := setResult dst (some f.ty.fmt) bs | throw .noRule
    pure (next (setReg t d v))
  | .testp _, [.pred r], [some p] => pure (next (setReg t p (.pred r)))
  | _, [.val v], [some d] => pure (next (setReg t d (v.toValue f.ty.fmt)))
  | _, [.val v0, .val v1], [some d] =>
    pure (next (setReg t d (.pair (v0.toValue f.ty.fmt) (v1.toValue f.ty.fmt))))
  | _, _, _ => throw .noRule

/-! ## THREAD-LOCAL — which rule a local instruction uses
Statement: A local instruction is executed by the rule that `Op.rule` names (PROG-INSTR-RULE):
  integer and floating operations, moves, conversions, address windows, shared addresses, cache
  prefetches, cache policies, `nanosleep` and `pmevent`, the tensormap prefetch or branches, and
  every other instruction has none. A kernel assumption that selects an instruction supplies its
  rule in place of the core's, and may replace a stretch of straight-line code by one local step.

Defs: execLocal, execLocal_cvta, execLocalRule, execLocalRule_of_none, execLocalA,
  execLocalA_noSegment

Source:
- none (dispatch)

Direction: equal

Applies: Local instruction dispatch, including optional assumptions

Premises: The instruction is local; any selected assumption supplies its local rule or segment.

Effect: Local rule assembly.
  When several assumption rules apply, the first one is used. A segment that an assumption selects
  at the thread's state replaces both the built-in rule and the assumption rules.
  `execLocal` sends each local instruction to the rule `Op.rule` names, and an instruction whose
  rule is none (a decode-only form, `Op.unmodeled`, `brx.idx.uni`) has `noRule`. In
  `execLocalRule` the kernel assumptions are consulted first: the first whose `localRule` selects
  the instruction at this state gives the outcome, and with none selecting it the outcome is the
  core's (`execLocalRule_of_none`). The assumptions that set `localRule` (ASM-IDEAL, ASM-APPROX)
  select only the floating forms they name and decline the operands they do not read, so every other
  instruction keeps the core's rule. `execLocalA` first asks
  the assumptions for a segment (`segmentRule`, ASM-INTERFACE): the first that selects one at this
  state gives the outcome of the whole straight-line code from the thread's `pc` as one local step,
  which may continue at any `pc`. With no segment selected the rule is `execLocalRule`
  (`execLocalA_noSegment`); without a kernel assumption that selects segments nothing changes.
-/

/-- A thread-local instruction: the new local state only. Memory and other threads are
not inputs. The rule is the one `Op.rule` names; an instruction whose rule is none or names an
event rule has no local rule. -/
def execLocal (L : Launch) (g : Nat) (t : TState) (op : Op) : Exec TState :=
  match op.rule, op with
  | some .threadInt, .int i => execInt L g t i
  | some .threadFloat, .float f => execFloat L g t f
  | some .threadMove, op => execMove L g t op
  | some .threadCvt, .cvt c => execCvt L g t c
  | some .threadCvta, .addr c => execCvta L g t c
  | some .threadSharedPointer, .addr c => execSharedAddress L g t c
  | some .threadPrefetch, .addr c => execPrefetch L g t c
  | some .threadCachePolicy, .misc m | some .threadNoEffect, .misc m => execMisc L g t m
  | some .threadTensorMapPrefetch, op => execTensorMapPrefetch L g t op
  | some .threadBranch, op => execBranch L g t op
  | _, _ => throw .noRule

/-- An address instruction whose rule is THREAD-CVTA runs `execCvta`; for `cvta.global` and
`cvta.param` this replaces the data-movement and parameter-pointer rules that ran them before. -/
theorem execLocal_cvta {L : Launch} {g : Nat} {t : TState} {c : AddrInstr}
    (h : c.rule = some .threadCvta) : execLocal L g t (.addr c) = execCvta L g t c := by
  simp only [execLocal, Op.rule, h]

/-- A local rule: the rule of the first kernel assumption that selects the instruction at this
state, otherwise the core's rule. -/
def execLocalRule (A : List Assumption) (L : Launch) (g : Nat) (t : TState) (op : Op) :
    Exec TState :=
  match A.findSome? (fun a => a.localRule L g t op) with
  | some r => r
  | none => execLocal L g t op

/-- With no assumption selecting the instruction at this state, the local rule is the core's. -/
theorem execLocalRule_of_none {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (h : ∀ a ∈ A, a.localRule L g t op = none) : execLocalRule A L g t op = execLocal L g t op := by
  unfold execLocalRule
  rw [List.findSome?_eq_none_iff.mpr h]

/-- The local step: a segment an assumption selects at this state, otherwise the local rule. -/
def execLocalA (A : List Assumption) (L : Launch) (g : Nat) (t : TState) (op : Op) :
    Exec TState :=
  match A.findSome? (fun a => a.segmentRule L g t) with
  | some r => r
  | none => execLocalRule A L g t op

/-- With no assumption selecting a segment at the thread's state, the local step is the local
rule of the instruction. -/
theorem execLocalA_noSegment {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} (h : ∀ a ∈ A, a.segmentRule L g t = none) :
    execLocalA A L g t op = execLocalRule A L g t op := by
  unfold execLocalA
  rw [List.findSome?_eq_none_iff.mpr h]


/-- The source operands with the special registers that change while the thread runs replaced, in
operand order, by the values read (THREAD-SREG). -/
def substVarying : List Opnd → List Nat → List Opnd
  | [], _ => []
  | o :: os, vs => match o.varying?, vs with
    | some _, v :: vs => .imm v :: substVarying os vs
    | _, vs => o :: substVarying os vs

/-- The instruction with its reads of changing special registers replaced by the values read
(THREAD-SREG); every other instruction unchanged. -/
def Op.withSregValues (op : Op) (vs : List Nat) : Op :=
  match op with
  | .int i => .int { i with srcs := substVarying i.srcs vs }
  | .move m => .move { m with srcs := substVarying m.srcs vs }
  | .cvt c => .cvt { c with srcs := substVarying c.srcs vs }
  | op => op

/-- The event of an integer, move or conversion instruction that reads special registers whose
values change while the thread runs (THREAD-SREG): one read of each, below its bound, then the
local rule of the instruction with the values read; a fault of that rule is a pending fault. -/
def sregTmpl (A : List Assumption) (L : Launch) (g : Nat) (t : TState) (op : Op) : Tmpl :=
  .sreg (op.varyingSregs.map fun s => (s, s.readBound L g)) fun vs =>
    match execLocalA A L g t (op.withSregValues vs) with
    | .ok t' => t'
    | .error f => { t with fault := some f }
end

end PTX
