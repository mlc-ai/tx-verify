-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaOrder
public import Core.Thread.Access

@[expose] public section

namespace PTX.TcMma
noncomputable section

/-! ## DEP-TC-MMA-VALUE — finite derivations of MMA accumulator values
Statement: The value of a result cell of a `kind::i8` MMA is the exact sum of the 32 products of its
  A row and B column, read from the recorded operand bytes as signed or unsigned, plus the old D
  value when accumulation is enabled, wrapped to 32 bits; with saturation a value is derived only
  when no partial sum can leave the s32 range. Every kind reads operand element `(r, k)` as the
  `kind.width` bytes at `(r * kind.k + k) * kind.width` of the row-major operand (`elementBytes`),
  with `k < kind.k`. The kind::i8 value is computed from the bit patterns of the operand bytes
  (THREAD-BYTES), and an unknown byte, or a byte without a bit pattern, gives no value. With
  saturation the products alone never leave the s32 range, and when a partial sum can leave it, the
  clamped value depends on the unspecified summation order and no value is derived. Core has no
  numerical profile for kind::f16, kind::tf32 and kind::f8f6f4, and the first selected profile gives
  their arithmetic. The floating kinds get values only from a selected numerical profile, and the
  old value of an accumulating MMA comes from an earlier MMA result or store that is its accumulator
  source.

Defs: TcMma.byteInt, TcMma.s32, TcMma.elementBytes, TcMma.mmaTerms, TcMma.SaturationFree,
  TcMma.accumulateInt, TcMma.intEval, TcMma.eval, TcMma.Result, TcMma.Wrote

Source:
- §9.7.18.10.10.1 (D = A*B + enable-input-d*C), Table 48 (kind::i8: s8 or u8 inputs, s32 D), Table
    51 bit 3 (saturate)
- EXT-TCI8-WRAP (integer overflow); explicitly selected numerical profile

Direction: reading

Applies: Dense MMA result cells with recorded operand observations

Premises: Actual issue, unmasked physical cell, exact recorded A/B observations and successful
  evaluation. Accumulation additionally requires the old value, a finite MMA derivation or a stored
  word, and an accumulator read source (`ReadSource .acc`, DEP-TC-READ-SOURCE) for the same physical
  cell. Disabled accumulation needs no prior D. Enabled
  accumulation cannot invent a zero and cannot justify a value by itself or circularly.

Effect: This contract derives a result. It asserts no completion and filters no execution.

### EXT-TCI8-WRAP — integer accumulation wraps modulo 2^32

Statement: For `tcgen05.mma.kind::i8` without the saturate bit the s32 accumulator wraps modulo 2^32
  on overflow, whatever the order of accumulation. With the saturate bit the model derives a value
  only when no partial sum in any order overflows.

Source:
- §9.7.16.5.14: "The .satfinite qualifier indicates that on overflow, the accumulated value is
    limited to the range MIN_INT32 .. MAX_INT32 ... If .satfinite is not specified, the accumulated
    value is wrapped instead"
- §9.7.17.5.2: "The .satfinite qualifier indicates that on overflow, the accumulated value is
    limited to the range MIN_INT32 .. MAX_INT32 ... If .satfinite is not specified, the accumulated
    value is wrapped instead"
- §9.7.18.10.10.1 and Table 51 bit 3: "Saturate for integer types"

Why it is not spec text: The sentences are in the `mma` and `wgmma` descriptions, and the model
  reads them as the behaviour of the 5th-generation integer MMA. The `tcgen05.mma` text states the
  saturate bit and the s32 D type but no overflow behaviour.

Direction: reading

Effect: The wrapped value is derived for a tcgen05 accumulation the text leaves open. If hardware
  clamped or wrapped differently, `Post` could differ from the result. Disclosed by every kernel
  whose statement names `MmaKind.i8`: TcGemm.

### EXT-TCTF32 — FP32 inputs of kind::tf32

Statement: The FP32 values in the 32-bit containers of a `kind::tf32` operand are converted to TF32
  by truncating their low 13 mantissa bits.

Why it is not spec text: The ISA calls kind::tf32 inputs TF32 without saying how the 32-bit
  containers' FP32 values are converted.

Evidence: On a B200 `Tools/probes/tcgen05_ws_ts_tf32.ptx` (`tcgen05.mma.ws` with A in Tensor Memory,
  M = 128, N = 64, K = 8, inputs with bits below the TF32 mantissa in A, and with `lowb` in B, every
  product and sum exact in FP32) matched truncation of the low 13 mantissa bits on all 8192 outputs
  (five runs), round-to-nearest-even on about 8% and no conversion on under 1%.

Direction: reading

Effect: The FP32 input values of a tf32 MMA are fixed by this truncation. If the hardware converts
  differently, the products differ from the ones proven. Disclosed by every kernel whose statement
  names `MmaKind.tf32`: none.
-/

/-- The value of an operand byte of an integer MMA, unsigned or two's complement: its bits
(THREAD-BYTES), whatever the stored value's type. An unknown byte, or a byte of a value
without a bit pattern, has none. -/
def byteInt (signed : Bool) : Option Byte → Option Int
  | some b => (byteBits b).map fun u => if signed ∧ 128 ≤ u then (u : Int) - 256 else u
  | none => none

/-- A 32-bit result as a register value: the low 32 bits of `v`, two's complement. -/
def s32 (v : Int) : Value := .bits 32 (BitVec.ofNat 64 (v % 2 ^ 32).toNat)

/-- The bytes of element `k` of row `row` of an operand read by an MMA of `kind`: the operand
is row-major with `kind.k` elements of `kind.width` bytes per row, whatever its physical
layout. An element beyond the bytes read is a short list. -/
def elementBytes (kind : Kind) (bs : List (Option Byte)) (row k : Nat) : List (Option Byte) :=
  (bs.drop ((row * kind.k + k) * kind.width)).take kind.width

/-- The `kind.k` products of element `(i, j)` of `A * B` for an integer `kind`: `ab` holds `A`
row by row, `bb` holds `B` column by column. A floating kind has none. -/
def mmaTerms (kind : Kind) (ab bb : List (Option Byte)) (i j : Nat) : Option (List Int) :=
  match kind with
  | .i8 sa sb _ =>
    (List.range kind.k).mapM fun k => do
      let x ← byteInt sa ((elementBytes kind ab i k).headD none)
      let y ← byteInt sb ((elementBytes kind bb j k).headD none)
      pure (x * y)
  | _ => none

/-- No partial sum of `c` and any subset of `terms` leaves the s32 range. -/
def SaturationFree (c : Int) (terms : List Int) : Prop :=
  -(2 ^ 31 : Int) ≤ c + (terms.map (min 0)).sum ∧ c + (terms.map (max 0)).sum ≤ 2 ^ 31 - 1

instance saturationFreeDecidable (c : Int) (terms : List Int) :
    Decidable (SaturationFree c terms) := by
  unfold SaturationFree; infer_instance

/-- Integer accumulation of products: the old D word is added modulo 2^32 when accumulating;
with saturation, only when no partial sum can overflow. -/
def accumulateInt (saturate accumulate : Bool) (terms : Option (List Int)) (old : Option Value) :
    Exec Value :=
  match terms, accumulate, old with
  | none, _, _ => .error .uninitialized
  | some ts, false, _ => .ok (s32 ts.sum)
  | some ts, true, some (.bits 32 c) =>
    if saturate then
      let ci := (BitVec.ofNat 32 c.toNat).toInt
      if SaturationFree ci ts then .ok (s32 (ci + ts.sum)) else .error .noRule
    else .ok (s32 (c.toNat + ts.sum))
  | some _, true, _ => .error .uninitialized

/-- The exact dense integer MMA. -/
def intEval (signedA signedB saturate accumulate : Bool) (a b : List (Option Byte))
    (old : Option Value) (row col : Nat) : Exec Value :=
  accumulateInt saturate accumulate (mmaTerms (.i8 signedA signedB saturate) a b row col) old

/-- The value of element (`row`, `col`) of D from the recorded A and B bytes and the old D
value: exact integer arithmetic for `kind::i8`, and for the floating kinds the first selected
numerical profile that gives a value. -/
def eval (A : List Assumption) (d : Descriptor) (accumulate : Bool)
    (a b : List (Option Byte)) (old : Option Value) (row col : Nat) : Exec Value :=
  match d.kind with
  | .i8 signedA signedB saturate =>
    intEval signedA signedB saturate accumulate a b old (operandRow d row col) col
  | .f16 .. | .tf32 | .f8f6f4 .. =>
    (A.findSome? fun profile => profile.mmaRule d accumulate a b old row col).getD (.error .noRule)

/-- A logical result may be derived before its asynchronous completion is observed.
Publication to a consumer is a separate obligation. -/
inductive Result (L : Launch) (A : List Assumption) (X : Execution) :
    EvId → Cell → Value → Prop where
  | overwrite {i d s mask row col cell operands value}
      (issue : X.MmaIssue i d s false mask)
      (position : writeCell s d mask row col = some cell)
      (reads : X.async.mmaOperands i = some operands)
      (arithmetic : eval A s.descriptor false operands.a operands.b none row col = .ok value) :
      Result L A X i cell value
  | accumulate {i d s mask row col cell operands value source old}
      (issue : X.MmaIssue i d s true mask)
      (position : writeCell s d mask row col = some cell)
      (reads : X.async.mmaOperands i = some operands)
      (previous : Result L A X source cell old)
      (provenance : ReadSource L X .acc source i cell)
      (arithmetic : eval A s.descriptor true operands.a operands.b (some old) row col = .ok value) :
      Result L A X i cell value
  | accumulateStored {i d s mask row col cell operands value source old}
      (issue : X.MmaIssue i d s true mask)
      (position : writeCell s d mask row col = some cell)
      (reads : X.async.mmaOperands i = some operands)
      (previous : StoreValue L X source cell old)
      (provenance : ReadSource L X .acc source i cell)
      (arithmetic : eval A s.descriptor true operands.a operands.b (some old) row col = .ok value) :
      Result L A X i cell value

/-! ## DEP-TMEM-SHIFT-VALUE — the words tcgen05.shift leaves
Statement: A `tcgen05.shift` leaves in a cell the word that the next lane of its chunk (index + 1)
  held when the shift read it: the value of an MMA result, a store or a copy of that cell that is
  ordered before the shift, that no other write of the cell follows before the shift has completed,
  and that no release of the allocation separates from the shift. A cell whose source is itself
  the result of a shift gets no value. The shift does not write the last lane of a 32-lane chunk,
  which keeps its word (THREAD-TC-SHIFT-CELLS).

Defs: TcMma.ShiftSource, TcMma.ShiftValue

Source:
- §9.7.18.9.3 (tcgen05.shift)
- §9.7.18.6.2.1.1: "Completion of the following instruction’s asynchronous operations is observed
    through the mbarrier based waiting mechanism: tcgen05.mma tcgen05.cp tcgen05.shift"
- THREAD-TC-SHIFT-CELLS
- EXT-TCSHIFT

Why it is not spec text: The text does not say when, between issue and completion, the shift reads
  its rows. A write of a source cell that is not ordered before the shift or after its completion
  therefore leaves the moved word without a value.

Direction: stricter

Applies: Every represented tcgen05.shift

Premises: The source cell is the cell of the next lane (index + 1) in the same chunk
  (`TcShift.source`), and its source write is ordered before the shift and stable until the shift
  completes (the read source of a shift read, `ReadSource .shift`, DEP-TC-READ-SOURCE).

Effect: A value relation used by DEP-TC-LOAD-VALUE; a load of a shifted cell without such a source
  has no read source, which ERR-TMEM-READ-SOURCE rejects. The model derives no value through two
  shifts in a row, since the source of a shift must be an MMA result, a store or a copy; this choice
  only rejects programs.

Review: The pipelined pairs of §9.7.18.6.2 that involve `tcgen05.shift` are not used: such a pair is
  ordered only by completion.
-/

/-- `source` is the write of `from` whose word shift `sh` moves: ordered before the shift, every
other write of `from` before the source or after the shift has completed, and no release of the
allocation between them. -/
def ShiftSource (L : Launch) (X : Execution) (source sh : EvId) (cell «from» : Cell) : Prop :=
  ShiftCell X sh cell ∧ TcShift.source cell = «from» ∧ ShiftReadCell X sh «from» ∧
    ReadSource L X .shift source sh «from»

/-- Shift `sh` leaves `value` in `cell`: the value its source left in the cell of the next lane. -/
def ShiftValue (L : Launch) (A : List Assumption) (X : Execution) (sh : EvId) (cell : Cell)
    (value : Value) : Prop :=
  ∃ source «from», ShiftSource L X source sh cell «from» ∧
    (Result L A X source «from» value ∨ StoreValue L X source «from» value ∨
      CpValue X source «from» value)

/-- The value a Tensor Memory write leaves in `cell`. -/
def Wrote (L : Launch) (A : List Assumption) (X : Execution) (source : EvId) (cell : Cell)
    (value : Value) : Prop :=
  Result L A X source cell value ∨ StoreValue L X source cell value ∨ CpValue X source cell value ∨
    ShiftValue L A X source cell value

end
end PTX.TcMma
