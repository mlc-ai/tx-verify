-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Access
public import Core.Sync.MatrixLayout

@[expose] public section

/-!
# Warp-level matrix instructions: what one thread does

The events of `ldmatrix`, `stmatrix`, `movmatrix`, `mma` and `mma.sp` in one thread: the row a
thread reads or writes and the bytes it contributes to and receives from the warp's instance.

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

/-! ## THREAD-MATRIX — matrix loads, stores and the register transpose

Statement: In a CTA whose size is a multiple of 32, `ldmatrix` makes each thread that supplies a row
  address read the 16 bytes of its row, as one weak read, and then take part in the warp's instance
  with those bytes; it writes the bytes it receives to its destination registers. `stmatrix` makes
  each thread take part with the bytes of its source registers and then write the 16 bytes it
  receives to the row whose address it supplies. `movmatrix` takes part with its source register and
  writes what it receives to its destination. A row address must lie in the thread's own
  `.shared::cta` window and be aligned to 16 bytes.

Defs: byteValue, valueByte, matrixRowLoc, regBytes, afterMatrix, matrixMoveTmpl, matrixTmpl

Source:
- §9.7.16.5.15: "Collectively load one or more matrices across all threads in a warp from the
    location indicated by the address operand p , from .shared state space into destination register
    r ."
- §9.7.16.5.15: "If the generic address doesn’t fall in .shared state space, then the behavior is
    undefined."
- §9.7.16.5.15: "Each address corresponds to the start of a matrix row."
- §9.7.16.5.15: "When reading 8x8 matrices, a group of four consecutive threads loads 16 bytes. The
    matrix addresses must be naturally aligned accordingly."
- §9.7.16.5.15: "For .b6x16_p32 format source data is 16 unsigned 6-bit elements with 32 bits
    padding."
- §9.7.16.5.15: "For .b4x16_p64 format source data is 16 unsigned 4-bit elements with 64 bits
    padding."
- §9.7.16.5.15: "The ldmatrix instruction is treated as a weak memory operation in the Memory
    Consistency Model ."
- §9.7.16.5.16: "When storing 8x8 matrices, a group of four consecutive threads stores 16 bytes."
- §9.7.16.5.16: "The stmatrix instruction is treated as a weak memory operation in the Memory
    Consistency Model ."
- §9.7.16.5.17: "Operands a and d are 32-bit registers containing fragments of the input matrix and
    the resulting matrix respectively."
- EXT-MATRIX-FIGURES

Direction: reading

Applies: The forms whose rule is THREAD-MATRIX (`MatrixInstr.rule`)

Premises: The CTA size is a multiple of 32, the row address is in the thread's own `.shared::cta`
  window and aligned to 16 bytes, and the source registers hold 32-bit values.

Effect: Event production: a read or write of the thread's row (THREAD-ACCESS events) and a matrix
  event (DEP-WARP-MATRIX). The rows of matrix `k` are supplied by threads `rows k` to `rows (k + 1)
  - 1` (`MatrixMove.rows`); the other threads supply no address, read no row and take part with no
    bytes.
  Every row of a supported form is 16 bytes: eight 16-bit elements, sixteen 8-bit elements, or
  sixteen 6-bit or 4-bit elements with their padding. Between the read and the matrix event of
  `ldmatrix`, and between the matrix event and the write of `stmatrix`, the thread keeps the row's
  bytes in `TState.acc`, each as the one-byte slice of its value (`byteValue`), at sub-step 1. A row
  with an unknown byte makes the reading thread fault (`uninitialized`): every byte of a row of a
  form with known values reaches some register, where the load would fault (THREAD-BYTES). A
  received list that does not rebuild into the destination registers faults the same way. A generic
  address must be a pointer into the thread's own shared memory (THREAD-ADDR); any other address is
  `badValue` (stricter for a `.shared::cluster` address of the own CTA, which the text does not
  mention), and a row address that is not a multiple of 16 is `misaligned`. In a CTA whose size is
  not a multiple of 32 the instructions have no rule, as for `shfl.sync`: the text does not say what
  the missing lanes of the last warp supply.
-/

/-- A memory byte as a value: the one-byte slice of its stored value. -/
def byteValue (b : Byte) : Value := .slice b.1 b.2 1

/-- The memory byte of a one-byte slice (`byteValue`). -/
def valueByte : Value → Option Byte
  | .slice v k 1 => some (v, k)
  | _ => none

/-- The location of the row whose address the thread supplies: in the thread's own `.shared::cta`
window (THREAD-ADDR) and aligned to 16 bytes. -/
def matrixRowLoc (L : Launch) (g : Nat) (t : TState) (i : MatrixInstr) : Exec Loc := do
  let some a := i.addr | throw .noRule
  let loc ← accessLoc L g t
    { kind := .load, space := i.space, sem := .weak, elem := .int .b 8, addr := a }
  unless loc.space = .shared ∧ loc.cta = g / L.block do throw .badValue
  unless loc.addr % 16 = 0 do throw .misaligned
  pure loc

/-- The bytes of the source operands `os`, each a `w`-bit value, in order. -/
def regBytes (L : Launch) (g : Nat) (t : TState) (w : Nat) (os : List Opnd) :
    Exec (List (Option Byte)) :=
  os.foldlM (fun acc o => do
    let v ← readValue L g t w o
    unless v.bytes = w / 8 do throw .typeMismatch
    pure (acc ++ v.toBytes.map some)) []

/-- The state after a matrix event that received `recv` for the `w`-bit destinations `ds`: each
destination is rebuilt from its bytes (THREAD-BYTES); a list of another length is a
`typeMismatch` fault. -/
def afterMatrix (t : TState) (w : Nat) (ds : List Nat) (recv : List (Option Byte)) : TState :=
  let n := w / 8
  if recv.length = ds.length * n then
    match ((List.range ds.length).map fun r => (recv.drop (r * n)).take n).mapM (rebuild 3) with
    | .ok vs => next (setRegs { t with sub := 0, acc := [] } ds vs)
    | .error f => { t with fault := some f }
  else { t with fault := some .typeMismatch }

/-- The events of a matrix load or store `m` of instruction `i` (THREAD-MATRIX). -/
def matrixMoveTmpl (L : Launch) (g : Nat) (t : TState) (i : MatrixInstr) (m : MatrixMove) :
    Tmpl :=
  let supplier := laneOf L g < m.num * m.rows
  if m.store then
    if t.sub = 0 then
      match regBytes L g t 32 i.srcs with
      | .error f => .ub f
      | .ok own => .matrix (.move m) own fun recv =>
        if supplier then
          if recv.length = 16 ∧ recv.all Option.isSome then
            { t with sub := 1, acc := recv.filterMap fun b => b.map byteValue }
          else { t with fault := some .typeMismatch }
        else next t
    else
      match matrixRowLoc L g t i with
      | .error f => .ub f
      | .ok loc => .write { loc := loc, size := 16 } (t.acc.filterMap valueByte)
          (next { t with sub := 0, acc := [] })
  else if supplier ∧ t.sub = 0 then
    match matrixRowLoc L g t i with
    | .error f => .ub f
    | .ok loc => .read { loc := loc, size := 16 } fun bs =>
        if bs.length = 16 ∧ bs.all Option.isSome then
          { t with sub := 1, acc := bs.filterMap fun b => b.map byteValue }
        else { t with fault := some .uninitialized }
  else
    .matrix (.move m) (if supplier then (t.acc.filterMap valueByte).map some else [])
      (afterMatrix t 32 i.dsts)

/-! ## THREAD-MMA-SYNC — warp-level matrix multiply-accumulate

Statement: In a CTA whose size is a multiple of 32, `mma` and `mma.sp` make each thread take part in
  the warp's instance with the bytes of its A, B and C registers and, for `mma.sp`, of its metadata
  register, and write the bytes it receives to its D registers.

Defs: mmaOwn

Source:
- §9.7.16.5.14: "Operands a and b represent two multiplicand matrices A and B, while c and d
    represent the accumulator and destination matrices, distributed across the threads in warp."
- §9.7.16.6.3: "Operands e and f represent sparsity metadata and sparsity selector respectively."

Direction: equal

Applies: The forms whose rule is THREAD-MMA-SYNC (`MatrixInstr.rule`)

Premises: The CTA size is a multiple of 32 and the source registers hold values of their widths.

Effect: Event production: a matrix event (DEP-WARP-MATRIX) whose received bytes DEP-WARP-MMA gives.
  A and B registers are 64 bits wide for `.f64` and 32 bits otherwise, C and D registers likewise
  for their own types, and the metadata register is 32 bits (`MmaSpec.regBits`).
-/

/-- The bytes an MMA thread contributes: its A and B registers, its C registers and its
metadata register, in operand order. -/
def mmaOwn (L : Launch) (g : Nat) (t : TState) (s : MmaSpec) (srcs : List Opnd) :
    Exec (List (Option Byte)) := do
  let (ra, rb, rc, _) := s.regs
  let ab ← regBytes L g t (MmaSpec.regBits s.types.a) (srcs.take (ra + rb))
  let c ← regBytes L g t (MmaSpec.regBits s.types.c) ((srcs.drop (ra + rb)).take rc)
  let e ← regBytes L g t 32 (srcs.drop (ra + rb + rc))
  pure (ab ++ c ++ e)

/-- The event of a warp-level matrix instruction with a rule (`MatrixInstr.rule`): THREAD-MATRIX
or THREAD-MMA-SYNC; in a CTA whose size is not a multiple of 32, and without a rule, `noRule`. -/
def matrixTmpl (L : Launch) (g : Nat) (t : TState) (i : MatrixInstr) : Tmpl :=
  if L.block % 32 = 0 then
    match i.rule, i.op, i.dsts, i.srcs with
    | some .threadMatrix, .move m, _, _ => matrixMoveTmpl L g t i m
    | some .threadMatrix, .transpose, [d], [a] =>
      match regBytes L g t 32 [a] with
      | .error f => .ub f
      | .ok own => .matrix .transpose own (afterMatrix t 32 [d])
    | some .threadMma, .mma s, ds, srcs =>
      match mmaOwn L g t s srcs with
      | .error f => .ub f
      | .ok own => .matrix (.mma s) own (afterMatrix t (MmaSpec.regBits s.types.d) ds)
    | _, _, _, _ => .ub .noRule
  else .ub .noRule

end

end PTX
