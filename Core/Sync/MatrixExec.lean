-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.Matrix
public import Core.Tc.TcMmaValue

@[expose] public section

/-!
# Warp-level matrix instructions: instances and values

The instance of a warp-level matrix instruction, the bytes each lane receives in it, and the
undefined behaviour of the instance.

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## DEP-WARP-MATRIX — instances of the warp-level matrix instructions

Statement: In each lane of a warp, the n-th warp-level matrix event belongs to the n-th instance of
  the warp, which waits for all 32 lanes. A lane of a matrix load receives the bytes of the rows
  that its registers hold, a lane of a matrix store that supplies a row receives the bytes of that
  row from the registers that hold them, and a lane of `movmatrix` receives the transposed elements.
  A result that cannot be computed is ERR-WARP-MATRIX. A lane that exits before the instance and two
  lanes of the instance that execute different instructions are ERR-ALIGNED-MISMATCH.

Defs: isMatrix, Execution.MatrixK, MatrixInstance, MatrixResult, OpenBytes, MatrixMove.storeByte,
  matrixMoveRecv, transposeRecv, matrixRecv, MatrixOk, matrixOk_of_none

Source:
- §9.7.16.5.15: "The mandatory .sync qualifier indicates that ldmatrix causes the executing thread
    to wait until all threads in the warp execute the same ldmatrix instruction before resuming
    execution."
- §9.7.16.5.15: "For 4-bit or 6-bit data, 8-bit element will have 4 bits or 2 bits of padding
    respectively."
- §9.7.16.5.17: "Each thread in a warp holds a fragment of a column of the result matrix, with
    thread 0 holding the first fragment in register d , and so on."
- THREAD-MATRIX-LAYOUT

Direction: stricter

Applies: Instances of the forms with THREAD-MATRIX and THREAD-MMA-SYNC

Premises: A matrix event exists at a given per-thread ordinal.

Effect: Execution constraint in `Consistent.matrix`; the undefined behaviour of an instance is
  ERR-WARP-MATRIX.
  `MatrixK` numbers the matrix events of a thread. The instance of the `n`-th events in the warp of
  thread `g` (`MatrixInstance`) assigns each lane the bytes it contributes; it exists when every
  lane of the warp performs its `n`-th matrix event at the same source position with the same
  operation. A lane's received bytes are `matrixRecv` of the instance: for a matrix load the bytes
  of the rows at the positions `MatrixMove.source` gives, for a matrix store the bytes of the
  supplier's row from the registers `MatrixMove.source` maps to it (`MatrixMove.storeByte`), for
  `movmatrix` the bytes `transposeSource` gives, and for an MMA the bytes of DEP-WARP-MMA. The
  `.b8x16` loads from a 6-bit or 4-bit source format have open results (`OpenBytes`): each received
  byte is a byte of an 8-bit integer, because the text gives neither the position of a source
  element in its row nor the position of the padding in the 8-bit element. Every lane of the warp
  either takes part or has exited (`Execution.ExitedShort`). An exited lane, lanes of one instance
  at different source positions and lanes with different operations are undefined behaviour by
  ERR-ALIGNED-MISMATCH. An instance orders no memory
  operation: the rows are accessed by the threads' own reads and writes (THREAD-MATRIX). Its waiting
  is the need of each event (`KindNeeds`, DEP-ORDER): every lane's `n`-th matrix event, or its exit
  short of it, is a witness of the return of every event of the instance, an edge of the execution
  layer only, as for the masked warp collectives (DEP-WARP-INSTANCE). A lane's short exit fills its
  need so that the instance exists and ERR-ALIGNED-MISMATCH reports the undefined behaviour.
-/

/-- A warp-level matrix event. -/
def isMatrix : Event → Bool
  | ⟨_, .matrix ..⟩ => true
  | _ => false

namespace Execution

variable (X : Execution)

/-- `e` is the `n`-th matrix event of its thread. -/
def MatrixK (e : EvId) (n : Nat) : Prop :=
  (∃ ev, X.get e = some ev ∧ isMatrix ev = true) ∧ ((X.tr e.1).take e.2).countP isMatrix = n

end Execution

/-- The instance of the `n`-th matrix events in the warp of thread `g`: every lane performs its
`n`-th matrix event at position `pc` with operation `op`, contributing `parts lane`. -/
def MatrixInstance (X : Execution) (g n pc : Nat) (op : MatrixOp)
    (parts : Nat → List (Option Byte)) : Prop :=
  ∀ lane < 32, ∃ j recv,
    X.get (g - laneOf L g + lane, j) = some ⟨pc, .matrix op (parts lane) recv⟩ ∧
    X.MatrixK (g - laneOf L g + lane, j) n

/-- What a lane receives: these bytes, or any `n` bytes of 8-bit integers (`open_`). -/
inductive MatrixResult where
  | bytes (bs : List (Option Byte))
  | open_ (n : Nat)

/-- `recv` is `n` bytes, each the byte of an 8-bit integer. -/
def OpenBytes (n : Nat) (recv : List (Option Byte)) : Prop :=
  recv.length = n ∧ ∀ b ∈ recv, ∃ x, b = some (.bits 8 x, 0)

/-- Byte `k` of the row that lane `row` supplies to a matrix store: the register byte that
`MatrixMove.source` maps to it. -/
def MatrixMove.storeByte (m : MatrixMove) (parts : Nat → List (Option Byte)) (row k : Nat) :
    Option Byte :=
  let n := m.num * m.regsPerMatrix * 4
  match ((List.range 32).flatMap fun l => (List.range n).map (l, ·)).find?
      (fun (l, x) => m.source l (x / 4) (x % 4) == (row, k)) with
  | some (l, x) => (parts l)[x]?.join
  | none => none

/-- What lane `l` receives in an instance of the matrix load or store `m`. -/
def matrixMoveRecv (m : MatrixMove) (parts : Nat → List (Option Byte)) (l : Nat) :
    MatrixResult :=
  let n := m.num * m.regsPerMatrix * 4
  if m.store then
    if l < m.num * m.rows then .bytes ((List.range 16).map (m.storeByte parts l)) else .bytes []
  else
    match m.fmt with
    | .b8x16 _ => .open_ n
    | _ => .bytes ((List.range n).map fun x =>
        let (row, k) := m.source l (x / 4) (x % 4)
        (parts row)[k]?.join)

/-- What lane `l` receives in an instance of `movmatrix`. -/
def transposeRecv (parts : Nat → List (Option Byte)) (l : Nat) : List (Option Byte) :=
  (List.range 4).map fun b =>
    let (src, k) := transposeSource l b
    (parts src)[k]?.join

/-! ## DEP-WARP-MMA — the values of `mma` and `mma.sp`

Statement: Each lane of an `mma` or `mma.sp` instance receives its D elements, each the sum of the
  products of its A row and B column plus its C element, all read from the registers that hold them.
  Integer products are exact and their sum wraps modulo 2^32, or with `.satfinite` has a value only
  when no partial sum leaves the s32 range; single-bit products are the bit operation of the two
  bits. Floating results come only from a kernel assumption. The non-zero elements of a sparse A
  meet the B rows their metadata selects, and invalid metadata or an invalid selector is undefined
  behaviour.

Defs: mmaElem, findFrag, operandElem, metaField, elemInt, mmaValue, mmaRecv

Source:
- §9.7.16.5.14: "Perform a MxNxK matrix multiply and accumulate operation, D = A*B+C , where the A
    matrix is MxK , the B matrix is KxN , and the C and D matrices are MxN ."
- §9.7.16.5.14: "mma.xor.popc and mma.and.popc computes the XOR, AND respectively of a k-bit row of
    A with a k-bit column of B, then counts the number of set bits in the result ( popc ). This
    result is added to the corresponding element of C and written into D."
- §9.7.16.5.14: "The .satfinite qualifier indicates that on overflow, the accumulated value is
    limited to the range MIN_INT32 .. MAX_INT32"
- §9.7.16.5.14: "If .satfinite is not specified, the accumulated value is wrapped instead."
- §9.7.16.5.14: "The accumulation order, rounding and handling of subnormal inputs are unspecified."
- §9.7.16.5.14: "Precision of the element-wise multiplication and addition operation is identical to
    that of .f64 precision fused multiply-add."
- §9.7.16.6.1: "Values 0b0000 , 0b0101 , 0b1010 , 0b1111 are invalid values for metadata and will
    result in undefined behavior."
- §9.7.16.6.1: "0b1110 and 0b0100 are the only meaningful index values; any other values result in
    undefined behavior."
- §9.7.16.6.1: "Hence, the sparsity selector must be either 0 (threads T0, T1) or 1 (threads T2,
    T3); any other value results in undefined behavior."
- §9.7.16.6.1: "Hence, the sparsity selector in this case must be 0. Any other value of sparsity
    selector results in an undefined behavior."
- §9.7.16.6.3: "Instruction mma.sp::ordered_metadata requires the indices in the sparsity metadata
    to be sorted in an increasing order starting from LSB, otherwise behavior is undefined."
- THREAD-MATRIX-LAYOUT
- ASM-INTERFACE

Direction: stricter

Applies: Instances of the forms with THREAD-MMA-SYNC

Premises: The instance exists (DEP-WARP-MATRIX).

Effect: The bytes each lane receives (`matrixRecv`); a computation that fails is undefined behaviour
  (`MatrixUnsafe`, ERR-WARP-MATRIX). `mmaRecv` computes, for each element of the lane's D fragment
  (`MmaSpec.fragCD`), its row, column and computation, finds every A, B and C element it needs in
  the lane and register that hold it (`findFrag`, THREAD-MATRIX-LAYOUT) and reads it from that
  lane's bytes (`mmaElem`): a floating element is rebuilt from its bytes (THREAD-BYTES), and an
  integer element is the bits of its bytes or, for a 4-bit or 1-bit element, of its part of a byte.
  For `mma.sp` the `k/2` stored elements of the A row are paired with the B rows `MmaSpec.sparseCol`
  selects from the metadata field of their chunk (`metaField`), and the zeros of A contribute
  nothing. An integer element is signed or unsigned by its type (`elemInt`) and C is a signed 32-bit
  integer. With `.satfinite` the clamped sum depends on the unspecified accumulation order when a
  partial sum leaves the s32 range, so the model derives a value only when no partial sum does (as
  for `tcgen05.mma`, `TcMma.SaturationFree`), and otherwise there is no rule (stricter). The
  floating types, `.f64` included, have no Core arithmetic: the first assumption whose
  `matrixMmaRule` gives a value for the element types supplies it (ASM-INTERFACE), and without one
  the instance is undefined behaviour (`noRule`). The D elements are packed into the D registers two
  to a register for `.f16` and one otherwise, the lower element first.
-/

/-- Element `i` of type `ty` of a fragment whose registers start at byte `off` of `bs`: a
floating element rebuilt from its bytes, an integer element of 8 bits or more as the bits of its
bytes, a narrower element as its bits. -/
def mmaElem (bs : List (Option Byte)) (off : Nat) (ty : DType) (i : Nat) : Exec Value :=
  let w := ty.width
  if 8 ≤ w then
    let el := (bs.drop (off + i * (w / 8))).take (w / 8)
    match ty with
    | .int .. => match littleEndianBits el with
      | some n => if el.length = w / 8 then pure (.bits w (BitVec.ofNat 64 n)) else throw .noRule
      | none => throw .uninitialized
    | _ => rebuild 3 el
  else
    match bs[off + i * w / 8]? with
    | some (some b) => match byteBits b with
      | some n => pure (.bits w (BitVec.ofNat 64 (n / 2 ^ (i * w % 8) % 2 ^ w)))
      | none => throw .typeMismatch
    | some none => throw .uninitialized
    | none => throw .noRule

/-- The lane and element index whose fragment element `f` places at `pos`, searching `n`
elements in each of the 32 lanes. -/
def findFrag (f : Nat → Nat → Nat × Nat × Nat) (n : Nat) (pos : Nat × Nat × Nat) :
    Option (Nat × Nat) :=
  ((List.range 32).flatMap fun l => (List.range n).map (l, ·)).find? fun (l, i) => f l i == pos

/-- The element at `pos` of an operand with fragment layout `f` of `n` elements per lane, type
`ty` and registers at byte `off`. -/
def operandElem (parts : Nat → List (Option Byte)) (f : Nat → Nat → Nat × Nat × Nat) (n off : Nat)
    (ty : DType) (pos : Nat × Nat × Nat) : Exec Value :=
  match findFrag f n pos with
  | some (l, i) => mmaElem (parts l) off ty i
  | none => throw .noRule

/-- The 4-bit metadata field at bit `bit` of the metadata register at byte `off` of `bs`. -/
def metaField (bs : List (Option Byte)) (off bit : Nat) : Exec Nat :=
  match littleEndianBits ((bs.drop off).take 4) with
  | some n => pure (n / 2 ^ bit % 16)
  | none => throw .uninitialized

/-- The integer a `w`-bit element of kind `k` denotes (`intOf` of its bit pattern). -/
def elemInt (k : IType) (w : Nat) (v : Value) : Exec Int :=
  match v.bitPattern with
  | some n => pure (intOf k w (BitVec.ofNat 64 n))
  | none => throw .typeMismatch

/-- One D element from its A row `as`, B column `bs` and C element `c`. -/
def mmaValue (A : List Assumption) (s : MmaSpec) (as bs : List Value) (c : Value) : Exec Value :=
  match s.types.a, s.types.b with
  | .int ka wa, .int kb wb => do
    let terms ← (as.zip bs).mapM fun (x, y) => do
      let x ← elemInt ka wa x
      let y ← elemInt kb wb y
      pure (match s.bitOp with
        | some .and => x * y
        | some .xor => if x = y then 0 else 1
        | none => x * y)
    let c ← elemInt .s 32 c
    if s.satfinite then
      if TcMma.SaturationFree c terms then pure (TcMma.s32 (c + terms.sum)) else throw .noRule
    else pure (TcMma.s32 (c + terms.sum))
  | _, _ => (A.findSome? fun a => a.matrixMmaRule s.types as bs c).getD (throw .noRule)

/-- The bytes of lane `l`'s D registers in an instance of MMA `s` with contributions `parts`. -/
def mmaRecv (A : List Assumption) (s : MmaSpec) (parts : Nat → List (Option Byte)) (l : Nat) :
    Exec (List (Option Byte)) := do
  let (ea, eb, ec, ed) := s.elems
  let (ra, rb, rc, rd) := s.regs
  let ab := MmaSpec.regBits s.types.a / 8
  let offC := (ra + rb) * ab
  let offE := offC + rc * (MmaSpec.regBits s.types.c / 8)
  let a := operandElem parts s.fragA ea 0 s.types.a
  let b := operandElem parts s.fragB eb (ra * ab) s.types.b
  let vals ← (List.range ed).mapM fun i => do
    let (q, row, col) := s.fragCD s.types.d l i
    let pairs ← match s.sparse with
      | none => (List.range s.k).mapM fun k => do pure (← a (q, row, k), ← b (q, k, col))
      | some (ordered, sel) => do
        let fields := s.k / s.metaCols
        unless (fields = 4 ∧ sel < 4) ∨ (fields = 8 ∧ sel < 2) ∨ (fields = 16 ∧ sel = 0) do
          throw .badValue
        (List.range s.kc).mapM fun c => do
          let (ml, bit) := s.metaLoc sel row (c / (s.metaCols / 2))
          let f ← metaField (parts ml) offE bit
          let some k := s.sparseCol ordered f c | throw .badValue
          pure (← a (0, row, c), ← b (0, k, col))
    let cv ← operandElem parts (s.fragCD s.types.c) ec offC s.types.c (q, row, col)
    let v ← mmaValue A s (pairs.map (·.1)) (pairs.map (·.2)) cv
    unless v.bytes = s.types.d.width / 8 do throw .typeMismatch
    pure v
  let per := MmaSpec.perReg s.types.d
  let regs := (List.range rd).map fun r => match (vals.drop (per * r)).take per with
    | [lo, hi] => Value.pair lo hi
    | v :: _ => v
    | [] => .bits 0 0
  pure (regs.flatMap fun v => v.toBytes.map some)

/-- What lane `l` receives in an instance of operation `op` with contributions `parts`. -/
def matrixRecv (A : List Assumption) (op : MatrixOp) (parts : Nat → List (Option Byte))
    (l : Nat) : Exec MatrixResult :=
  match op with
  | .move m => pure (matrixMoveRecv m parts l)
  | .transpose => pure (.bytes (transposeRecv parts l))
  | .mma s => .bytes <$> mmaRecv A s parts l

/-- Every matrix event received what `matrixRecv` gives for its instance. That every lane of the
warp takes part or has exited is the need of the event (`KindNeeds`, DEP-ORDER). -/
def MatrixOk (A : List Assumption) (X : Execution) : Prop :=
  ∀ g i pc op own recv n, X.get (g, i) = some ⟨pc, .matrix op own recv⟩ → X.MatrixK (g, i) n →
    ∀ parts, MatrixInstance L X g n pc op parts →
      match matrixRecv A op parts (laneOf L g) with
      | .ok (.bytes bs) => recv = bs
      | .ok (.open_ m) => OpenBytes m recv
      | .error _ => True

/-- An execution without matrix events satisfies DEP-WARP-MATRIX (the new `Consistent.matrix` field
holds for every execution of a kernel without warp-level matrix instructions). -/
theorem matrixOk_of_none {A : List Assumption} {X : Execution}
    (h : ∀ e ev, X.get e = some ev → isMatrix ev = false) : MatrixOk L A X := by
  intro g i pc op own recv n hget _
  have := h _ _ hget
  simp [isMatrix] at this

/-! ## ERR-WARP-MATRIX — an instance whose result cannot be computed
Statement: An execution is unsafe when a lane of an instance of a warp-level matrix instruction
  receives a result that cannot be computed.

Defs: MatrixUnsafe, not_matrixUnsafe_of_none

Source:
- DEP-WARP-MATRIX (the instance and the result of each lane)
- DEP-WARP-MMA (the quoted undefined behaviour of invalid sparse metadata and selectors)
- §9.7.16.6.1: "Values 0b0000 , 0b0101 , 0b1010 , 0b1111 are invalid values for metadata and will
    result in undefined behavior."
- §9.7.16.6.1: "Hence, the sparsity selector in this case must be 0. Any other value of sparsity
    selector results in an undefined behavior."
- modelling choice: a lane result that the model cannot compute (an unknown byte, a missing
    numerical rule) is undefined behaviour of the instance; the text states undefined behaviour
    only for invalid sparse metadata and selectors (§9.7.16.6.1, quoted above)

Direction: stricter

Applies: Instances of the forms with THREAD-MATRIX and THREAD-MMA-SYNC

Premises: The instance exists (DEP-WARP-MATRIX).

Effect: Safety rejection (part of Unsafe). A result that cannot be computed (an unknown byte, a
  missing numerical rule, invalid sparse metadata) is undefined behaviour of the instance.
-/
/-- An instance of a matrix event whose lane result cannot be computed. -/
def MatrixUnsafe (A : List Assumption) (X : Execution) : Prop :=
  ∃ g i pc op own recv n, X.get (g, i) = some ⟨pc, .matrix op own recv⟩ ∧ X.MatrixK (g, i) n ∧
    ∃ parts f, MatrixInstance L X g n pc op parts ∧ matrixRecv A op parts (laneOf L g) = .error f

/-- An execution without matrix events has no undefined matrix instance (the disjunct
`MatrixUnsafe` of `Unsafe` is false). -/
theorem not_matrixUnsafe_of_none {A : List Assumption} {X : Execution}
    (h : ∀ e ev, X.get e = some ev → isMatrix ev = false) : ¬ MatrixUnsafe L A X := by
  rintro ⟨g, i, pc, op, own, recv, n, hget, -⟩
  have := h _ _ hget
  simp [isMatrix] at this

end

end PTX
