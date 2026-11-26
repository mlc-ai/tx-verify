-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Matrix.Instance
public import Lemmas.Matrix.Move
public import Assumption.IdealReal
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Warp-level MMA over the reals: `mma.sync.aligned.m16n8k16.row.col.f32.bf16.bf16.f32`

A proof tool, generic over the kernel. One instance of the bf16 tensor-core multiply-accumulate
`D = A · B + C` (`mma16`: `A` is 16×16, `B` is 16×8, `C` and `D` are 16×8; A and B elements are
bf16, C and D elements are f32), under an assumption list whose rule for this MMA is the
ideal-real one (`IdealMma`: the first assumption that gives the element types a
`matrixMmaRule` is `Assumption.idealReal` with these types in `warpMma`, ASM-IDEAL). Only this
form is covered; the statements are not generic in `MmaSpec`.

**Who holds what** (lane `l = 4 g + t`, `g = l / 4`, `t = l % 4`; a register of A or B holds two
bf16 elements, low half first; a register of C or D one f32 element):

| operand | registers per lane | register `r`, half `h` holds | defs |
| --- | --- | --- | --- |
| A | 4 | `a (g + 8 (r % 2)) (2 t + h + 8 (r / 2))` | `aRow`, `aCol` |
| B | 2 | `b (8 r + 2 t + h) g` | `bRow`, `bCol` |
| C, D | 4 | `c (g + 8 (r / 2)) (2 t + r % 2)` | `cRow`, `cCol` |

Conversely (`aPos`, `bPos`, `cPos`): `a i k` is in lane `4 (i % 8) + k % 8 / 2`, register
`2 (k / 8) + i / 8`, half `k % 2`; `b k j` in lane `4 j + k % 8 / 2`, register `k / 8`, half
`k % 2`; `c i j` and `d i j` in lane `4 (i % 8) + j / 2`, register `2 (i / 8) + j % 2`.
These agree with Core's `MmaSpec.fragA`, `fragB`, `fragCD` (`fragA_eq`, `fragB_eq`, `fragCD_eq`).
In the fragment layout of `Lemmas/Matrix/Move.lean` the A registers hold the four 8×8 tiles of
`a` (`aTiles`, `aFrag_eq`: what a plain `ldmatrix.x4` of the tiles' rows loads) and the B
registers the transposes of the 8×8 tiles of `b` (`bTiles`, `bFrag_eq`: what `ldmatrix.x4.trans`
of the tiles' rows loads).

**Results.**
* `mmaRecv_eq`, `matrixRecv_mma`: when the registers of the 32 lanes hold real matrices `a`, `b`
  and `c` (`Operands`: A and B registers are packed pairs of bf16 payloads, a C register is any
  32-bit value an f32 operand reads as the number, `F32Reg`: a payload `.float .f32 x`, or the
  zero word `.bits 32 0` of a cleared accumulator), each lane receives the 16 bytes of its four
  D elements `c i j + ∑ k < 16, a i k * b k j` (`mmaReal`, `outParts`).
* `mma_recv`, `mma_event`: the same for the events of a consistent execution; `mma_ne_error`:
  such an instance has a defined result in every lane.
* `afterMatrix_mma`: the lane's four D registers then hold `.float .f32 (d i j)` at the positions
  `cRow`, `cCol`.
* `mmaOwn_mma16`, `matrixTmpl_mma16`: the bytes a thread contributes, from the values of its
  ten source registers, and its event.

How Core reads the operands: the contributed bytes of a register holding `.pair lo hi` are the
two bytes of `lo` and then the two bytes of `hi`; `mmaElem` rebuilds each bf16 element from its
two bytes, which gives back the payload. The model has no floating arithmetic of its own for
this instruction; the value is `idealWarpMma`'s exact real sum, without rounding.
-/

namespace PTX.WarpMatrix

open PTX.Assumption

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The element types of `…f32.bf16.bf16.f32`: A and B are bf16, C and D are f32. -/
def bfTypes : MmaTypes := ⟨.float .bf16, .float .bf16, .float .f32, .float .f32, none⟩

/-- `mma.sync.aligned.m16n8k16.row.col.f32.bf16.bf16.f32`. -/
def mma16 : MmaSpec := { m := 16, n := 8, k := 16, types := bfTypes }

/-! ## The layout -/

/-- The row of A that A register `r` of lane `l` holds. -/
def aRow (l r : Nat) : Nat := l / 4 + 8 * (r % 2)

/-- The column of A that half `h` of A register `r` of lane `l` holds. -/
def aCol (l r h : Nat) : Nat := 2 * (l % 4) + h + 8 * (r / 2)

/-- The row of B (the contraction index) that half `h` of B register `r` of lane `l` holds. -/
def bRow (l r h : Nat) : Nat := 8 * r + (2 * (l % 4) + h)

/-- The column of B that the B registers of lane `l` hold. -/
def bCol (l : Nat) : Nat := l / 4

/-- The row of C and D that C or D register `r` of lane `l` holds. -/
def cRow (l r : Nat) : Nat := l / 4 + 8 * (r / 2)

/-- The column of C and D that C or D register `r` of lane `l` holds. -/
def cCol (l r : Nat) : Nat := 2 * (l % 4) + r % 2

/-- Core's A fragment: element `i` of a lane is half `i % 2` of register `i / 2`. -/
theorem fragA_eq (l i : Nat) :
    mma16.fragA l i = (0, aRow l (i / 2), aCol l (i / 2) (i % 2)) := by
  simp only [MmaSpec.fragA, mma16, bfTypes, MmaSpec.quad, MmaSpec.perReg, MmaSpec.regBits,
    DType.width, aRow, aCol]
  simp

/-- Core's B fragment: element `i` of a lane is half `i % 2` of register `i / 2`. -/
theorem fragB_eq (l i : Nat) :
    mma16.fragB l i = (0, bRow l (i / 2) (i % 2), bCol l) := by
  simp only [MmaSpec.fragB, mma16, bfTypes, MmaSpec.quad, MmaSpec.perReg, MmaSpec.regBits,
    DType.width, bRow, bCol]
  simp
  omega

/-- Core's C and D fragment: element `i` of a lane is register `i`. -/
theorem fragCD_eq (ty : DType) (l i : Nat) : mma16.fragCD ty l i = (0, cRow l i, cCol l i) := by
  simp [MmaSpec.fragCD, mma16, MmaSpec.quad, cRow, cCol]

/-- `a i k` is held by lane `4 (i % 8) + k % 8 / 2`, A register `2 (k / 8) + i / 8`, half
`k % 2`. -/
theorem aPos {i : Nat} (hi : i < 16) (k : Nat) :
    aRow (4 * (i % 8) + k % 8 / 2) (2 * (k / 8) + i / 8) = i ∧
      aCol (4 * (i % 8) + k % 8 / 2) (2 * (k / 8) + i / 8) (k % 2) = k := by
  unfold aRow aCol
  omega

/-- `b k j` is held by lane `4 j + k % 8 / 2`, B register `k / 8`, half `k % 2`. -/
theorem bPos (k j : Nat) :
    bRow (4 * j + k % 8 / 2) (k / 8) (k % 2) = k ∧ bCol (4 * j + k % 8 / 2) = j := by
  unfold bRow bCol
  omega

/-- `c i j` and `d i j` are held by lane `4 (i % 8) + j / 2`, register `2 (i / 8) + j % 2`. -/
theorem cPos (i : Nat) {j : Nat} (hj : j < 8) :
    cRow (4 * (i % 8) + j / 2) (2 * (i / 8) + j % 2) = i ∧
      cCol (4 * (i % 8) + j / 2) (2 * (i / 8) + j % 2) = j := by
  unfold cRow cCol
  omega

/-- The four 8×8 tiles of a 16×16 matrix `a` in the order of the A registers: tile `q` has
rows `8 (q % 2)` to `8 (q % 2) + 7` and columns `8 (q / 2)` to `8 (q / 2) + 7`. -/
def aTiles (a : Nat → Nat → ℝ) (q i j : Nat) : ℝ := a (i + 8 * (q % 2)) (j + 8 * (q / 2))

/-- The 8×8 tiles of a matrix `b` with 8 columns in the order of the B registers: tile `q` has
rows `8 q` to `8 q + 7`. -/
def bTiles (b : Nat → Nat → ℝ) (q i j : Nat) : ℝ := b (8 * q + i) j

/-- The A registers hold the tiles of `a` in the fragment layout of `ldmatrix`: a plain
`ldmatrix.x4` of the rows of the four tiles loads the A operand. -/
theorem aFrag_eq (a : Nat → Nat → ℝ) (l r h : Nat) :
    a (aRow l r) (aCol l r h) = toFrag (aTiles a) l r h :=
  rfl

/-- The B registers hold the transposed tiles of `b` in the fragment layout of `ldmatrix`: an
`ldmatrix.x4.trans` of the rows of the tiles loads the B operands (two registers per MMA). -/
theorem bFrag_eq (b : Nat → Nat → ℝ) (l r h : Nat) :
    b (bRow l r h) (bCol l) = toFrag (transposeMats (bTiles b)) l r h :=
  rfl

/-! ## The assumption -/

/-- **The MMA's rule is the ideal-real one.** For the element types `bfTypes`, the first
assumption of `A` with a `matrixMmaRule` gives `idealWarpMma`: the exact real sum of products
plus the accumulator, as an f32 payload (ASM-IDEAL). -/
def IdealMma (A : List Assumption) : Prop :=
  ∀ as bs c, A.findSome? (fun a => a.matrixMmaRule bfTypes as bs c) = idealWarpMma bfTypes as bs c

/-- `Assumption.idealReal` with the bf16 MMA in its scope, at the head of the list. -/
theorem IdealMma.cons_idealReal (name why : String) {s : IdealScope} (h : bfTypes ∈ s.warpMma)
    (A : List Assumption) : IdealMma (idealReal name s why :: A) := by
  intro as bs c
  have hr : (idealReal name s why).matrixMmaRule bfTypes as bs c =
      idealWarpMma bfTypes as bs c := by
    simp [idealReal, h]
  rw [List.findSome?_cons, hr]
  rfl

/-- An assumption without a rule for the bf16 MMA in front of the list changes nothing (every
assumption that leaves `matrixMmaRule` at its default qualifies, by `fun _ _ _ => rfl`). -/
theorem IdealMma.cons_skip {a : Assumption} {A : List Assumption}
    (h : ∀ as bs c, a.matrixMmaRule bfTypes as bs c = none) (hA : IdealMma A) :
    IdealMma (a :: A) := by
  intro as bs c
  rw [List.findSome?_cons, h, hA]

/-! ## The operands in the registers of the warp -/

/-- A 32-bit register value that an f32 operand reads as the real `x` and that is stored as one
scalar (its first byte names it): an f32 payload, or bits that decode to a finite f32. -/
structure F32Reg (v : Value) (x : ℝ) : Prop where
  bytes : v.bytes = 4
  whole : v.byteAt 0 = (v, 0)
  val : valFloat .f32 v = .ok x

/-- An f32 payload is read as its number. -/
theorem F32Reg.float (x : ℝ) : F32Reg (.float .f32 x) x :=
  ⟨rfl, rfl, valFloat_float⟩

/-- The zero word (a cleared accumulator, `mov.b32 r, 0`) is read as the number 0. -/
theorem F32Reg.zero : F32Reg (.bits 32 (BitVec.ofNat 64 0)) 0 := by
  refine ⟨rfl, rfl, ?_⟩
  have h : FloatFmt.f32.layout.decode 0 = some (.zero false) := by
    simp [FloatFmt.layout, Layout.decode, Layout.fieldVal]
  have hc : classify .f32 (.bits 32 (BitVec.ofNat 64 0)) = .ok (.zero false) := by
    simpa [FloatFmt.bytes] using classify_bits (fmt := .f32) (by norm_num) h
  rw [valFloat_of_classify (fmt := .f32) (x := .zero false) (by intro f y hh; cases hh) hc]
  simp [FVal.finite, pure, Except.pure]

/-- The value of A register `r` of lane `l` that holds its two elements of `a`. -/
def regA (a : Nat → Nat → ℝ) (l r : Nat) : Value :=
  bf16Pair (a (aRow l r) (aCol l r 0)) (a (aRow l r) (aCol l r 1))

/-- The value of B register `r` of lane `l` that holds its two elements of `b`. -/
def regB (b : Nat → Nat → ℝ) (l r : Nat) : Value :=
  bf16Pair (b (bRow l r 0) (bCol l)) (b (bRow l r 1) (bCol l))

/-- The value of C or D register `r` of lane `l` that holds its element of `c` as a payload. -/
def regC (c : Nat → Nat → ℝ) (l r : Nat) : Value := .float .f32 (c (cRow l r) (cCol l r))

/-- **The registers of the 32 lanes hold the real operands** `a` (16×16), `b` (16×8) and `c`
(16×8): `ra l r`, `rb l r`, `rc l r` are the values of A, B and C register `r` of lane `l`. An A
or B register is the packed pair of two bf16 payloads (`regA`, `regB`); a C register is read as
its number (`F32Reg`). -/
structure Operands (ra rb rc : Nat → Nat → Value) (a b c : Nat → Nat → ℝ) : Prop where
  a : ∀ l < 32, ∀ r < 4, ra l r = regA a l r
  b : ∀ l < 32, ∀ r < 2, rb l r = regB b l r
  c : ∀ l < 32, ∀ r < 4, F32Reg (rc l r) (c (cRow l r) (cCol l r))

/-- Registers of payloads hold their matrices. -/
theorem operands_float (a b c : Nat → Nat → ℝ) : Operands (regA a) (regB b) (regC c) a b c :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => F32Reg.float _⟩

/-- A cleared accumulator: C registers that all hold the zero word are the zero matrix. -/
theorem operands_zero (a b : Nat → Nat → ℝ) :
    Operands (regA a) (regB b) (fun _ _ => .bits 32 (BitVec.ofNat 64 0)) a b fun _ _ => 0 :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => F32Reg.zero⟩

/-- The 40 bytes lane `l` contributes (`mmaOwn`): its four A registers, two B registers and
four C registers, in operand order. -/
def mmaParts (ra rb rc : Nat → Nat → Value) (l : Nat) : List (Option Byte) :=
  [ra l 0, ra l 1, ra l 2, ra l 3, rb l 0, rb l 1, rc l 0, rc l 1, rc l 2, rc l 3].flatMap
    fun v => v.toBytes.map some

/-- The result matrix over the reals: `d i j = c i j + ∑ k < 16, a i k * b k j`. -/
noncomputable def mmaReal (a b c : Nat → Nat → ℝ) (i j : Nat) : ℝ :=
  c i j + ∑ k ∈ Finset.range 16, a i k * b k j

/-- The 16 bytes of the four D registers of lane `l` that hold the f32 payloads of `d`. -/
def outParts (d : Nat → Nat → ℝ) (l : Nat) : List (Option Byte) :=
  ((List.range 4).map fun r => Value.float .f32 (d (cRow l r) (cCol l r))).flatMap
    fun v => v.toBytes.map some

/-! ## Reading the operands back from the contributed bytes -/

private theorem bytes4 {v : Value} (h : v.bytes = 4) :
    v.toBytes.map some =
      [some (v.byteAt 0), some (v.byteAt 1), some (v.byteAt 2), some (v.byteAt 3)] := by
  unfold Value.toBytes
  rw [h]
  rfl

/-- The bytes of one stored scalar rebuild to it (THREAD-BYTES). -/
private theorem rebuild_whole {v : Value} (hv : 0 < v.bytes) (hs : v.byteAt 0 = (v, 0)) :
    rebuild 3 (v.toBytes.map some) = .ok v := by
  obtain ⟨n, hn⟩ : ∃ n, v.bytes = n + 1 := ⟨v.bytes - 1, by omega⟩
  have e : v.toBytes.map some =
      some (v, 0) :: (List.range n).map (fun k => some (v.byteAt (k + 1))) := by
    simp [Value.toBytes, hn, List.range_succ_eq_map, hs]
  rw [e]
  simp only [rebuild]
  rw [ite_eq_left ⟨by simp [hn], e.symm⟩]
  rfl

private theorem rebuild_bf16 (x : ℝ) :
    rebuild 3 [bf16Enc x 0, bf16Enc x 1] = .ok (.float .bf16 x) := by
  simp [rebuild, bf16Enc, Value.bytes, FloatFmt.bytes, Value.toBytes, Value.byteAt,
    List.range_succ, pure, Except.pure]

/-- The contributed bytes of a lane, element by element. -/
private def norm (a b : Nat → Nat → ℝ) (vc : Nat → Value) (l : Nat) : List (Option Byte) :=
  ((List.range 8).flatMap fun i =>
    [bf16Enc (a (aRow l (i / 2)) (aCol l (i / 2) (i % 2))) 0,
     bf16Enc (a (aRow l (i / 2)) (aCol l (i / 2) (i % 2))) 1]) ++
  ((List.range 4).flatMap fun i =>
    [bf16Enc (b (bRow l (i / 2) (i % 2)) (bCol l)) 0,
     bf16Enc (b (bRow l (i / 2) (i % 2)) (bCol l)) 1]) ++
  ((List.range 4).flatMap fun i =>
    [some ((vc i).byteAt 0), some ((vc i).byteAt 1), some ((vc i).byteAt 2),
     some ((vc i).byteAt 3)])

private theorem parts_norm {ra rb rc : Nat → Nat → Value} {a b c : Nat → Nat → ℝ}
    (h : Operands ra rb rc a b c) {l : Nat} (hl : l < 32) :
    mmaParts ra rb rc l = norm a b (rc l) l := by
  have hc (r : Nat) (hr : r < 4) := bytes4 (h.c l hl r hr).bytes
  simp only [mmaParts, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [h.a l hl 0 (by omega), h.a l hl 1 (by omega), h.a l hl 2 (by omega), h.a l hl 3 (by omega),
    h.b l hl 0 (by omega), h.b l hl 1 (by omega), hc 0 (by omega), hc 1 (by omega),
    hc 2 (by omega), hc 3 (by omega)]
  rfl

private theorem norm_a (a b : Nat → Nat → ℝ) (vc : Nat → Value) (l : Nat) (i : Fin 8) :
    ((norm a b vc l).drop (0 + i.val * 2)).take 2 =
      [bf16Enc (a (aRow l (i.val / 2)) (aCol l (i.val / 2) (i.val % 2))) 0,
       bf16Enc (a (aRow l (i.val / 2)) (aCol l (i.val / 2) (i.val % 2))) 1] := by
  fin_cases i <;> rfl

private theorem norm_b (a b : Nat → Nat → ℝ) (vc : Nat → Value) (l : Nat) (i : Fin 4) :
    ((norm a b vc l).drop (16 + i.val * 2)).take 2 =
      [bf16Enc (b (bRow l (i.val / 2) (i.val % 2)) (bCol l)) 0,
       bf16Enc (b (bRow l (i.val / 2) (i.val % 2)) (bCol l)) 1] := by
  fin_cases i <;> rfl

private theorem norm_c (a b : Nat → Nat → ℝ) (vc : Nat → Value) (l : Nat) (i : Fin 4) :
    ((norm a b vc l).drop (24 + i.val * 4)).take 4 =
      [some ((vc i.val).byteAt 0), some ((vc i.val).byteAt 1), some ((vc i.val).byteAt 2),
       some ((vc i.val).byteAt 3)] := by
  fin_cases i <;> rfl

section Read

variable {ra rb rc : Nat → Nat → Value} {a b c : Nat → Nat → ℝ}
  {parts : Nat → List (Option Byte)}

/-- Core reads A element `i` of a lane (`mmaElem`) as the bf16 payload the register holds. -/
theorem mmaElem_a (h : Operands ra rb rc a b c) (hp : ∀ l < 32, parts l = mmaParts ra rb rc l)
    {l i : Nat} (hl : l < 32) (hi : i < 8) :
    mmaElem (parts l) 0 (.float .bf16) i =
      .ok (.float .bf16 (a (aRow l (i / 2)) (aCol l (i / 2) (i % 2)))) := by
  rw [hp l hl, parts_norm h hl]
  change rebuild 3 (((norm a b (rc l) l).drop (0 + i * 2)).take 2) = _
  rw [norm_a a b _ l ⟨i, hi⟩]
  exact rebuild_bf16 _

/-- Core reads B element `i` of a lane as the bf16 payload the register holds. -/
theorem mmaElem_b (h : Operands ra rb rc a b c) (hp : ∀ l < 32, parts l = mmaParts ra rb rc l)
    {l i : Nat} (hl : l < 32) (hi : i < 4) :
    mmaElem (parts l) 16 (.float .bf16) i =
      .ok (.float .bf16 (b (bRow l (i / 2) (i % 2)) (bCol l))) := by
  rw [hp l hl, parts_norm h hl]
  change rebuild 3 (((norm a b (rc l) l).drop (16 + i * 2)).take 2) = _
  rw [norm_b a b _ l ⟨i, hi⟩]
  exact rebuild_bf16 _

/-- Core reads C element `i` of a lane as the value of C register `i`. -/
theorem mmaElem_c (h : Operands ra rb rc a b c) (hp : ∀ l < 32, parts l = mmaParts ra rb rc l)
    {l i : Nat} (hl : l < 32) (hi : i < 4) :
    mmaElem (parts l) 24 (.float .f32) i = .ok (rc l i) := by
  rw [hp l hl, parts_norm h hl]
  change rebuild 3 (((norm a b (rc l) l).drop (24 + i * 4)).take 4) = _
  rw [norm_c a b _ l ⟨i, hi⟩, ← bytes4 (h.c l hl i hi).bytes]
  exact rebuild_whole (by rw [(h.c l hl i hi).bytes]; decide) (h.c l hl i hi).whole

/-- The element at a position of an operand is the value every lane that holds the position
has there (`operandElem` takes the first such lane). -/
private theorem lookup {parts : Nat → List (Option Byte)} {f : Nat → Nat → Nat × Nat × Nat}
    {n off : Nat} {ty : DType} {pos : Nat × Nat × Nat} {v : Nat × Nat × Nat → Value}
    (cover : ∃ l < 32, ∃ i < n, f l i = pos)
    (reads : ∀ l < 32, ∀ i < n, mmaElem (parts l) off ty i = .ok (v (f l i))) :
    operandElem parts f n off ty pos = .ok (v pos) := by
  let cells := (List.range 32).flatMap fun l => (List.range n).map (l, ·)
  let accepts := fun p : Nat × Nat => f p.1 p.2 == pos
  have in_cells (l i : Nat) : (l, i) ∈ cells ↔ l < 32 ∧ i < n := by simp [cells]
  obtain ⟨l, hl, i, hi, hp⟩ := cover
  have present := List.find?_isSome.mpr
    (⟨(l, i), (in_cells ..).mpr ⟨hl, hi⟩, by simp [accepts, hp]⟩ : ∃ p, p ∈ cells ∧ accepts p)
  cases found : cells.find? accepts with
  | none => simp [found] at present
  | some p =>
    have hit : accepts p := List.find?_some found
    have exactPos : f p.1 p.2 = pos := eq_of_beq hit
    have valid := (in_cells p.1 p.2).mp (List.mem_of_find?_eq_some found)
    unfold operandElem
    change (match cells.find? accepts with
      | some (j, k) => mmaElem (parts j) off ty k
      | none => Except.error Fault.noRule) = _
    rw [found, ← exactPos]
    exact reads _ valid.1 _ valid.2

/-- **The A operand.** Core finds `a i k` at position `(i, k)` of A. -/
theorem operand_a (h : Operands ra rb rc a b c) (hp : ∀ l < 32, parts l = mmaParts ra rb rc l)
    {i k : Nat} (hi : i < 16) (hk : k < 16) :
    operandElem parts mma16.fragA 8 0 (.float .bf16) (0, i, k) =
      .ok (.float .bf16 (a i k)) := by
  apply lookup (v := fun p => Value.float .bf16 (a p.2.1 p.2.2))
  · refine ⟨4 * (i % 8) + k % 8 / 2, by omega, 4 * (k / 8) + 2 * (i / 8) + k % 2, by omega, ?_⟩
    simp only [fragA_eq, aRow, aCol, Prod.mk.injEq, true_and]
    omega
  · intro l hl j hj
    rw [fragA_eq]
    exact mmaElem_a h hp hl hj

/-- **The B operand.** Core finds `b k j` at position `(k, j)` of B. -/
theorem operand_b (h : Operands ra rb rc a b c) (hp : ∀ l < 32, parts l = mmaParts ra rb rc l)
    {k j : Nat} (hk : k < 16) (hj : j < 8) :
    operandElem parts mma16.fragB 4 16 (.float .bf16) (0, k, j) =
      .ok (.float .bf16 (b k j)) := by
  apply lookup (v := fun p => Value.float .bf16 (b p.2.1 p.2.2))
  · refine ⟨4 * j + k % 8 / 2, by omega, 2 * (k / 8) + k % 2, by omega, ?_⟩
    simp only [fragB_eq, bRow, bCol, Prod.mk.injEq, true_and]
    omega
  · intro l hl j hj
    rw [fragB_eq]
    exact mmaElem_b h hp hl hj

/-- **The C operand.** Core finds, at position `(i, j)` of C, the value of the C register that
holds it: register `2 (i / 8) + j % 2` of lane `4 (i % 8) + j / 2`, which reads as `c i j`. -/
theorem operand_c (h : Operands ra rb rc a b c) (hp : ∀ l < 32, parts l = mmaParts ra rb rc l)
    {i j : Nat} (hi : i < 16) (hj : j < 8) :
    ∃ v, operandElem parts (mma16.fragCD (.float .f32)) 4 24 (.float .f32) (0, i, j) = .ok v ∧
      valFloat .f32 v = .ok (c i j) := by
  refine ⟨rc (4 * (i % 8) + j / 2) (2 * (i / 8) + j % 2), ?_, ?_⟩
  · apply lookup (v := fun p => rc (4 * (p.2.1 % 8) + p.2.2 / 2) (2 * (p.2.1 / 8) + p.2.2 % 2))
    · refine ⟨4 * (i % 8) + j / 2, by omega, 2 * (i / 8) + j % 2, by omega, ?_⟩
      simp only [fragCD_eq, cRow, cCol, Prod.mk.injEq, true_and]
      omega
    · intro l hl r hr
      rw [fragCD_eq, mmaElem_c h hp hl hr]
      have h1 : 4 * (cRow l r % 8) + cCol l r / 2 = l := by unfold cRow cCol; omega
      have h2 : 2 * (cRow l r / 8) + cCol l r % 2 = r := by unfold cRow cCol; omega
      simp only [h1, h2]
  · have hv := (h.c (4 * (i % 8) + j / 2) (by omega) (2 * (i / 8) + j % 2) (by omega)).val
    rwa [(cPos i hj).1, (cPos i hj).2] at hv

end Read

/-! ## The value of one element and of a lane -/

private theorem mapM_ok {α β : Type} (xs : List α) (f : α → Exec β) (v : α → β)
    (h : ∀ i ∈ xs, f i = .ok (v i)) : xs.mapM f = .ok (xs.map v) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, h x (by simp), ih (fun i hi => h i (by simp [hi]))]
    rfl

private theorem sum_range (f : Nat → ℝ) (n : Nat) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

private theorem products (xs : List (ℝ × ℝ)) :
    ((xs.map (fun p => Value.float .bf16 p.1)).zip
        (xs.map (fun p => Value.float .bf16 p.2))).mapM (fun (x, y) => do
      pure ((← idealWarpElem bfTypes.a x) * (← idealWarpElem bfTypes.b y))) =
      .ok (xs.map fun (x, y) => x * y) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons, ih]
    rfl

/-- **One D element over the reals.** Under the ideal-real rule, an A row and a B column of
bf16 payloads and an accumulator read as `z` give the f32 payload of the exact sum. -/
theorem mmaValue_ideal (hA : IdealMma A) (xs : List (ℝ × ℝ)) {cv : Value} {z : ℝ}
    (hc : valFloat .f32 cv = .ok z) :
    mmaValue A mma16 (xs.map fun p => .float .bf16 p.1) (xs.map fun p => .float .bf16 p.2) cv =
      .ok (.float .f32 ((xs.map fun p => p.1 * p.2).sum + z)) := by
  have hv : mmaValue A mma16 (xs.map fun p => .float .bf16 p.1)
      (xs.map fun p => .float .bf16 p.2) cv =
      (A.findSome? fun a => a.matrixMmaRule bfTypes (xs.map fun p => .float .bf16 p.1)
        (xs.map fun p => .float .bf16 p.2) cv).getD (throw .noRule) := rfl
  rw [hv, hA]
  change (do
    let ps : List ℝ ← _
    let c ← valFloat .f32 cv
    pure (Value.float .f32 (ps.sum + c))) = _
  rw [products xs, hc]
  rfl

private def pairValues (p : ℝ × ℝ) : Value × Value := (.float .bf16 p.1, .float .bf16 p.2)

private noncomputable def pairs (parts : Nat → List (Option Byte)) (r j : Nat) :
    Exec (List (Value × Value)) :=
  (List.range 16).mapM fun k => do
    pure (← operandElem parts mma16.fragA 8 0 (.float .bf16) (0, r, k),
          ← operandElem parts mma16.fragB 4 16 (.float .bf16) (0, k, j))

private noncomputable def cell (A : List Assumption) (parts : Nat → List (Option Byte))
    (r j : Nat) : Exec Value := do
  let ab ← pairs parts r j
  let z ← operandElem parts (mma16.fragCD (.float .f32)) 4 24 (.float .f32) (0, r, j)
  let v ← mmaValue A mma16 (ab.map (·.1)) (ab.map (·.2)) z
  unless v.bytes = 4 do throw .typeMismatch
  pure v

section Recv

variable {ra rb rc : Nat → Nat → Value} {a b c : Nat → Nat → ℝ}
  {parts : Nat → List (Option Byte)}

private theorem read_pairs (h : Operands ra rb rc a b c)
    (hp : ∀ l < 32, parts l = mmaParts ra rb rc l) {i j : Nat} (hi : i < 16) (hj : j < 8) :
    pairs parts i j =
      .ok (((List.range 16).map (fun k => (a i k, b k j))).map pairValues) := by
  unfold pairs
  rw [List.map_map]
  apply mapM_ok
  intro k hk
  have hk' := List.mem_range.mp hk
  simp only [operand_a h hp hi hk', operand_b h hp hk' hj]
  rfl

private theorem read_cell (hA : IdealMma A) (h : Operands ra rb rc a b c)
    (hp : ∀ l < 32, parts l = mmaParts ra rb rc l) {i j : Nat} (hi : i < 16) (hj : j < 8) :
    cell A parts i j = .ok (.float .f32 (mmaReal a b c i j)) := by
  let xs := (List.range 16).map (fun k => (a i k, b k j))
  obtain ⟨cv, hcv, hval⟩ := operand_c h hp hi hj
  unfold cell
  rw [read_pairs h hp hi hj, hcv]
  change (do
    let v ← mmaValue A mma16 ((xs.map pairValues).map Prod.fst)
      ((xs.map pairValues).map Prod.snd) cv
    unless v.bytes = 4 do throw Fault.typeMismatch
    pure v) = _
  simp only [List.map_map, Function.comp_def, pairValues]
  rw [mmaValue_ideal hA xs hval]
  have hsum : (xs.map fun p => p.1 * p.2).sum + c i j = mmaReal a b c i j := by
    simp only [xs, List.map_map, Function.comp_def, sum_range, mmaReal]
    exact add_comm _ _
  rw [hsum]
  rfl

/-- **What a lane receives from the MMA, as bytes.** When the registers of the 32 lanes hold
the real matrices `a`, `b`, `c` and the lanes contribute their bytes, lane `l` receives the
bytes of the four f32 payloads `c i j + ∑ k < 16, a i k * b k j` at its D positions
`(cRow l r, cCol l r)`, `r = 0, …, 3`. Only the contributions of the 32 lanes matter. -/
theorem mmaRecv_eq (hA : IdealMma A) (h : Operands ra rb rc a b c)
    (hp : ∀ l < 32, parts l = mmaParts ra rb rc l) {l : Nat} (hl : l < 32) :
    mmaRecv A mma16 parts l = .ok (outParts (mmaReal a b c) l) := by
  let v := fun i => Value.float .f32 (mmaReal a b c (cRow l i) (cCol l i))
  have vals : (List.range 4).mapM (fun i => cell A parts (cRow l i) (cCol l i)) =
      .ok ((List.range 4).map v) := by
    apply mapM_ok
    intro i hi
    have hi := List.mem_range.mp hi
    exact read_cell hA h hp (by unfold cRow; omega) (by unfold cCol; omega)
  change (do
    let vals ← (List.range 4).mapM (fun i => cell A parts (cRow l i) (cCol l i))
    let regs := (List.range 4).map fun r => match (vals.drop (1 * r)).take 1 with
      | [lo, hi] => Value.pair lo hi
      | x :: _ => x
      | [] => .bits 0 0
    pure (regs.flatMap fun (v : Value) => v.toBytes.map some)) = _
  rw [vals]
  rfl

/-- `mmaRecv_eq` as the result of the instance (`matrixRecv`): it is not an error. -/
theorem matrixRecv_mma (hA : IdealMma A) (h : Operands ra rb rc a b c)
    (hp : ∀ l < 32, parts l = mmaParts ra rb rc l) {l : Nat} (hl : l < 32) :
    matrixRecv A (.mma mma16) parts l = .ok (.bytes (outParts (mmaReal a b c) l)) :=
  matrixRecv_mma_ok (mmaRecv_eq hA h hp hl)

/-- **The MMA event of a lane, given the event.** In a consistent execution whose MMA rule is
the ideal-real one, if the 32 lanes of the warp at `w` perform their `n`-th matrix events as
this MMA with registers that hold `a`, `b`, `c`, then a matrix event of ordinal `n` of lane `l`
received the bytes of its four D elements of `a · b + c`. -/
theorem mma_recv (hX : Consistent L K A mem0 X) (hA : IdealMma A) (hb : L.block % 32 = 0)
    {w n pc l i pc' : Nat} {op' : MatrixOp} {own recv : List (Option Byte)}
    (hw : laneOf L w = 0) (hI : WarpInstance X w n pc (.mma mma16) (mmaParts ra rb rc))
    (h : Operands ra rb rc a b c) (hl : l < 32)
    (he : X.get (w + l, i) = some ⟨pc', .matrix op' own recv⟩) (hk : X.MatrixK (w + l, i) n) :
    recv = outParts (mmaReal a b c) l :=
  recv_mma hX hb hw hI hl he hk (mmaRecv_eq hA h (fun _ _ => rfl) hl)

/-- **The MMA event of a lane.** The same, naming the event: lane `l` has a matrix event of
ordinal `n` at `pc` that contributed its register bytes and received the bytes of its four D
elements of `a · b + c`. -/
theorem mma_event (hX : Consistent L K A mem0 X) (hA : IdealMma A) (hb : L.block % 32 = 0)
    {w n pc l : Nat} (hw : laneOf L w = 0)
    (hI : WarpInstance X w n pc (.mma mma16) (mmaParts ra rb rc))
    (h : Operands ra rb rc a b c) (hl : l < 32) :
    ∃ j, X.get (w + l, j) = some ⟨pc, .matrix (.mma mma16) (mmaParts ra rb rc l)
      (outParts (mmaReal a b c) l)⟩ ∧ X.MatrixK (w + l, j) n :=
  recv_of_instance hX hb hw hI hl (matrixRecv_mma hA h (fun _ _ => rfl) hl)

/-- **The instance is defined.** Whatever contributions `parts'` describe the `n`-th instance of
the warp (Core's `MatrixUnsafe` quantifies over them), the result of a lane is not an error,
when the lanes perform this MMA with registers that hold `a`, `b`, `c`. -/
theorem mma_ne_error (hA : IdealMma A) {w n pc pc' l : Nat} {op' : MatrixOp}
    {parts' : Nat → List (Option Byte)}
    (hI : WarpInstance X w n pc (.mma mma16) (mmaParts ra rb rc))
    (h : Operands ra rb rc a b c) (hI' : WarpInstance X w n pc' op' parts') (hl : l < 32)
    (f : Fault) : matrixRecv A op' parts' l ≠ .error f := by
  obtain ⟨-, rfl, hp⟩ := hI.unique hI'
  rw [matrixRecv_mma hA h hp hl]
  exact fun hne => by cases hne

end Recv

/-! ## The registers of one thread -/

/-- **The D registers after the event.** A lane that receives `outParts d l` continues with its
four D registers holding the f32 payloads `d (cRow l r) (cCol l r)`, `r = 0, …, 3`. -/
theorem afterMatrix_mma (t : TState) {ds : List Nat} (hds : ds.length = 4)
    (d : Nat → Nat → ℝ) (l : Nat) :
    afterMatrix t 32 ds (outParts d l) =
      next (setRegs { t with sub := 0, acc := [] } ds
        ((List.range 4).map fun r => Value.float .f32 (d (cRow l r) (cCol l r)))) := by
  have read (r : Nat) : rebuild 3 ((Value.float .f32 (d (cRow l r) (cCol l r))).toBytes.map some) =
      .ok (.float .f32 (d (cRow l r) (cCol l r))) :=
    rebuild_whole (by change 0 < 4; decide) rfl
  have hlen : (outParts d l).length = ds.length * (32 / 8) := by
    rw [hds]
    rfl
  have hm : ((List.range ds.length).map fun r =>
      ((outParts d l).drop (r * (32 / 8))).take (32 / 8)).mapM (rebuild 3) =
      .ok ((List.range 4).map fun r => Value.float .f32 (d (cRow l r) (cCol l r))) := by
    rw [hds]
    change [(Value.float .f32 (d (cRow l 0) (cCol l 0))).toBytes.map some,
      (Value.float .f32 (d (cRow l 1) (cCol l 1))).toBytes.map some,
      (Value.float .f32 (d (cRow l 2) (cCol l 2))).toBytes.map some,
      (Value.float .f32 (d (cRow l 3) (cCol l 3))).toBytes.map some].mapM (rebuild 3) = _
    simp only [List.mapM_cons, List.mapM_nil, read, bind, Except.bind, pure, Except.pure]
    rfl
  unfold afterMatrix
  simp only [hlen, ite_true, hm]

/-- **The bytes a thread contributes** (`mmaOwn`), when its ten source registers `rs` (four of
A, two of B, four of C) hold the values `vs`, each of four bytes: the bytes of the values in
operand order. With `vs = [ra l 0, …, ra l 3, rb l 0, rb l 1, rc l 0, …, rc l 3]` this is
`mmaParts ra rb rc l`. -/
theorem mmaOwn_mma16 (L : Launch) (g : Nat) (t : TState) {rs : List Nat} {vs : List Value}
    (hlen : rs.length = 10)
    (h : List.Forall₂ (fun r v => t.regs r = some v ∧ v.bytes = 4) rs vs) :
    mmaOwn L g t mma16 (rs.map .reg) = .ok (vs.flatMap fun v => v.toBytes.map some) := by
  have hvl : vs.length = 10 := by rw [← h.length_eq, hlen]
  have h1 := regBytes_regs L g t (List.forall₂_take 6 h)
  have h2 := regBytes_regs L g t (List.forall₂_take 4 (List.forall₂_drop 6 h))
  have h3 : regBytes L g t 32 ((rs.map Opnd.reg).drop 10) = .ok [] := by
    rw [List.drop_of_length_le (by simp [hlen])]
    rfl
  change (do
    let ab ← regBytes L g t 32 ((rs.map Opnd.reg).take 6)
    let c ← regBytes L g t 32 (((rs.map Opnd.reg).drop 6).take 4)
    let e ← regBytes L g t 32 ((rs.map Opnd.reg).drop 10)
    pure (ab ++ c ++ e)) = _
  rw [h3, ← List.map_take, h1, ← List.map_drop, ← List.map_take, h2]
  change Except.ok (_ ++ _ ++ []) = _
  rw [List.append_nil, ← List.flatMap_append]
  have hv : vs.take 6 ++ (vs.drop 6).take 4 = vs := by
    have : (vs.drop 6).take 4 = vs.drop 6 := List.take_of_length_le (by simp [hvl])
    rw [this, List.take_append_drop]
  rw [hv]

/-- **The event of one thread.** In a CTA whose size is a multiple of 32, a thread at this MMA
with destination registers `ds` and source registers `rs` that hold the values `vs` performs the
matrix event that contributes the bytes of `vs` and writes what it receives to `ds`. -/
theorem matrixTmpl_mma16 (L : Launch) (g : Nat) (t : TState) {ds rs : List Nat}
    {vs : List Value} (hb : L.block % 32 = 0) (hds : ds.length = 4) (hrs : rs.length = 10)
    (h : List.Forall₂ (fun r v => t.regs r = some v ∧ v.bytes = 4) rs vs) :
    matrixTmpl L g t { op := .mma mma16, dsts := ds, srcs := rs.map .reg } =
      .matrix (.mma mma16) (vs.flatMap fun v => v.toBytes.map some) (afterMatrix t 32 ds) := by
  have rule : ({ op := .mma mma16, dsts := ds, srcs := rs.map .reg } : MatrixInstr).rule =
      some .threadMma := by
    have hs : mma16.supported = true := by decide
    have hr : mma16.regs = (4, 2, 4, 4) := by decide
    have hsp : mma16.sparse = none := rfl
    simp [MatrixInstr.rule, hs, hr, hsp, hds, hrs]
  unfold matrixTmpl
  rw [ite_eq_left hb, rule]
  change (match mmaOwn L g t mma16 (rs.map .reg) with
    | .error f => Tmpl.ub f
    | .ok own => .matrix (.mma mma16) own (afterMatrix t 32 ds)) = _
  rw [mmaOwn_mma16 L g t hrs h]

end PTX.WarpMatrix
