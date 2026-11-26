-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Matrix.Instance

@[expose] public section

/-! # Warp-level matrix moves: the bytes and elements of `ldmatrix`, `stmatrix`, `movmatrix`

A proof tool, generic over the kernel. Closed forms of what each lane receives
(`matrixMoveRecv`, `transposeRecv`, DEP-WARP-MATRIX) in an instance of

* `ldmatrix.sync.aligned.x4.m8n8.shared.b16` and its `.trans` form (`ld4 false`, `ld4 true`),
* `stmatrix.sync.aligned.x4.m8n8.shared.b16` and its `.trans` form (`st4 false`, `st4 true`),
* `movmatrix.sync.aligned.m8n8.trans.b16` (`MatrixOp.transpose`).

Only these forms are covered; the other shapes of `MatrixMove.source` have no lemma here.

Notation: lane `l = 4 g + t` with `g = l / 4` and `t = l % 4`. A lane's four 32-bit registers are
16 bytes, byte `b` (0 to 3) of register `r` (0 to 3) at position `4 r + b`. A memory row is 16
bytes; lane `s = 8 r + i` supplies row `i` (0 to 7) of matrix `r`.

**Bytes.**
* `ld4_recv`: after a load, byte `b` of register `r` of lane `l` is byte `4 t + b` of the row of
  lane `8 r + g`; with `.trans` it is byte `2 g + b % 2` of the row of lane `8 r + 2 t + b / 2`
  (`ldByte`).
* `st4_recv`: the row a lane `s` writes after a store has, as byte `k`, byte `k % 4` of register
  `s / 8` of lane `4 (s % 8) + k / 4`; with `.trans` byte `2 (s % 2) + k % 2` of register `s / 8`
  of lane `4 (k / 2) + s % 8 / 2` (`stByte`). `stByte` and `ldByte` are inverse
  (`ldByte_stByte`, `stByte_ldByte`).
* `mov_recv`: byte `b` of the result of lane `l` is byte `2 (g % 2) + b % 2` of the source
  register of lane `4 (2 t + b / 2) + g / 2` (`movByte`); `movByte` is an involution.

**Elements.** An element is 16 bits, two bytes given by an encoding `enc x β` (byte `β` of
element `x`). Four 8×8 matrices are `M q i j` (matrix `q`, row `i`, column `j`); the fragments of
a warp are `F l r h` (lane `l`, register `r`, half `h`: 0 is the low half). The fragment layout
(`toFrag`, `ofFrag`, the bijection `fragEquiv`) is: lane `4 g + t` holds row `g`, columns `2 t`
and `2 t + 1` of matrix `r` in register `r`.
* `ld4_elems`: a load of the rows of `M` gives the fragments of `M`; with `.trans` the fragments
  of the transposed matrices.
* `st4_elems`: a store of the fragments `F` writes the rows of the matrices `F` holds; with
  `.trans` the rows of their transposes.
* `mov_elems`: `movmatrix` of the fragments of an 8×8 matrix gives the fragments of its
  transpose.

**Events.** `ld4_event`, `st4_event`, `mov_event`: the same closed forms for a matrix event of a
lane in a consistent execution, from the instance of its warp (`WarpInstance`,
`Lemmas/Matrix/Instance.lean`).

**Registers.** `regBytes_regs`: the bytes a thread contributes from its source registers.
`acc_bytes`: the row bytes a thread keeps between its row access and its matrix event are the
bytes it read or received. `rebuild_bf16Pair`, `afterMatrix_bf16`, `afterMatrix_bf16_one`: a
register that receives the four bytes of two bf16 payloads holds the packed pair `.pair lo hi` of
the two payloads (`bf16Pair`), and `bf16Pair_bytes`, `regPart_bf16` give the bytes such registers
contribute; an `mma` reads its bf16 elements back from them (`Lemmas/Matrix/Mma.lean`).
-/

namespace PTX.WarpMatrix

/-- `ldmatrix.sync.aligned.x4.m8n8.shared.b16`; with `.trans` when `trans` holds. -/
def ld4 (trans : Bool) : MatrixMove := ⟨false, .m8n8, 4, trans, .b16⟩

/-- `stmatrix.sync.aligned.x4.m8n8.shared.b16`; with `.trans` when `trans` holds. -/
def st4 (trans : Bool) : MatrixMove := ⟨true, .m8n8, 4, trans, .b16⟩

/-! ## Bytes -/

private theorem app2 {β γ δ : Type} (f : β → γ → δ) {a a' : β} {b b' : γ} (h1 : a = a')
    (h2 : b = b') : f a b = f a' b' := by rw [h1, h2]

private theorem app3 {β γ δ ε : Type} (f : β → γ → δ → ε) {a a' : β} {b b' : γ} {c c' : δ}
    (h1 : a = a') (h2 : b = b') (h3 : c = c') : f a b c = f a' b' c' := by rw [h1, h2, h3]

/-- The 16 bytes of a memory row as a lane's contribution: `rows s k` is byte `k` of the row
whose address lane `s` supplies. -/
def rowPart (rows : Nat → Nat → Option Byte) (s : Nat) : List (Option Byte) :=
  (List.range 16).map (rows s)

/-- The 16 bytes of the four registers of a lane: `regs l r b` is byte `b` of register `r` of
lane `l`. -/
def regPart (regs : Nat → Nat → Nat → Option Byte) (l : Nat) : List (Option Byte) :=
  (List.range 16).map fun x => regs l (x / 4) (x % 4)

/-- The 4 bytes of one register of a lane: `reg l b` is byte `b` of the register of lane `l`. -/
def reg1Part (reg : Nat → Nat → Option Byte) (l : Nat) : List (Option Byte) :=
  (List.range 4).map (reg l)

theorem rowPart_get (rows : Nat → Nat → Option Byte) (s : Nat) {k : Nat} (hk : k < 16) :
    (rowPart rows s)[k]?.join = rows s k := by
  simp [rowPart, hk]

theorem regPart_get (regs : Nat → Nat → Nat → Option Byte) (l : Nat) {x : Nat} (hx : x < 16) :
    (regPart regs l)[x]?.join = regs l (x / 4) (x % 4) := by
  simp [regPart, hx]

theorem reg1Part_get (reg : Nat → Nat → Option Byte) (l : Nat) {b : Nat} (hb : b < 4) :
    (reg1Part reg l)[b]?.join = reg l b := by
  simp [reg1Part, hb]

/-- Where a load takes byte `b` of register `r` of lane `l` from: the supplying lane and the
byte of its row (`MatrixMove.source`, EXT-MATRIX-FIGURES). -/
theorem ld4_source (trans : Bool) (l r b : Nat) :
    (ld4 trans).source l r b =
      if trans then (8 * r + 2 * (l % 4) + b / 2, 2 * (l / 4) + b % 2)
      else (8 * r + l / 4, 4 * (l % 4) + b) := by
  cases trans <;> rfl

/-- A store places register bytes in rows by the same map as the load. -/
theorem st4_source (trans : Bool) (l r b : Nat) :
    (st4 trans).source l r b = (ld4 trans).source l r b := by
  cases trans <;> rfl

/-- Byte `b` of register `r` of lane `l` after a load of the rows `rows`: without `.trans` byte
`4 (l % 4) + b` of the row of lane `8 r + l / 4`; with `.trans` byte `2 (l / 4) + b % 2` of the
row of lane `8 r + 2 (l % 4) + b / 2`. -/
def ldByte (trans : Bool) (rows : Nat → Nat → Option Byte) (l r b : Nat) : Option Byte :=
  if trans then rows (8 * r + 2 * (l % 4) + b / 2) (2 * (l / 4) + b % 2)
  else rows (8 * r + l / 4) (4 * (l % 4) + b)

/-- **`ldmatrix`, any contributions.** The 16 bytes lane `l` receives, from the lanes'
contributed lists. -/
theorem ld4_recv_parts (trans : Bool) (parts : Nat → List (Option Byte)) (l : Nat) :
    matrixMoveRecv (ld4 trans) parts l = .bytes ((List.range 16).map fun x =>
      if trans then (parts (8 * (x / 4) + 2 * (l % 4) + x % 4 / 2))[2 * (l / 4) + x % 4 % 2]?.join
      else (parts (8 * (x / 4) + l / 4))[4 * (l % 4) + x % 4]?.join) := by
  cases trans <;> rfl

/-- **`ldmatrix`, bytes.** Lane `l` of a load of the rows `rows` receives the 16 register bytes
`ldByte trans rows l`. -/
theorem ld4_recv (trans : Bool) (rows : Nat → Nat → Option Byte) {l : Nat} (hl : l < 32) :
    matrixMoveRecv (ld4 trans) (rowPart rows) l = .bytes (regPart (ldByte trans rows) l) := by
  rw [ld4_recv_parts]
  refine congrArg MatrixResult.bytes (List.map_congr_left fun x hx => ?_)
  have hx' := List.mem_range.mp hx
  cases trans
  · simp only [Bool.false_eq_true, ite_false, ldByte]
    exact rowPart_get rows _ (by omega)
  · simp only [ite_true, ldByte]
    exact rowPart_get rows _ (by omega)

/-- Byte `b` of register `r` of what lane `l` received from a load. -/
theorem ld4_recv_byte (trans : Bool) (rows : Nat → Nat → Option Byte) {l r b : Nat}
    (hr : r < 4) (hb : b < 4) :
    (regPart (ldByte trans rows) l)[4 * r + b]? = some (ldByte trans rows l r b) := by
  have h1 : (4 * r + b) / 4 = r := by omega
  have h2 : (4 * r + b) % 4 = b := by omega
  simp [regPart, show 4 * r + b < 16 by omega, h1, h2]

/-- Byte `k` of the row lane `s` writes after a store of the register bytes `regs`: without
`.trans` byte `k % 4` of register `s / 8` of lane `4 (s % 8) + k / 4`; with `.trans` byte
`2 (s % 2) + k % 2` of register `s / 8` of lane `4 (k / 2) + s % 8 / 2`. -/
def stByte (trans : Bool) (regs : Nat → Nat → Nat → Option Byte) (s k : Nat) : Option Byte :=
  if trans then regs (4 * (k / 2) + s % 8 / 2) (s / 8) (2 * (s % 2) + k % 2)
  else regs (4 * (s % 8) + k / 4) (s / 8) (k % 4)

private theorem find?_unique {α : Type} {p : α → Bool} {xs : List α} {a : α} (ha : a ∈ xs)
    (hp : p a = true) (hu : ∀ b ∈ xs, p b = true → b = a) : xs.find? p = some a := by
  cases h : xs.find? p with
  | none => exact absurd hp (by simpa using List.find?_eq_none.mp h a ha)
  | some b => rw [hu b (List.mem_of_find?_eq_some h) (List.find?_some h)]

/-- The lane and register byte that a store places at byte `k` of row `s`, found by Core's
search (`MatrixMove.storeByte`): the only register byte `MatrixMove.source` maps there. -/
theorem st4_storeByte_parts (trans : Bool) (parts : Nat → List (Option Byte)) {s k : Nat}
    (hs : s < 32) (hk : k < 16) :
    (st4 trans).storeByte parts s k =
      if trans then (parts (4 * (k / 2) + s % 8 / 2))[4 * (s / 8) + 2 * (s % 2) + k % 2]?.join
      else (parts (4 * (s % 8) + k / 4))[4 * (s / 8) + k % 4]?.join := by
  let cells := (List.range 32).flatMap fun l => (List.range 16).map (l, ·)
  have mem (l x : Nat) : (l, x) ∈ cells ↔ l < 32 ∧ x < 16 := by simp [cells]
  have hfind (a : Nat × Nat) (h : cells.find?
      (fun (l, x) => (st4 trans).source l (x / 4) (x % 4) == (s, k)) = some a) :
      (st4 trans).storeByte parts s k = (parts a.1)[a.2]?.join := by
    unfold MatrixMove.storeByte
    change (match cells.find? (fun (l, x) => (st4 trans).source l (x / 4) (x % 4) == (s, k)) with
      | some (l, x) => (parts l)[x]?.join
      | none => none) = _
    rw [h]
  cases trans
  · rw [hfind (4 * (s % 8) + k / 4, 4 * (s / 8) + k % 4)]
    · rfl
    · refine find?_unique ((mem _ _).mpr ⟨by omega, by omega⟩) ?_ ?_
      · simp only [st4_source, ld4_source, Bool.false_eq_true, ite_false, beq_iff_eq,
          Prod.mk.injEq]
        omega
      · rintro ⟨l, x⟩ hm hp
        have hb := (mem l x).mp hm
        simp only [st4_source, ld4_source, Bool.false_eq_true, ite_false, beq_iff_eq,
          Prod.mk.injEq] at hp
        simp only [Prod.mk.injEq]
        omega
  · rw [hfind (4 * (k / 2) + s % 8 / 2, 4 * (s / 8) + 2 * (s % 2) + k % 2)]
    · rfl
    · refine find?_unique ((mem _ _).mpr ⟨by omega, by omega⟩) ?_ ?_
      · simp only [st4_source, ld4_source, ite_true, beq_iff_eq, Prod.mk.injEq]
        omega
      · rintro ⟨l, x⟩ hm hp
        have hb := (mem l x).mp hm
        simp only [st4_source, ld4_source, ite_true, beq_iff_eq, Prod.mk.injEq] at hp
        simp only [Prod.mk.injEq]
        omega

/-- **`stmatrix`, any contributions.** The 16 bytes lane `s` receives (and then writes to its
row), from the lanes' contributed register bytes. -/
theorem st4_recv_parts (trans : Bool) (parts : Nat → List (Option Byte)) {s : Nat}
    (hs : s < 32) :
    matrixMoveRecv (st4 trans) parts s = .bytes ((List.range 16).map fun k =>
      if trans then (parts (4 * (k / 2) + s % 8 / 2))[4 * (s / 8) + 2 * (s % 2) + k % 2]?.join
      else (parts (4 * (s % 8) + k / 4))[4 * (s / 8) + k % 4]?.join) := by
  have h : matrixMoveRecv (st4 trans) parts s =
      .bytes ((List.range 16).map ((st4 trans).storeByte parts s)) := by
    change (if s < 4 * 8 then MatrixResult.bytes ((List.range 16).map _) else .bytes []) = _
    rw [ite_eq_left (by omega : s < 4 * 8)]
  rw [h]
  exact congrArg MatrixResult.bytes (List.map_congr_left fun k hk =>
    st4_storeByte_parts trans parts hs (List.mem_range.mp hk))

/-- **`stmatrix`, bytes.** Lane `s` of a store of the register bytes `regs` receives the 16 row
bytes `stByte trans regs s`. -/
theorem st4_recv (trans : Bool) (regs : Nat → Nat → Nat → Option Byte) {s : Nat} (hs : s < 32) :
    matrixMoveRecv (st4 trans) (regPart regs) s = .bytes (rowPart (stByte trans regs) s) := by
  rw [st4_recv_parts trans _ hs]
  refine congrArg MatrixResult.bytes (List.map_congr_left fun k hk => ?_)
  have hk' := List.mem_range.mp hk
  cases trans
  · simp only [Bool.false_eq_true, ite_false, stByte]
    rw [regPart_get regs _ (by omega)]
    exact app3 regs rfl (by omega) (by omega)
  · simp only [ite_true, stByte]
    rw [regPart_get regs _ (by omega)]
    exact app3 regs rfl (by omega) (by omega)

/-- Loading the rows that a store wrote gives back the register bytes. -/
theorem ldByte_stByte (trans : Bool) (regs : Nat → Nat → Nat → Option Byte) {l r b : Nat}
    (hl : l < 32) (hb : b < 4) :
    ldByte trans (stByte trans regs) l r b = regs l r b := by
  cases trans
  · simp only [ldByte, stByte, Bool.false_eq_true, ite_false]
    exact app3 regs (by omega) (by omega) (by omega)
  · simp only [ldByte, stByte, ite_true]
    exact app3 regs (by omega) (by omega) (by omega)

/-- Storing the registers that a load filled gives back the rows. -/
theorem stByte_ldByte (trans : Bool) (rows : Nat → Nat → Option Byte) {s k : Nat}
    (hk : k < 16) :
    stByte trans (ldByte trans rows) s k = rows s k := by
  cases trans
  · simp only [ldByte, stByte, Bool.false_eq_true, ite_false]
    exact app2 rows (by omega) (by omega)
  · simp only [ldByte, stByte, ite_true]
    exact app2 rows (by omega) (by omega)

/-- Byte `b` of the `movmatrix` result of lane `l`: byte `2 (l / 4 % 2) + b % 2` of the source
register of lane `4 (2 (l % 4) + b / 2) + l / 4 / 2` (`transposeSource`). -/
def movByte (reg : Nat → Nat → Option Byte) (l b : Nat) : Option Byte :=
  reg (4 * (2 * (l % 4) + b / 2) + l / 4 / 2) (2 * (l / 4 % 2) + b % 2)

/-- **`movmatrix`, any contributions.** The 4 bytes lane `l` receives. -/
theorem mov_recv_parts (parts : Nat → List (Option Byte)) (l : Nat) :
    transposeRecv parts l = (List.range 4).map fun b =>
      (parts (4 * (2 * (l % 4) + b / 2) + l / 4 / 2))[2 * (l / 4 % 2) + b % 2]?.join :=
  rfl

/-- **`movmatrix`, bytes.** Lane `l` receives the 4 register bytes `movByte reg l`. -/
theorem mov_recv (reg : Nat → Nat → Option Byte) (l : Nat) :
    transposeRecv (reg1Part reg) l = reg1Part (movByte reg) l := by
  rw [mov_recv_parts]
  refine List.map_congr_left fun b _ => ?_
  exact reg1Part_get reg _ (by omega)

/-- `movmatrix` twice gives back the source registers. -/
theorem movByte_movByte (reg : Nat → Nat → Option Byte) {l b : Nat} (hl : l < 32) (hb : b < 4) :
    movByte (movByte reg) l b = reg l b := by
  simp only [movByte]
  have h1 : (4 * (2 * (l % 4) + b / 2) + l / 4 / 2) % 4 = l / 4 / 2 := by omega
  have h2 : (4 * (2 * (l % 4) + b / 2) + l / 4 / 2) / 4 = 2 * (l % 4) + b / 2 := by omega
  have h3 : (2 * (l / 4 % 2) + b % 2) / 2 = l / 4 % 2 := by omega
  have h4 : (2 * (l / 4 % 2) + b % 2) % 2 = b % 2 := by omega
  rw [h1, h2, h3, h4]
  exact app2 reg (by omega) (by omega)

/-! ## 16-bit elements -/

section Elements

variable {α : Type}

/-- The fragments that hold the 8×8 matrix `S`: lane `l` holds row `l / 4`, column
`2 (l % 4)` in the low half (`h = 0`) and `2 (l % 4) + 1` in the high half (`h = 1`). -/
def toFrag1 (S : Nat → Nat → α) (l h : Nat) : α := S (l / 4) (2 * (l % 4) + h)

/-- The 8×8 matrix that one register per lane holds: element `(i, j)` is half `j % 2` of lane
`4 i + j / 2`. -/
def ofFrag1 (F : Nat → Nat → α) (i j : Nat) : α := F (4 * i + j / 2) (j % 2)

/-- The fragments that hold the matrices `M`: register `r` of lane `l` holds matrix `r`. -/
def toFrag (M : Nat → Nat → Nat → α) (l r h : Nat) : α := toFrag1 (M r) l h

/-- The matrices that the fragments `F` hold: matrix `q` is in register `q` of each lane. -/
def ofFrag (F : Nat → Nat → Nat → α) (q i j : Nat) : α := ofFrag1 (fun l => F l q) i j

/-- The transposes of the matrices `M`. -/
def transposeMats (M : Nat → Nat → Nat → α) (q i j : Nat) : α := M q j i

theorem toFrag1_ofFrag1 (F : Nat → Nat → α) {l h : Nat} (hh : h < 2) :
    toFrag1 (ofFrag1 F) l h = F l h := by
  simp only [toFrag1, ofFrag1]
  exact app2 F (by omega) (by omega)

theorem ofFrag1_toFrag1 (S : Nat → Nat → α) {i j : Nat} (hj : j < 8) :
    ofFrag1 (toFrag1 S) i j = S i j := by
  simp only [toFrag1, ofFrag1]
  exact app2 S (by omega) (by omega)

/-- The fragments of the matrices that fragments hold are those fragments. -/
theorem toFrag_ofFrag (F : Nat → Nat → Nat → α) {l r h : Nat} (hh : h < 2) :
    toFrag (ofFrag F) l r h = F l r h :=
  toFrag1_ofFrag1 (fun l => F l r) hh

/-- The matrices that the fragments of matrices hold are those matrices. -/
theorem ofFrag_toFrag (M : Nat → Nat → Nat → α) {q i j : Nat} (hj : j < 8) :
    ofFrag (toFrag M) q i j = M q i j :=
  ofFrag1_toFrag1 (M q) hj

/-- **The fragment layout is a bijection** between the positions (lane, register, half) of a
warp's four registers and the positions (matrix, row, column) of four 8×8 matrices. -/
def fragEquiv : Fin 32 × Fin 4 × Fin 2 ≃ Fin 4 × Fin 8 × Fin 8 where
  toFun p := (p.2.1, ⟨p.1 / 4, by omega⟩, ⟨2 * (p.1 % 4) + p.2.2, by omega⟩)
  invFun q := (⟨4 * q.2.1 + q.2.2 / 2, by omega⟩, q.1, ⟨q.2.2 % 2, by omega⟩)
  left_inv := by
    rintro ⟨l, r, h⟩
    simp only [Prod.mk.injEq, Fin.ext_iff, true_and]
    omega
  right_inv := by
    rintro ⟨q, i, j⟩
    simp only [Prod.mk.injEq, Fin.ext_iff, true_and]
    omega

/-- `toFrag` reads the matrices at the position `fragEquiv` gives. -/
theorem toFrag_fin (M : Nat → Nat → Nat → α) (p : Fin 32 × Fin 4 × Fin 2) :
    toFrag M p.1 p.2.1 p.2.2 = M (fragEquiv p).1 (fragEquiv p).2.1 (fragEquiv p).2.2 :=
  rfl

/-- `ofFrag` reads the fragments at the position `fragEquiv.symm` gives. -/
theorem ofFrag_fin (F : Nat → Nat → Nat → α) (q : Fin 4 × Fin 8 × Fin 8) :
    ofFrag F q.1 q.2.1 q.2.2 =
      F (fragEquiv.symm q).1 (fragEquiv.symm q).2.1 (fragEquiv.symm q).2.2 :=
  rfl

variable (enc : α → Nat → Option Byte)

/-- The row bytes of four 8×8 matrices of elements with byte encoding `enc`: lane `s` supplies
row `s % 8` of matrix `s / 8`, element `j` at bytes `2 j` and `2 j + 1`. -/
def matRows (M : Nat → Nat → Nat → α) (s k : Nat) : Option Byte :=
  enc (M (s / 8) (s % 8) (k / 2)) (k % 2)

/-- The register bytes of fragments: half `h` of a register at its bytes `2 h` and `2 h + 1`. -/
def fragRegs (F : Nat → Nat → Nat → α) (l r b : Nat) : Option Byte :=
  enc (F l r (b / 2)) (b % 2)

/-- The bytes of one register per lane. -/
def fragReg1 (F : Nat → Nat → α) (l b : Nat) : Option Byte := enc (F l (b / 2)) (b % 2)

/-- A load of the rows of `M` fills the registers with the fragments of `M`, or with `.trans`
of the transposes. -/
theorem ldByte_matRows (trans : Bool) (M : Nat → Nat → Nat → α) {l r b : Nat} (hl : l < 32)
    (hb : b < 4) :
    ldByte trans (matRows enc M) l r b =
      fragRegs enc (toFrag (if trans then transposeMats M else M)) l r b := by
  cases trans
  · simp only [ldByte, matRows, fragRegs, toFrag, toFrag1, Bool.false_eq_true, ite_false]
    exact app2 enc (app3 M (by omega) (by omega) (by omega)) (by omega)
  · simp only [ldByte, matRows, fragRegs, toFrag, toFrag1, transposeMats, ite_true]
    exact app2 enc (app3 M (by omega) (by omega) (by omega)) (by omega)

/-- **`ldmatrix`, elements.** Lane `l = 4 g + t` of a load of the rows of the matrices `M`
receives, in register `r`, elements `M r g (2 t)` and `M r g (2 t + 1)`; with `.trans`,
`M r (2 t) g` and `M r (2 t + 1) g`. -/
theorem ld4_elems (trans : Bool) (M : Nat → Nat → Nat → α) {l : Nat} (hl : l < 32) :
    matrixMoveRecv (ld4 trans) (rowPart (matRows enc M)) l =
      .bytes (regPart (fragRegs enc (toFrag (if trans then transposeMats M else M))) l) := by
  rw [ld4_recv trans _ hl]
  refine congrArg MatrixResult.bytes (List.map_congr_left fun x hx => ?_)
  have hx' := List.mem_range.mp hx
  exact ldByte_matRows enc trans M hl (by omega)

/-- A store of fragments writes the rows of the matrices they hold, or with `.trans` of their
transposes. -/
theorem stByte_fragRegs (trans : Bool) (F : Nat → Nat → Nat → α) (s k : Nat) :
    stByte trans (fragRegs enc F) s k =
      matRows enc (if trans then transposeMats (ofFrag F) else ofFrag F) s k := by
  cases trans
  · simp only [stByte, matRows, fragRegs, ofFrag, ofFrag1, Bool.false_eq_true, ite_false]
    exact app2 enc (app3 F (by omega) rfl (by omega)) (by omega)
  · simp only [stByte, matRows, fragRegs, ofFrag, ofFrag1, transposeMats, ite_true]
    exact app2 enc (app3 F (by omega) rfl (by omega)) (by omega)

/-- **`stmatrix`, elements.** Lane `s = 8 q + i` of a store of the fragments `F` receives, and
writes to its row, the elements `j = 0, …, 7` of row `i` of the matrix that the registers `q`
hold: half `j % 2` of register `q` of lane `4 i + j / 2`; with `.trans`, of column `i`: half
`i % 2` of register `q` of lane `4 j + i / 2`. -/
theorem st4_elems (trans : Bool) (F : Nat → Nat → Nat → α) {s : Nat} (hs : s < 32) :
    matrixMoveRecv (st4 trans) (regPart (fragRegs enc F)) s =
      .bytes (rowPart (matRows enc (if trans then transposeMats (ofFrag F) else ofFrag F)) s) := by
  rw [st4_recv trans _ hs]
  exact congrArg MatrixResult.bytes (List.map_congr_left fun k _ =>
    stByte_fragRegs enc trans F s k)

/-- `movmatrix` on the register bytes of the fragments of an 8×8 matrix. -/
theorem movByte_fragReg1 (S : Nat → Nat → α) {l : Nat} (hl : l < 32) (b : Nat) :
    movByte (fragReg1 enc (toFrag1 S)) l b = fragReg1 enc (toFrag1 fun i j => S j i) l b := by
  simp only [movByte, fragReg1, toFrag1]
  exact app2 enc (app2 S (by omega) (by omega)) (by omega)

/-- **`movmatrix`, elements.** When the source registers of the warp hold the 8×8 matrix `S`
(lane `4 g + t` holds `S g (2 t)` and `S g (2 t + 1)`), lane `l` receives the fragment of the
transpose: `S (2 t) g` and `S (2 t + 1) g`. -/
theorem mov_elems (S : Nat → Nat → α) {l : Nat} (hl : l < 32) :
    transposeRecv (reg1Part (fragReg1 enc (toFrag1 S))) l =
      reg1Part (fragReg1 enc (toFrag1 fun i j => S j i)) l := by
  rw [mov_recv]
  exact List.map_congr_left fun b _ => movByte_fragReg1 enc S hl b

end Elements

/-! ## Events of a consistent execution -/

section Events

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`ldmatrix`, the event of a lane.** In a consistent execution, if the 32 lanes of the warp
at `w` perform their `n`-th matrix events as this load, lane `s` contributing the 16 bytes
`rows s` of the row it read, then a matrix event of ordinal `n` of lane `l` received the register
bytes `ldByte trans rows l`. -/
theorem ld4_event (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0) {trans : Bool}
    {rows : Nat → Nat → Option Byte} {w n pc l i pc' : Nat} {op' : MatrixOp}
    {own recv : List (Option Byte)} (hw : laneOf L w = 0)
    (hI : WarpInstance X w n pc (.move (ld4 trans)) (rowPart rows)) (hl : l < 32)
    (he : X.get (w + l, i) = some ⟨pc', .matrix op' own recv⟩) (hk : X.MatrixK (w + l, i) n) :
    recv = regPart (ldByte trans rows) l :=
  recv_move hX hb hw hI hl he hk (ld4_recv trans rows hl)

/-- **`stmatrix`, the event of a lane.** If the 32 lanes perform their `n`-th matrix events as
this store, lane `l'` contributing the 16 bytes `regs l'` of its four source registers, then a
matrix event of ordinal `n` of lane `l` received the row bytes `stByte trans regs l`, which it
then writes to the row whose address it supplies. -/
theorem st4_event (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0) {trans : Bool}
    {regs : Nat → Nat → Nat → Option Byte} {w n pc l i pc' : Nat} {op' : MatrixOp}
    {own recv : List (Option Byte)} (hw : laneOf L w = 0)
    (hI : WarpInstance X w n pc (.move (st4 trans)) (regPart regs)) (hl : l < 32)
    (he : X.get (w + l, i) = some ⟨pc', .matrix op' own recv⟩) (hk : X.MatrixK (w + l, i) n) :
    recv = rowPart (stByte trans regs) l :=
  recv_move hX hb hw hI hl he hk (st4_recv trans regs hl)

/-- **`movmatrix`, the event of a lane.** If the 32 lanes perform their `n`-th matrix events as
`movmatrix`, lane `l'` contributing the 4 bytes `reg l'` of its source register, then a matrix
event of ordinal `n` of lane `l` received the register bytes `movByte reg l`. -/
theorem mov_event (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0)
    {reg : Nat → Nat → Option Byte} {w n pc l i pc' : Nat} {op' : MatrixOp}
    {own recv : List (Option Byte)} (hw : laneOf L w = 0)
    (hI : WarpInstance X w n pc .transpose (reg1Part reg)) (hl : l < 32)
    (he : X.get (w + l, i) = some ⟨pc', .matrix op' own recv⟩) (hk : X.MatrixK (w + l, i) n) :
    recv = reg1Part (movByte reg) l :=
  (recv_transpose hX hb hw hI hl he hk).trans (mov_recv reg l)

end Events

/-! ## Registers: contributed bytes, and two bf16 payloads in one register -/

/-- The row bytes a thread keeps in its state between its row access and its matrix event
(`matrixMoveTmpl`: `acc := bs.filterMap (·.map byteValue)`, read back with `valueByte`) are the
bytes it read (a load, which contributes them) or received (a store, which writes them), when
none is unknown. -/
theorem acc_bytes {bs : List (Option Byte)} (h : bs.all Option.isSome = true) :
    ((bs.filterMap fun b => b.map byteValue).filterMap valueByte).map some = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    cases b with
    | none => simp at h
    | some b =>
      have ih' := ih h.2
      simp only [List.filterMap_cons, Option.map_some, valueByte, byteValue, List.map_cons]
      rw [ih']

/-- The bytes the 32-bit source registers `rs` of a thread contribute (`regBytes`: the
contribution of a `stmatrix` or `movmatrix` thread, and the parts of an MMA's `mmaOwn`), when
they hold the values `vs`, each of four bytes. -/
theorem regBytes_regs (L : Launch) (g : Nat) (t : TState) {rs : List Nat} {vs : List Value}
    (h : List.Forall₂ (fun r v => t.regs r = some v ∧ v.bytes = 4) rs vs) :
    regBytes L g t 32 (rs.map .reg) = .ok (vs.flatMap fun v => v.toBytes.map some) := by
  let step : List (Option Byte) → Opnd → Exec (List (Option Byte)) := fun acc o => do
    let v ← readValue L g t 32 o
    unless v.bytes = 32 / 8 do throw .typeMismatch
    pure (acc ++ v.toBytes.map some)
  have key : ∀ acc : List (Option Byte),
      (rs.map Opnd.reg).foldlM step acc =
        .ok (acc ++ vs.flatMap fun v => v.toBytes.map some) := by
    induction h with
    | nil => intro acc; simp [pure, Except.pure]
    | @cons r v rs vs hrv _ ih =>
      intro acc
      obtain ⟨hr, hv⟩ := hrv
      have hstep : step acc (.reg r) = .ok (acc ++ v.toBytes.map some) := by
        simp [step, readValue, readReg, hr, hv, bind, Except.bind, pure, Except.pure]
      rw [List.map_cons, List.foldlM_cons, hstep]
      change (rs.map Opnd.reg).foldlM step (acc ++ v.toBytes.map some) = _
      rw [ih, List.flatMap_cons, List.append_assoc]
  have h0 := key []
  rw [List.nil_append] at h0
  exact h0

/-- The byte encoding of a bf16 payload: byte `β` (0 or 1) of the stored value `.float .bf16 x`.
A memory row written from bf16 payloads holds these bytes. -/
def bf16Enc (x : ℝ) (β : Nat) : Option Byte := some (.float .bf16 x, β)

/-- The 32-bit register value that holds the bf16 payloads `lo` (low half) and `hi`. -/
def bf16Pair (lo hi : ℝ) : Value := .pair (.float .bf16 lo) (.float .bf16 hi)

/-- The four bytes a register of two bf16 payloads contributes. -/
theorem bf16Pair_bytes (lo hi : ℝ) :
    (bf16Pair lo hi).toBytes.map some =
      [bf16Enc lo 0, bf16Enc lo 1, bf16Enc hi 0, bf16Enc hi 1] :=
  rfl

/-- **Four bytes of two bf16 payloads rebuild to the packed pair** (THREAD-BYTES): the register
a matrix load or `movmatrix` fills from such bytes holds `.pair lo hi` of the two payloads. -/
theorem rebuild_bf16Pair (lo hi : ℝ) :
    rebuild 3 [bf16Enc lo 0, bf16Enc lo 1, bf16Enc hi 0, bf16Enc hi 1] =
      .ok (bf16Pair lo hi) := by
  simp [rebuild, rebuild.halves, bf16Enc, bf16Pair, Value.bytes, FloatFmt.bytes, Value.toBytes,
    Value.byteAt, intByte, List.range_succ, bind, Except.bind, pure, Except.pure]

/-- The 16 register bytes of fragments of bf16 payloads are the bytes of four packed pairs. -/
theorem regPart_bf16 (F : Nat → Nat → Nat → ℝ) (l : Nat) :
    regPart (fragRegs bf16Enc F) l =
      ((List.range 4).map fun r => bf16Pair (F l r 0) (F l r 1)).flatMap fun v =>
        v.toBytes.map some := by
  have h : regPart (fragRegs bf16Enc F) l =
      [bf16Enc (F l 0 0) 0, bf16Enc (F l 0 0) 1, bf16Enc (F l 0 1) 0, bf16Enc (F l 0 1) 1,
       bf16Enc (F l 1 0) 0, bf16Enc (F l 1 0) 1, bf16Enc (F l 1 1) 0, bf16Enc (F l 1 1) 1,
       bf16Enc (F l 2 0) 0, bf16Enc (F l 2 0) 1, bf16Enc (F l 2 1) 0, bf16Enc (F l 2 1) 1,
       bf16Enc (F l 3 0) 0, bf16Enc (F l 3 0) 1, bf16Enc (F l 3 1) 0, bf16Enc (F l 3 1) 1] :=
    rfl
  rw [h]
  rfl

/-- The 4 register bytes of a fragment of bf16 payloads are the bytes of a packed pair. -/
theorem reg1Part_bf16 (F : Nat → Nat → ℝ) (l : Nat) :
    reg1Part (fragReg1 bf16Enc F) l = (bf16Pair (F l 0) (F l 1)).toBytes.map some := by
  have h : reg1Part (fragReg1 bf16Enc F) l =
      [bf16Enc (F l 0) 0, bf16Enc (F l 0) 1, bf16Enc (F l 1) 0, bf16Enc (F l 1) 1] := rfl
  rw [h]
  rfl

/-- **The registers after a load of bf16 elements.** A lane that receives the register bytes
of the fragments `F` of bf16 payloads (`ld4_elems` with `enc := bf16Enc`) continues with its
four destination registers holding the packed pairs `.pair (F l r 0) (F l r 1)`. -/
theorem afterMatrix_bf16 (t : TState) {ds : List Nat} (hds : ds.length = 4)
    (F : Nat → Nat → Nat → ℝ) (l : Nat) :
    afterMatrix t 32 ds (regPart (fragRegs bf16Enc F) l) =
      next (setRegs { t with sub := 0, acc := [] } ds
        ((List.range 4).map fun r => bf16Pair (F l r 0) (F l r 1))) := by
  have hlen : (regPart (fragRegs bf16Enc F) l).length = ds.length * (32 / 8) := by
    simp [regPart, hds]
  have hm : ((List.range ds.length).map fun r =>
      ((regPart (fragRegs bf16Enc F) l).drop (r * (32 / 8))).take (32 / 8)).mapM (rebuild 3) =
      .ok ((List.range 4).map fun r => bf16Pair (F l r 0) (F l r 1)) := by
    rw [hds]
    change [_, _, _, _].mapM (rebuild 3) = _
    simp only [List.mapM_cons, List.mapM_nil]
    change (do
      let a ← rebuild 3 [bf16Enc (F l 0 0) 0, bf16Enc (F l 0 0) 1, bf16Enc (F l 0 1) 0,
        bf16Enc (F l 0 1) 1]
      let b ← (do
        let a ← rebuild 3 [bf16Enc (F l 1 0) 0, bf16Enc (F l 1 0) 1, bf16Enc (F l 1 1) 0,
          bf16Enc (F l 1 1) 1]
        let b ← (do
          let a ← rebuild 3 [bf16Enc (F l 2 0) 0, bf16Enc (F l 2 0) 1, bf16Enc (F l 2 1) 0,
            bf16Enc (F l 2 1) 1]
          let b ← (do
            let a ← rebuild 3 [bf16Enc (F l 3 0) 0, bf16Enc (F l 3 0) 1, bf16Enc (F l 3 1) 0,
              bf16Enc (F l 3 1) 1]
            let b ← pure []
            pure (a :: b))
          pure (a :: b))
        pure (a :: b))
      pure (a :: b)) = _
    simp only [rebuild_bf16Pair]
    rfl
  unfold afterMatrix
  simp only [hlen, ite_true, hm]

/-- **The register after `movmatrix` of bf16 elements.** A lane that receives the register
bytes of the fragment `F` of bf16 payloads (`mov_elems` with `enc := bf16Enc`) continues with
its destination register holding the packed pair `.pair (F l 0) (F l 1)`. -/
theorem afterMatrix_bf16_one (t : TState) (d : Nat) (F : Nat → Nat → ℝ) (l : Nat) :
    afterMatrix t 32 [d] (reg1Part (fragReg1 bf16Enc F) l) =
      next (setRegs { t with sub := 0, acc := [] } [d] [bf16Pair (F l 0) (F l 1)]) := by
  have hm : ((List.range [d].length).map fun r =>
      ((reg1Part (fragReg1 bf16Enc F) l).drop (r * (32 / 8))).take (32 / 8)).mapM (rebuild 3) =
      .ok [bf16Pair (F l 0) (F l 1)] := by
    change (do
      let a ← rebuild 3 [bf16Enc (F l 0) 0, bf16Enc (F l 0) 1, bf16Enc (F l 1) 0,
        bf16Enc (F l 1) 1]
      let b ← pure []
      pure (a :: b)) = _
    rw [rebuild_bf16Pair]
    rfl
  have hlen : (reg1Part (fragReg1 bf16Enc F) l).length = [d].length * (32 / 8) := by
    simp [reg1Part]
  unfold afterMatrix
  simp only [hlen, ite_true, hm]

end PTX.WarpMatrix
