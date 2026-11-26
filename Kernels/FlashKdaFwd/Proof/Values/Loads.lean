-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Forms
public import Lemmas.Matrix.Vals

@[expose] public section

/-!
# The matrix loads of a tile: what the rows hold and what the registers receive

An `ldmatrix` of a compute warp reads sixteen-byte rows of shared memory: lane `8 q + i` reads
row `i` of the 8 × 8 matrix `q` (`q` is 0 to 3), eight 16-bit elements. `LoadSrc` names what the
44 loads of a tile read, in the notation of `Math/FragmentsLayout.lean`:

* `tilesA M`: the four tiles of an A operand `M` (a block of `k_decayed` or `q_decayed`, `INV`,
  `Mqk`), bfloat16 payloads;
* `state bi m`: the rows of `state_acc` of key block `m` for the value block `bi` of the warp,
  bfloat16 payloads (two B operands, one per half);
* `restored m`: the tiles of key block `m` of `k_restored`, loaded with the transposing form;
* `values bi`: the block of `v` of value block `bi`: bit patterns, or payload zeros where the
  tensor load was out of bounds. Its registers are not payloads; only its forms are stated here.

For a source of payloads: `LoadSrc.row` is the row a lane reads, `LoadSrc.vals` the four values
its destination registers receive, `LoadSrc.forms` the forms of these registers, and
`LoadSrc.forms_hold` says the values satisfy the forms. `LoadSrc.recv`, `LoadSrc.vals_ok` state
what the lane receives when every lane contributes its row, and what the machine records.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX PTX.Flow PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Math.Fragments

noncomputable section

/-- What an `ldmatrix` of the tile loop reads. -/
inductive LoadSrc where
  /-- The four 8 × 8 tiles of the A operand `M`. -/
  | tilesA (M : Mat)
  /-- The rows of `state_acc` of key block `m` and value block `bi`. -/
  | state (bi m : ℕ)
  /-- The tiles of key block `m` of `k_restored` (transposing load). -/
  | restored (m : ℕ)
  /-- The block of `v` of value block `bi` (bit patterns). -/
  | values (bi : ℕ)
  deriving DecidableEq, Repr

/-- The load is the transposing form `ldmatrix … .trans`. -/
def LoadSrc.trans : LoadSrc → Bool
  | .restored _ => true
  | _ => false

/-- The rows hold bfloat16 payloads (every source but `v`). -/
def LoadSrc.payload : LoadSrc → Bool
  | .values _ => false
  | _ => true

/-- The four 8 × 8 matrices whose rows the lanes read (`0` for `v`, which is not a payload). -/
def LoadSrc.tiles (x : Inputs) (w : ℕ) : LoadSrc → ℕ → ℕ → ℕ → ℝ
  | .tilesA M => aTiles (M.eval x w)
  | .state bi m => stateTiles x.copy (halfBase w bi 0) m
  | .restored m => restoredTiles x.restoredKey m
  | .values _ => fun _ _ _ => 0

/-- The sixteen bytes of the row lane `l` reads. -/
def LoadSrc.row (x : Inputs) (w l : ℕ) (s : LoadSrc) : List (Option Byte) :=
  rowPart (matRows bf16Enc (s.tiles x w)) l

/-- The fragments the destination registers hold after the load. -/
def LoadSrc.frag (x : Inputs) (w : ℕ) (s : LoadSrc) : ℕ → ℕ → ℕ → ℝ :=
  toFrag (if s.trans then transposeMats (s.tiles x w) else s.tiles x w)

/-- The values of the four destination registers of lane `l` after the load. -/
def LoadSrc.vals (x : Inputs) (w l : ℕ) (s : LoadSrc) : List Value :=
  (List.range 4).map fun r => bf16Pair (s.frag x w l r 0) (s.frag x w l r 1)

/-- The forms of the four destination registers. -/
def LoadSrc.forms : LoadSrc → List Form
  | .tilesA M => [.regA M 0, .regA M 1, .regA M 2, .regA M 3]
  | .state bi m => [.regB (.stateBlock bi 0 m) 0, .regB (.stateBlock bi 0 m) 1,
      .regB (.stateBlock bi 1 m) 0, .regB (.stateBlock bi 1 m) 1]
  | .restored m => [.regA (.keyBlockT m) 0, .regA (.keyBlockT m) 1, .regA (.keyBlockT m) 2,
      .regA (.keyBlockT m) 3]
  | .values bi => [.rawA bi 0, .rawA bi 1, .rawA bi 2, .rawA bi 3]

theorem LoadSrc.forms_length (s : LoadSrc) : s.forms.length = 4 := by cases s <;> rfl

theorem LoadSrc.vals_length (x : Inputs) (w l : ℕ) (s : LoadSrc) : (s.vals x w l).length = 4 :=
  by simp [LoadSrc.vals]

/-- Every byte of a row of payloads is known. -/
theorem LoadSrc.row_all (x : Inputs) (w l : ℕ) (s : LoadSrc) :
    (s.row x w l).all Option.isSome = true := by
  simp [LoadSrc.row, rowPart, matRows, bf16Enc]

/-- **The destination registers of a load of payloads satisfy their forms**: the tiles of an A
operand give `regA`, the rows of the state give the B operands of the two halves
(`stateTiles_frag`), the transposed tiles of `k_restored` give `regA` of `keyBlockT`
(`restoredTiles_frag`). -/
theorem LoadSrc.forms_hold (x : Inputs) (w l : ℕ) (s : LoadSrc) (hs : s.payload = true)
    (r : ℕ) (h : r < 4) :
    (s.forms[r]'(by rw [s.forms_length]; exact h)).Holds x w l
      ((s.vals x w l)[r]'(by rw [s.vals_length]; exact h)) := by
  have hv : (s.vals x w l)[r]'(by rw [s.vals_length]; exact h) =
      bf16Pair (s.frag x w l r 0) (s.frag x w l r 1) := by
    simp [LoadSrc.vals]
  rw [hv]
  cases s with
  | tilesA M =>
    interval_cases r <;> rfl
  | state bi m =>
    have key : ∀ r hh, LoadSrc.frag x w (.state bi m) l r hh =
        stateBlock x.copy (halfBase w bi (r / 2)) m (bRow l (r % 2) hh) (bCol l) := by
      intro r hh
      change toFrag (stateTiles x.copy (halfBase w bi 0) m) l r hh = _
      rw [stateTiles_frag, halfBase_add]
    interval_cases r <;> simp only [LoadSrc.forms, List.getElem_cons_zero, List.getElem_cons_succ,
      Form.Holds, key] <;> rfl
  | restored m =>
    have key : ∀ r hh, LoadSrc.frag x w (.restored m) l r hh =
        keyBlockT x.restoredKey m (aRow l r) (aCol l r hh) := by
      intro r hh
      exact restoredTiles_frag x.restoredKey m l r hh
    interval_cases r <;> simp only [LoadSrc.forms, List.getElem_cons_zero, List.getElem_cons_succ,
      Form.Holds, key] <;> rfl
  | values bi => cases hs

/-- The register bytes a lane receives from a load whose lanes contribute the rows of `M`. -/
theorem regPart_ldByte (tr : Bool) (M : ℕ → ℕ → ℕ → ℝ) {l : ℕ} (hl : l < 32) :
    regPart (ldByte tr (matRows bf16Enc M)) l =
      regPart (fragRegs bf16Enc (toFrag (if tr then transposeMats M else M))) l := by
  refine List.map_congr_left fun k hk => ?_
  have hk' := List.mem_range.mp hk
  exact ldByte_matRows bf16Enc tr M hl (by omega)

/-- **What the machine records after a load of payloads**: the bytes lane `l` receives when the
lanes contribute the rows of the source rebuild into `LoadSrc.vals`. -/
theorem LoadSrc.vals_ok (x : Inputs) (w : ℕ) (s : LoadSrc) {l : ℕ} (hl : l < 32) :
    matrixVals 32 4 (regPart (ldByte s.trans (matRows bf16Enc (s.tiles x w))) l) =
      .ok (s.vals x w l) := by
  rw [regPart_ldByte s.trans _ hl]
  exact matrixVals_bf16 _ l

/-! ## The rows of `v` -/

/-- The token row of the tile that lane `l` reads in a load of a tile array: lane `8 q + i`
reads row `i` of matrix `q`, and the matrices `q` and `q + 1` hold the rows 0 to 7 and 8 to
15. -/
def rowOfLane (l : ℕ) : ℕ := l % 8 + 8 * (l / 8 % 2)

/-- **The row of `v` that lane `l` reads** (16 bytes: eight consecutive channels of one token
row of value block `bi`): the bytes of eight finite bfloat16 bit patterns that decode to the
values, or, for a token past the end of the array, the bytes of eight bfloat16 payload zeros
(then the values are zero). One row is one token, so the two cases never mix inside a row. -/
def VRow (x : Inputs) (w bi l : ℕ) (row : List (Option Byte)) : Prop :=
  (∃ n : ℕ → ℕ, (∀ j < 8, n j < 65536 ∧ ∃ y : ℚ, FloatFmt.bf16.decode (n j) = some y ∧
        (y : ℝ) = x.value (rowOfLane l) (halfBase w bi 0 + 8 * (l / 16) + j)) ∧
      row = (List.range 16).map fun k =>
        some ((Value.bits 16 (BitVec.ofNat 64 (n (k / 2)))).byteAt (k % 2))) ∨
  ((∀ j < 8, x.value (rowOfLane l) (halfBase w bi 0 + 8 * (l / 16) + j) = 0) ∧
      row = (List.range 16).map fun k => bf16Enc 0 (k % 2))

/-- **The row a lane holds between the two events of a load**: the row of the source, for a
source of payloads; a row of `v` otherwise. -/
def LoadSrc.RowOk (x : Inputs) (w l : ℕ) (s : LoadSrc) (row : List (Option Byte)) : Prop :=
  match s with
  | .values bi => VRow x w bi l row
  | s => row = s.row x w l

theorem LoadSrc.rowOk_payload {x : Inputs} {w l : ℕ} {s : LoadSrc} {row : List (Option Byte)}
    (hs : s.payload = true) : s.RowOk x w l row ↔ row = s.row x w l := by
  cases s <;> first | rfl | cases hs

/-- Every byte of a row of `v` is known. -/
theorem VRow.all {x : Inputs} {w bi l : ℕ} {row : List (Option Byte)} (h : VRow x w bi l row) :
    row.all Option.isSome = true := by
  rcases h with ⟨n, -, rfl⟩ | ⟨-, rfl⟩ <;> simp [bf16Enc]

/-- Every byte of the row a lane holds is known. -/
theorem LoadSrc.RowOk.all {x : Inputs} {w l : ℕ} {s : LoadSrc} {row : List (Option Byte)}
    (h : s.RowOk x w l row) : row.all Option.isSome = true := by
  cases s with
  | values bi => exact VRow.all h
  | tilesA M => have h' : row = _ := h; rw [h']; exact LoadSrc.row_all ..
  | state bi m => have h' : row = _ := h; rw [h']; exact LoadSrc.row_all ..
  | restored m => have h' : row = _ := h; rw [h']; exact LoadSrc.row_all ..

private theorem rows_get {rows : ℕ → ℕ → Option Byte} {s : ℕ} {row : List (Option Byte)}
    (h : rowPart rows s = row) {k : ℕ} (hk : k < 16) : rows s k = row[k]?.join := by
  rw [← h]
  exact (rowPart_get rows s hk).symm

/-- **The registers after the load of `v`.** When every lane contributes a row of `v`
(`VRow`), the bytes lane `l` receives rebuild into four values that satisfy the forms `rawA`:
each register holds two neighbouring elements of one token row, so it is a 32-bit word of two
bit patterns or the pair of two payload zeros (`RawPair`). -/
theorem raw_vals {x : Inputs} {w bi : ℕ} {rows : ℕ → ℕ → Option Byte}
    (hrows : ∀ s < 32, VRow x w bi s (rowPart rows s)) {l : ℕ} (hl : l < 32) :
    ∃ v0 v1 v2 v3, matrixVals 32 4 (regPart (ldByte false rows) l) = .ok [v0, v1, v2, v3] ∧
      (Form.rawA bi 0).Holds x w l v0 ∧ (Form.rawA bi 1).Holds x w l v1 ∧
      (Form.rawA bi 2).Holds x w l v2 ∧ (Form.rawA bi 3).Holds x w l v3 := by
  -- one register: the four bytes of elements `2 t` and `2 t + 1` of the row of lane `8 r + g`
  have key : ∀ r < 4, ∃ v, rebuild 3 [ldByte false rows l r 0, ldByte false rows l r 1,
      ldByte false rows l r 2, ldByte false rows l r 3] = .ok v ∧
      (Form.rawA bi r).Holds x w l v := by
    intro r hr
    have hs : 8 * r + l / 4 < 32 := by omega
    have e0 : rowOfLane (8 * r + l / 4) = aRow l r := by unfold rowOfLane aRow; omega
    have ec : ∀ h < 2, halfBase w bi 0 + 8 * ((8 * r + l / 4) / 16) + (2 * (l % 4) + h) =
        halfBase w bi 0 + aCol l r h := by
      intro h hh
      unfold aCol
      omega
    have hb : ∀ b < 4, ldByte false rows l r b = rows (8 * r + l / 4) (4 * (l % 4) + b) :=
      fun b _ => rfl
    rw [hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega)]
    rcases hrows _ hs with ⟨n, hn, hrow⟩ | ⟨hz, hrow⟩
    · have g : ∀ b < 4, rows (8 * r + l / 4) (4 * (l % 4) + b) =
          some ((Value.bits 16 (BitVec.ofNat 64 (n (2 * (l % 4) + b / 2)))).byteAt (b % 2)) := by
        intro b hb'
        rw [rows_get hrow (by omega)]
        simp only [List.getElem?_map, List.getElem?_range (by omega : 4 * (l % 4) + b < 16),
          Option.map_some, Option.join_some]
        rw [show (4 * (l % 4) + b) / 2 = 2 * (l % 4) + b / 2 by omega,
          show (4 * (l % 4) + b) % 2 = b % 2 by omega]
      rw [g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega)]
      obtain ⟨h0, y0, hy0, hx0⟩ := hn (2 * (l % 4) + 0) (by omega)
      obtain ⟨h1, y1, hy1, hx1⟩ := hn (2 * (l % 4) + 1) (by omega)
      obtain ⟨v, hv, hp⟩ := rebuild_rawPair_bits h0 h1 hy0 hy1 hx0 hx1
      refine ⟨v, hv, ?_⟩
      change RawPair v _ _
      rw [← e0, ← ec 0 (by omega), ← ec 1 (by omega)]
      exact hp
    · have g : ∀ b < 4, rows (8 * r + l / 4) (4 * (l % 4) + b) = bf16Enc 0 (b % 2) := by
        intro b hb'
        rw [rows_get hrow (by omega)]
        simp only [List.getElem?_map, List.getElem?_range (by omega : 4 * (l % 4) + b < 16),
          Option.map_some, Option.join_some]
        rw [show (4 * (l % 4) + b) % 2 = b % 2 by omega]
      rw [g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega)]
      obtain ⟨v, hv, hp⟩ := rebuild_rawPair_zeros
      refine ⟨v, hv, ?_⟩
      change RawPair v _ _
      rw [← e0, ← ec 0 (by omega), ← ec 1 (by omega), hz _ (by omega), hz _ (by omega)]
      exact hp
  obtain ⟨v0, r0, f0⟩ := key 0 (by omega)
  obtain ⟨v1, r1, f1⟩ := key 1 (by omega)
  obtain ⟨v2, r2, f2⟩ := key 2 (by omega)
  obtain ⟨v3, r3, f3⟩ := key 3 (by omega)
  exact ⟨v0, v1, v2, v3,
    matrixVals_x4.mpr ⟨by simp [regPart], _, _, _, _, rfl, r0, r1, r2, r3⟩, f0, f1, f2, f3⟩

/-! ## The matrix stores of a tile -/

/-- What an `stmatrix` of the tile loop writes: the output block of value block `bi` (to the
output stage), or the new state of key block `m` and value block `bi` (transposed, to
`state_acc`). Its four source registers pack the narrowed accumulators of the two halves. -/
inductive StoreSrc where
  | out (bi : ℕ)
  | state (bi m : ℕ)
  deriving DecidableEq, Repr

/-- The store is the transposing form `stmatrix … .trans`. -/
def StoreSrc.trans : StoreSrc → Bool
  | .out _ => false
  | .state .. => true

/-- The matrix of half `q` that the store writes. -/
def StoreSrc.mat : StoreSrc → ℕ → Mat
  | .out bi, q => .output bi q
  | .state bi m, q => .nextState bi q m

/-- The fragments the four source registers hold. -/
def StoreSrc.frag (x : Inputs) (w : ℕ) (s : StoreSrc) : ℕ → ℕ → ℕ → ℝ :=
  pairFrag fun q => (s.mat q).eval x w

/-- The forms of the four source registers. -/
def StoreSrc.forms (s : StoreSrc) : List Form :=
  [.rowPair (s.mat 0) 0, .rowPair (s.mat 0) 1, .rowPair (s.mat 1) 0, .rowPair (s.mat 1) 1]

/-- The sixteen bytes lane `l` receives from the store and writes to its row. -/
def StoreSrc.row (x : Inputs) (w l : ℕ) (s : StoreSrc) : List (Option Byte) :=
  rowPart (matRows bf16Enc
    (if s.trans then transposeMats (ofFrag (s.frag x w)) else ofFrag (s.frag x w))) l

theorem StoreSrc.row_all (x : Inputs) (w l : ℕ) (s : StoreSrc) :
    (s.row x w l).all Option.isSome = true := by
  simp [StoreSrc.row, rowPart, matRows, bf16Enc]

theorem StoreSrc.row_length (x : Inputs) (w l : ℕ) (s : StoreSrc) :
    (s.row x w l).length = 16 := by
  simp [StoreSrc.row, rowPart]

/-- Source registers that satisfy the forms of the store contribute the register bytes of its
fragments. -/
theorem StoreSrc.own {x : Inputs} {w l : ℕ} (s : StoreSrc) {v0 v1 v2 v3 : Value}
    (h0 : (Form.rowPair (s.mat 0) 0).Holds x w l v0)
    (h1 : (Form.rowPair (s.mat 0) 1).Holds x w l v1)
    (h2 : (Form.rowPair (s.mat 1) 0).Holds x w l v2)
    (h3 : (Form.rowPair (s.mat 1) 1).Holds x w l v3) :
    ownBytes [v0, v1, v2, v3] = regPart (fragRegs bf16Enc (s.frag x w)) l := by
  have e0 : v0 = _ := h0
  have e1 : v1 = _ := h1
  have e2 : v2 = _ := h2
  have e3 : v3 = _ := h3
  rw [e0, e1, e2, e3, ← ownBytes_bf16]
  rfl

/-- What a lane receives from a store whose lanes contribute the register bytes of the
fragments: its row. -/
theorem StoreSrc.recv (x : Inputs) (w l : ℕ) (s : StoreSrc) :
    rowPart (stByte s.trans (fragRegs bf16Enc (s.frag x w))) l = s.row x w l :=
  List.map_congr_left fun k _ => stByte_fragRegs bf16Enc s.trans (s.frag x w) l k

/-! ## `movmatrix` of a packed accumulator register -/

/-- A register with the form `rowPair M p` contributes the register bytes of the tile of rows
`8 p` to `8 p + 7` of `M`. -/
theorem rowPair_own {x : Inputs} {w l : ℕ} {M : Mat} {p : ℕ} {v : Value}
    (h : (Form.rowPair M p).Holds x w l v) :
    ownBytes [v] = reg1Part (fragReg1 bf16Enc (toFrag1 (rowTile (M.eval x w) p))) l := by
  have e : v = _ := h
  rw [e, rowPair_eq _ _ _ (by omega : 0 < 2), rowPair_eq _ _ _ (by omega : 1 < 2)]
  exact ownBytes_bf16_one (toFrag1 (rowTile (M.eval x w) p)) l

/-- **The value after `movmatrix` of a packed accumulator register**: the bytes lane `l`
receives rebuild into B register `p` of the matrix. -/
theorem mov_vals (x : Inputs) (w : ℕ) (M : Mat) (p : ℕ) {l : ℕ} (hl : l < 32) :
    matrixVals 32 1 (reg1Part (movByte (fragReg1 bf16Enc
      (toFrag1 (rowTile (M.eval x w) p)))) l) = .ok [regB (M.eval x w) l p] := by
  have h : reg1Part (movByte (fragReg1 bf16Enc (toFrag1 (rowTile (M.eval x w) p)))) l =
      reg1Part (fragReg1 bf16Enc (toFrag1 fun i j => rowTile (M.eval x w) p j i)) l :=
    List.map_congr_left fun b _ => movByte_fragReg1 bf16Enc _ hl b
  rw [h]
  exact matrixVals_bf16_one _ l

/-! ## The scalar loads of a tile -/

/-- What a scalar load of the tile loop reads: the gate logit of row `l / 4 + 8 e` of the tile
(two bytes of the `beta` part of the input stage), or the entry of `g_total` of key feature
`16 m + l / 4 + 8 e` (four bytes). -/
inductive ScalarSrc where
  | logit (e : ℕ)
  | decay (m e : ℕ)
  deriving DecidableEq, Repr

/-- The form of the register the load writes. -/
def ScalarSrc.form : ScalarSrc → Form
  | .logit e => .logitZ e
  | .decay m e => .decay m e

/-- **The bytes a scalar load reads.** A gate logit: the two bytes of a finite bfloat16 bit
pattern that decodes to the logit, or, for a token past the end of the array, the two bytes of
the payload zero (then the logit is zero). An entry of `g_total`: the four bytes of its FP32
payload. -/
def ScalarSrc.Bytes (x : Inputs) (l : ℕ) : ScalarSrc → List (Option Byte) → Prop
  | .logit e, bs =>
      (∃ n < 65536, ∃ y : ℚ, FloatFmt.bf16.decode n = some y ∧ (y : ℝ) = logitAt x l e ∧
        bs = [some ((Value.bits 16 (BitVec.ofNat 64 n)).byteAt 0),
          some ((Value.bits 16 (BitVec.ofNat 64 n)).byteAt 1)]) ∨
      (logitAt x l e = 0 ∧ bs = [bf16Enc 0 0, bf16Enc 0 1])
  | .decay m e, bs =>
      bs = (Value.float .f32 (x.totalDecay (16 * m + l / 4 + 8 * e))).toBytes.map some

/-- The zero-extending 16-bit load of a gate logit writes its bit pattern (form `logitZ`). -/
theorem ScalarSrc.logit_val {x : Inputs} {l e : ℕ} {bs : List (Option Byte)} (w : ℕ)
    (h : (ScalarSrc.logit e).Bytes x l bs) :
    ∃ v, Thread.ldVal (.zero 32) 16 bs = .ok v ∧ (Form.logitZ e).Holds x w l v := by
  rcases h with ⟨n, hn, y, hy, hx, rfl⟩ | ⟨h0, rfl⟩
  · exact ⟨_, ldLogit_bits hn, n, hn, y, rfl, hy, hx⟩
  · exact ⟨_, ldLogit_zero, 0, by norm_num, 0, rfl, bf16_decode_zero, by rw [h0]; norm_num⟩

/-- The 32-bit load of an entry of `g_total` writes its FP32 payload (form `decay`). -/
theorem ScalarSrc.decay_val {x : Inputs} {l m e : ℕ} {bs : List (Option Byte)} (w : ℕ)
    (h : (ScalarSrc.decay m e).Bytes x l bs) :
    ∃ v, rebuild 3 bs = .ok v ∧ (Form.decay m e).Holds x w l v := by
  have h' : bs = _ := h
  exact ⟨_, by rw [h']; exact rebuild_f32 _, rfl⟩

/-- The same, for the form of the load that the machine uses before a run of scalar
instructions (`ldVal .same 32`: no extension). -/
theorem ScalarSrc.decay_val' {x : Inputs} {l m e : ℕ} {bs : List (Option Byte)} (w : ℕ)
    (h : (ScalarSrc.decay m e).Bytes x l bs) :
    ∃ v, Thread.ldVal .same 32 bs = .ok v ∧ (Form.decay m e).Holds x w l v := by
  have h' : bs = _ := h
  refine ⟨_, ?_, rfl⟩
  rw [Thread.ldVal, h', rebuild_f32]
  rfl

end

end PTX.Kernels.FlashKdaFwd.Proof.Values
