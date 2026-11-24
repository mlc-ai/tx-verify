-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Def
public import Core.Data.Events
import Kernels.TmlFa4Fwd.Proof.Lib.SmemElements
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Lemmas.Tcgen05.TcMmaF16Pair
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The shared operand elements of the MMAs

A stage of Q, a K block and a V block have 128 rows of 128 columns in two 16384-byte boxes of 64
columns, with the 128-byte swizzle: byte `z` of element `(row, d)` of a block at `base` is at
`blockAddr base row d z`. The operand elements of the MMAs are elements of these blocks: element
`(row, c)` of A of QK step `j` is element `(row, 16 j + c)` of the Q stage, element `(col, c)` of
its B is element `(col, 16 j + c)` of the K block of its tile, and element `(col, c)` of B of PV
step `j` is element `(16 j + c, col)` of the V block of its tile. So the elements are the blocks'
contents (`qk_a`, `qk_b`, `pv_b`) when the operand bytes are the bytes that the copies wrote
(`OperandBytes`), and they are numbers (`smemElements`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm

noncomputable section

/-- **The blocks a CTA's loader warps load**: query row `row` of stage `st`, key `col` and value row
`key` of the K/V block of tile `u`. -/
structure Inputs where
  q : Nat → Nat → Nat → ℝ
  k : Nat → Nat → Nat → ℝ
  v : Nat → Nat → Nat → ℝ

/-- The address of byte `z` of element `(row, d)` of a block at `base`. -/
def blockAddr (base row d z : Nat) : Nat :=
  base + 16384 * (d / 64) + TensorSwizzle.offset .b128 (base + 16384 * (d / 64))
    (128 * row + 2 * (d % 64) + z)

/-- A byte of a block of a CTA. -/
abbrev blockLoc (c base row d z : Nat) : Loc := ⟨.shared, c, blockAddr base row d z⟩

/-- The blocks of Q stage `st` and of K/V ring slot `s`. -/
abbrev qBase (L : Launch) (st : Nat) : Nat := L.sharedBase + 3072 + 32768 * st
abbrev kvBase (L : Launch) (s : Nat) : Nat := L.sharedBase + 68608 + 32768 * s

/-- The two bytes from `n` on are those of the BF16 number `x`. -/
def Elem16 (bs : List (Option Byte)) (n : Nat) (x : ℝ) : Prop :=
  ∃ b0 b1, bs[n]? = some b0 ∧ bs[n + 1]? = some b1 ∧
    (rebuild 1 [b0, b1] >>= valFloat .bf16) = .ok x

/-- **The operand elements of the completed MMAs are the copies'**: the elements of the Q stage, of
the K block of the tile and of the V block of the tile (ring uses `2 u` and `2 u + 1`). The sources
of the tensor copies and of the row copies give the blocks' contents. -/
structure OperandBytes (I : Nat → Inputs) (L : Launch) (X : Execution) : Prop where
  q : ∀ {g k st u : Nat} {j : Fin 8} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {ops : AsyncCopy.MmaOperands} {index row c : Nat}, st < 2 → Qk L X g k st u j
        →
    X.MmaIssue (g, k) d s acc mask → X.async.mmaDone (g, k) = true →
    X.async.mmaOperands (g, k) = some ops → row < 128 → c < 128 →
    (∀ z < 2, s.byteLoc .a (index + z) = some (blockLoc (g / L.block) (qBase L st) row c z)) →
    Elem16 ops.a index ((I (g / L.block)).q st row c)
  k : ∀ {g k st u : Nat} {j : Fin 8} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {ops : AsyncCopy.MmaOperands} {index col c : Nat}, st < 2 → Qk L X g k st u j
        →
    X.MmaIssue (g, k) d s acc mask → X.async.mmaDone (g, k) = true →
    X.async.mmaOperands (g, k) = some ops → col < 128 → c < 128 →
    (∀ z < 2, s.byteLoc .b (index + z) = some (blockLoc (g / L.block) (kvBase L (2 * u % 3)) col c
        z)) →
    Elem16 ops.b index ((I (g / L.block)).k u col c)
  v : ∀ {g k st u : Nat} {j : Fin 8} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {ops : AsyncCopy.MmaOperands} {index key c : Nat}, st < 2 → Pv L X g k st u j
        →
    X.MmaIssue (g, k) d s acc mask → X.async.mmaDone (g, k) = true →
    X.async.mmaOperands (g, k) = some ops → key < 128 → c < 128 →
    (∀ z < 2, s.byteLoc .b (index + z) = some (blockLoc (g / L.block) (kvBase L ((2 * u + 1) % 3))
        key c z)) →
    Elem16 ops.b index ((I (g / L.block)).v u key c)

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {I : Nat → Inputs}

/-- A byte of a K-major operand. -/
private theorem k_byteLoc {s : OperandSpec} {c : Nat} {op : Operand} (hD : s.descriptor = qkDsc)
    (hl : s.lowCta = c) (haT : s.aTmem = none) {base j : Nat}
    (hs : op.major s.descriptor = .k ∧ (match op with | .a => s.a | .b => s.b) =
      kDesc (base + 16384 * (j / 4) + 32 * (j % 4))) (hb : base % 128 = 0)
    {y k z : Nat} (hy : y < 128) (hk : k < 16) (hz : z < 2) :
    s.byteLoc op (2 * (y * 16 + k) + z) = some (blockLoc c base y (16 * j + k) z) := by
  have hd1 : (16 * j + k) / 64 = j / 4 := by omega
  have hd2 : (16 * j + k) % 64 = 16 * (j % 4) + k := by omega
  have haddr := k_byteAddress (base := base + 16384 * (j / 4)) (c := 16 * (j % 4)) (y := y) (k := k)
    (z := z) (by omega) hz
  rw [show 2 * (16 * (j % 4)) = 32 * (j % 4) by ring] at haddr
  have hdiv : (2 * (y * 16 + k) + z) / (16 * 2) = y := by omega
  have hkdiv : (2 * (y * 16 + k) + z) / 2 % 16 = k := by omega
  have hbmod : (2 * (y * 16 + k) + z) % 2 = z := by omega
  have hv := qkDsc_valid
  unfold OperandSpec.byteLoc blockLoc blockAddr
  obtain ⟨-, hs⟩ := hs
  cases op <;>
    simp only [hD, qkDsc, Kind.k, Kind.width, Operand.extent, CtaGroup.size, hdiv, Operand.major,
      hkdiv, hbmod, hs, haT, hl, hd1, hd2] at hv ⊢ <;>
    simp [hv, hy, Nat.mod_eq_of_lt hy, haddr]

/-- A byte of an MN-major operand. -/
private theorem mn_byteLoc {s : OperandSpec} {c : Nat} (hD : s.descriptor = pvDsc)
    (hl : s.lowCta = c) {base j : Nat} (hs : s.b = mnDesc (base + 2048 * j))
    (hb : base % 128 = 0) {y' k z : Nat} (hy' : y' < 128) (hk : k < 16) (hz : z < 2) :
    s.byteLoc .b (2 * (y' * 16 + k) + z) = some (blockLoc c base (16 * j + k) y' z) := by
  obtain ⟨r, y, hr, hy, rfl⟩ : ∃ r y, r < 2 ∧ y < 64 ∧ y' = 64 * r + y :=
    ⟨y' / 64, y' % 64, by omega, Nat.mod_lt _ (by decide), by omega⟩
  have hd1 : (64 * r + y) / 64 = r := by omega
  have hd2 : (64 * r + y) % 64 = y := by omega
  have haddr := mn_byteAddress (base := base + 2048 * j) (r := r) (y := y) (k := k) (z := z)
    (by omega) hy hz
  have e1 := TensorSwizzle.offset_add_base .b128 (base + 2048 * j + 16384 * r)
    (128 * k + 2 * y + z) (by omega)
  have e2 := TensorSwizzle.offset_add_base .b128 (base + 16384 * r)
    (128 * (16 * j + k) + 2 * y + z) (by omega)
  have e3 : base + 2048 * j + 16384 * r + (128 * k + 2 * y + z) =
      base + 16384 * r + (128 * (16 * j + k) + 2 * y + z) := by ring
  rw [← e1, e3, e2] at haddr
  have hdiv : (2 * ((64 * r + y) * 16 + k) + z) / (16 * 2) = 64 * r + y := by omega
  have hkdiv : (2 * ((64 * r + y) * 16 + k) + z) / 2 % 16 = k := by omega
  have hbmod : (2 * ((64 * r + y) * 16 + k) + z) % 2 = z := by omega
  have hext : 64 * r + y < 128 := by omega
  have hv := pvDsc_valid
  unfold OperandSpec.byteLoc blockLoc blockAddr
  simp only [hD, pvDsc, Kind.k, Kind.width, Operand.extent, CtaGroup.size, hdiv, Operand.major,
    hkdiv, hbmod, hs, hl, hd1, hd2] at hv ⊢
  simp [hv, hext, Nat.mod_eq_of_lt hext, haddr]

section
variable (hp : Pre p L m) (hI : OperandBytes I L X)
include hp hI

/-- **An element of A of a QK MMA.** -/
theorem qk_a {g k st u : Nat} {j : Fin 8} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {ops : AsyncCopy.MmaOperands} {row c : Nat} (hst : st < 2)
    (hq : Qk L X g k st u j) (hi : X.MmaIssue (g, k) d s acc mask)
    (hd : X.async.mmaDone (g, k) = true) (hops : X.async.mmaOperands (g, k) = some ops)
    (hrow : row < 128) (hc : c < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row c =
      .ok ((I (g / L.block)).q st row (16 * j.val + c)) := by
  have hj := j.isLt
  have hs := hp.shared.1
  obtain ⟨b0, b1, e0, e1, hx⟩ := hI.q (index := 2 * (row * 16 + c)) (c := 16 * j.val + c) hst hq hi
      hd
    hops hrow (by omega) fun z hz => by
      obtain ⟨-, -, -, rfl⟩ := hq.spec_eq hi
      exact k_byteLoc (op := .a) rfl rfl rfl ⟨rfl, rfl⟩ (by unfold qBase; omega) hrow hc hz
  exact element_of_pair e0 e1 hx

/-- **An element of B of a QK MMA.** -/
theorem qk_b {g k st u : Nat} {j : Fin 8} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {ops : AsyncCopy.MmaOperands} {col c : Nat} (hst : st < 2)
    (hq : Qk L X g k st u j) (hi : X.MmaIssue (g, k) d s acc mask)
    (hd : X.async.mmaDone (g, k) = true) (hops : X.async.mmaOperands (g, k) = some ops)
    (hcol : col < 128) (hc : c < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col c =
      .ok ((I (g / L.block)).k u col (16 * j.val + c)) := by
  have hj := j.isLt
  have hs := hp.shared.1
  obtain ⟨b0, b1, e0, e1, hx⟩ := hI.k (index := 2 * (col * 16 + c)) (c := 16 * j.val + c) hst hq hi
      hd
    hops hcol (by omega) fun z hz => by
      obtain ⟨-, -, -, rfl⟩ := hq.spec_eq hi
      exact k_byteLoc (op := .b) rfl rfl rfl ⟨rfl, rfl⟩ (by unfold kvBase; omega) hcol hc hz
  exact element_of_pair e0 e1 hx

/-- **An element of B of a PV MMA.** -/
theorem pv_b {g k st u : Nat} {j : Fin 8} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} {ops : AsyncCopy.MmaOperands} {col c : Nat} (hst : st < 2)
    (hq : Pv L X g k st u j) (hi : X.MmaIssue (g, k) d s acc mask)
    (hd : X.async.mmaDone (g, k) = true) (hops : X.async.mmaOperands (g, k) = some ops)
    (hcol : col < 128) (hc : c < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col c =
      .ok ((I (g / L.block)).v u (16 * j.val + c) col) := by
  have hj := j.isLt
  have hs := hp.shared.1
  obtain ⟨b0, b1, e0, e1, hx⟩ := hI.v (index := 2 * (col * 16 + c)) (key := 16 * j.val + c) (c :=
      col)
    hst hq hi hd hops (by omega) hcol fun z hz => by
      obtain ⟨-, -, -, rfl⟩ := hq.spec_eq hi
      exact mn_byteLoc rfl rfl rfl (by unfold kvBase; omega) hcol hc hz
  exact element_of_pair e0 e1 hx

/-- **The shared operand elements are numbers.** -/
theorem smemElements (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X) :
    SmemElements X := by
  rintro ⟨g, k⟩ d s acc mask ops row c hi hd hops hrow hc
  obtain ⟨-, st, u, j, hst, hq | hq⟩ := mma_qkpv hp hX hFw ⟨_, _, _, _, hi⟩
  · exact ⟨⟨_, qk_b hp hI hst hq hi hd hops hrow hc⟩,
      fun _ => ⟨_, qk_a hp hI hst hq hi hd hops hrow hc⟩⟩
  · refine ⟨⟨_, pv_b hp hI hst hq hi hd hops hrow hc⟩, fun h => ?_⟩
    obtain ⟨-, -, -, rfl⟩ := hq.spec_eq hi
    cases h

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
