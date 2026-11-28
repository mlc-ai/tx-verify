-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.QkElems
public import Kernels.InklingRelDecode.Proof.Lib.QueryCoord
import Kernels.InklingRelDecode.Proof.Protocol.Values.QueryElement
import Kernels.InklingRelDecode.Proof.Protocol.Values.QueryTile
import Kernels.InklingRelDecode.Proof.Prologue.Export.QueryWord
import Kernels.InklingRelDecode.Proof.Prologue.Export.QueryLane
import Kernels.InklingRelDecode.Proof.Lib.QkAGeom
import Kernels.InklingRelDecode.Proof.Lib.ZeroElement
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Lemmas.Tcgen05.TcMmaF16Sum

@[expose] public section

/-! # The A elements of a QK MMA are the query elements

The A byte of step `j` at row `row` and column `kk` is a byte of the word the prologue lane
`8 (row % 16) + 2 (j % 4) + kk / 8` stored (`qk_a_geom`), and that word holds the query elements
(`query_word_exact`), or zero for a row that does not load. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX

/-- The A element of the QK issue `i` at row `row`, column `k`: the query element, or zero for a
row that does not load. -/
noncomputable def qkA (Q : Params) (L : Launch) (X : Execution) (i : EvId) (row k : Nat) : ℝ :=
  open Classical in
  if Lib.QRowValid Q L (i.1 / L.block) row then
    Lib.qMat Q L (i.1 / L.block) row (16 * qkStepOf X i + k) else 0

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A byte of the A operand of a QK MMA** is the byte of the query element (or of zero). -/
theorem qk_a_byte (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {g k pc dst s acc mask ops} (he : X.get (g, k) = some ⟨pc, .tc (.mma dst s acc mask)⟩)
    (hops : X.async.mmaOperands (g, k) = some ops) {j : Fin 8} (hj : pc = Lib.qkIssue j)
    {row kk byte : Nat} (hrow : row < 64) (hk : kk < 16) (hb : byte < 2) :
    (Lib.QRowValid Q L (g / L.block) row → ops.a[2 * (row * 16 + kk) + byte]? =
      some (some ((Value.float .bf16
        (Lib.qMat Q L (g / L.block) row (16 * j.val + kk))).byteAt byte))) ∧
    (¬ Lib.QRowValid Q L (g / L.block) row → ops.a[2 * (row * 16 + kk) + byte]? =
      some (some (Value.bits 32 (BitVec.ofNat 64 0), 2 * (kk % 2) + byte))) := by
  obtain ⟨b, -, -, -, -, desc⟩ := Mma.Export.qk_block hp hX hf base he ⟨j, hj⟩
  obtain ⟨-, hsa, -⟩ := desc j hj
  obtain ⟨-, hlo, -, b2, hd⟩ := Mma.Export.columns hp hX hf base he
  have ne : ∀ j j' : Fin 8, Lib.qkIssue j ≠ Lib.pvIssue j' := by decide
  obtain ⟨hat, hD⟩ : s.aTmem = none ∧ s.descriptor = Lib.qkDesc := by
    rcases hd with ⟨j', -, -, hat, hD⟩ | ⟨j', hpc, -⟩
    · exact ⟨hat, hD⟩
    · exact absurd (hj.symm.trans hpc) (ne j j')
  have hl := Lib.qk_a_addr hD hat hsa hrow hk hb
  obtain ⟨g1, k1, a1, bs1, i1, get1, cov, sz, -, ob⟩ :=
    query_byte hp hX hf (query_tile hp hX hf words) he hops hl
  obtain ⟨jw, loc, pair, zero⟩ := Prologue.Export.query_word_exact hp hX hf get1
  have lane := Prologue.Export.query_lane hp hX hf get1
  obtain ⟨-, ct, lo, hi⟩ := cov
  simp only [sz, loc] at ct lo hi
  simp only [wbyte, loc] at ob
  have al := hp.sharedAlignment
  generalize hO : TensorSwizzle.offset .b128 0 (((L.sharedBase + 196608) / 16 +
    (2 * (j.val % 4) + 512 * (j.val / 4))) * 16 + (128 * (row % 8) + 1024 * (row / 8) + 2 * kk) +
    byte) = O at lo hi ob
  obtain ⟨hi1, ht1, hw1, hb1⟩ := Lib.qk_a_geom (t := g1 % L.block) (i := i1.val) (w := jw.val)
    (b := O - (L.sharedBase + Lib.qSwz (g1 % L.block) + (196608 + 2048 * Lib.qGroup i1.val) +
      4 * jw.val)) al j.isLt hrow hk hb lane i1.isLt jw.isLt (by omega) (by omega)
  have hc : g1 / L.block = g / L.block := ct.symm.trans hlo
  have hrw : Lib.qTileRow (g1 % L.block) (i1.val / 2) = row := by
    unfold Lib.qTileRow
    generalize g1 % L.block = t at ht1
    omega
  have hv' : Lib.QValid Q L g1 (i1.val / 2) = Lib.QRowValid Q L (g / L.block) row := by
    unfold Lib.QValid
    rw [hrw, hc]
  have idx : O - (L.sharedBase + Lib.qSwz (g1 % L.block) + (196608 + 2048 * Lib.qGroup i1.val) +
      4 * jw.val) = 2 * (kk % 2) + byte := hb1
  rw [idx] at ob
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  swap
  · rw [ob, zero (by rw [hv']; exact hv) _ (by omega)]
  have pr := pair (by rw [hv']; exact hv) byte hb
  rw [ob]
  have pos := Lib.qElem_pos (Q := Q) (L := L) (g := g1) j.isLt hrow hk ht1
  rcases Nat.mod_two_eq_zero_or_one kk with h2 | h2
  · rw [h2, Nat.mul_zero, Nat.zero_add, pr.1,
      show 8 * i1.val + 2 * jw.val = 8 * (2 * (row / 16) + j.val / 4) + 2 * (kk % 8 / 2) +
        kk % 2 by omega, pos, hc]
  · rw [h2, Nat.mul_one, pr.2,
      show 8 * i1.val + 2 * jw.val + 1 = 8 * (2 * (row / 16) + j.val / 4) + 2 * (kk % 8 / 2) +
        kk % 2 by omega, pos, hc]

/-- **The `Ea` hypothesis of `ld_s_real`.** -/
theorem qk_a_ideal (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {i d s acc mask ops row k} (hq : QkIssue X i) (hi : X.MmaIssue i d s acc mask)
    (hops : X.async.mmaOperands i = some ops) (hrow : row < 64) (hk : k < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok (qkA Q L X i row k) := by
  obtain ⟨g, k0⟩ := i
  obtain ⟨pc, he⟩ := hi
  obtain ⟨pc', d', s', acc', mask', he', j, hj⟩ := hq
  obtain ⟨rfl, -⟩ := Event.mk.inj (Option.some.inj (he.symm.trans he'))
  have byte := fun z (hz : z < 2) => qk_a_byte hp hX hf words base he hops hj hrow hk hz
  simp only [qkA, qkStepOf, he, Option.map_some, Option.getD_some, hj, qkStep_qkIssue]
  by_cases hv : Lib.QRowValid Q L (g / L.block) row
  · simp only [hv, ↓reduceIte]
    exact TcMma.element_of_bytes (Or.inr rfl) fun z hz => (byte z hz).1 hv
  · simp only [hv, ↓reduceIte]
    exact Lib.zero_elem (p := 2 * (k % 2)) (by omega) (by simpa using (byte 0 (by omega)).2 hv)
      ((byte 1 (by omega)).2 hv)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
