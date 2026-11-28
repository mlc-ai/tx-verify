-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Lemmas.Flow.Regs
public import Lemmas.Tmem.AccessCp
import Lemmas.Flow.TcStLen
import Lemmas.Tcgen05.TcDataCell
public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.DataStatic
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount

/-! # The cells of the kernel's `tcgen05.st` stores

The two stores of the softmax warps are `16x32bx2`: the store of the probabilities (pc 1009, 32
registers at the score buffer `ba` of the round, `ba` zero or 128) and the rescale store of the
accumulator (pc 2328, 64 registers at column 256). The cell of register `j` of thread `g` is in
the thread's CTA, in the lane `32 (warp % 4) + lane % 16` and in the column
`ba + (0 or the split) + j`: the cell fixes the thread among the data lanes of its CTA. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.Proof PTX.TcMma

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The cell of a half-split `16x32bx2` access** at `ba + w 2^21` (the base and the split below
the column field). -/
public theorem cell_split (L : Launch) (g ba off w j : Nat) (hba : ba + off < 2 ^ 16) :
    tcDataCell L g (.s16x32bx2 off) (ba + w * 2 ^ 21) j =
      ⟨g / L.block, g % L.block / 32 % 4 * 32 + laneOf L g % 16,
        ba + (if laneOf L g < 16 then 0 else off) + j⟩ := by
  unfold tcDataCell TcShape.base TcShape.columnIn TcShape.laneIn TcShape.lanes chunkOffset laneBase
  by_cases hl : laneOf L g < 16
  · simp only [hl, ↓reduceIte]
    have e1 : (ba + w * 2 ^ 21) / 2 ^ 16 = w * 32 := by omega
    have e2 : (ba + w * 2 ^ 21) % 2 ^ 16 = ba := by omega
    rw [e1, e2]
    have e3 : w * 32 % 32 = 0 := by omega
    have e4 : laneOf L g % 16 = laneOf L g := by omega
    simp only [e3, e4]
    congr 1
  · simp only [hl, ↓reduceIte]
    have e1 : (ba + w * 2 ^ 21 + off) / 2 ^ 16 = w * 32 := by omega
    have e2 : (ba + w * 2 ^ 21 + off) % 2 ^ 16 = ba + off := by omega
    rw [e1, e2]
    have e3 : w * 32 % 32 = 0 := by omega
    simp only [e3]
    congr 1

/-- **Two data lanes of one CTA whose half-split stores share a cell are one thread.** -/
public theorem split_thread {L : Launch} {g h ba off w w' j j' : Nat} (hba : ba + off < 2 ^ 16)
    (hj : j < off) (hj' : j' < off) (hg : g % L.block < 128) (hh : h % L.block < 128)
    (hc : g / L.block = h / L.block)
    (heq : tcDataCell L g (.s16x32bx2 off) (ba + w * 2 ^ 21) j =
      tcDataCell L h (.s16x32bx2 off) (ba + w' * 2 ^ 21) j') : g = h := by
  rw [cell_split L g ba off w j hba, cell_split L h ba off w' j' hba] at heq
  simp only [TcMma.Cell.mk.injEq] at heq
  obtain ⟨h1, h2, h3⟩ := heq
  unfold laneOf at h2 h3
  have : g % L.block = h % L.block := by
    split_ifs at h3 <;> omega
  have hdiv := Nat.div_add_mod g L.block
  have hdiv' := Nat.div_add_mod h L.block
  rw [← hdiv, ← hdiv', hc, this]

/-- **A cell of the kernel's stores**: the store is a data lane's, one of the two sites, and the
cell is the half-split cell of its register. -/
public theorem st_write_cell {x : EvId} {cell : Cell} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) (h : StoreCell L X x cell) :
    x.1 % L.block < 128 ∧ x.1 < L.threads ∧
      ((∃ a vals ba w j, X.get x = some ⟨1009, .tc (.st a vals (.s16x32bx2 32))⟩ ∧
        a = ba + w * 2 ^ 21 ∧ (ba = 0 ∨ ba = 128) ∧ j < 32 ∧
        cell = tcDataCell L x.1 (.s16x32bx2 32) a j) ∨
      ∃ a vals w j, X.get x = some ⟨2328, .tc (.st a vals (.s16x32bx2 64))⟩ ∧
        a = 256 + w * 2 ^ 21 ∧ j < 64 ∧ cell = tcDataCell L x.1 (.s16x32bx2 64) a j) := by
  obtain ⟨g,k⟩ := x
  obtain ⟨a,vals,sh,j,⟨pc,he⟩,hj,hc⟩ := h
  have ly := Export.tc_data_lane hp hX hf he (by rfl)
  refine ⟨ly,Frame.lt_of_get hX he,?_⟩
  obtain ⟨i,w,-,hpc⟩ := st_static hp hX hf base he
  rcases hpc with ⟨rfl,ha,rfl,hl⟩ | ⟨rfl,ha,rfl,hl⟩
  · exact .inr ⟨a,vals,w,j,he,ha,by omega,hc⟩
  · refine .inl ⟨a,vals,i%2*128,w,j,he,by omega,by omega,by omega,hc⟩

end PTX.Kernels.InklingRelDecode.Proof.Tmem
