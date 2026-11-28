-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.PWords
public import Kernels.InklingRelDecode.Proof.Iface.RescaleWords
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.QkStore
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccSource
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! # The store a MMA's accumulator read takes its word from

The source of an accumulator read that is a store is the rescale store (pc 2328): a probability
store (pc 1009) writes columns below 256, which only QK steps read, and a QK step that accumulates
has its block's previous step as a write before it, so by the rounds (`qk_store_round`) a store
before the step is before the previous step too. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma Tmem

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A probability store is not the source of a QK step's accumulator read.** -/
theorem pst_not_acc_source (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (hG : SyncGuarded L kernel X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    {i src : EvId} {cell : Cell} {a vals sh}
    (hrd : X.MmaReadCell i cell) (hs : ReadSource L X .acc src i cell)
    (hy : X.get src = some ⟨1009, .tc (.st a vals sh)⟩)
    (hcell : ∃ ba w j, (ba = 0 ∨ ba = 128) ∧ a = ba + w * 2 ^ 21 ∧ j < 32 ∧
      cell = tcDataCell L src.1 (.s16x32bx2 32) a j) : False := by
  obtain ⟨g, kp⟩ := i
  have cyc : ∀ {x y : EvId}, Relation.TransGen (TcStep L X) x y →
      Relation.TransGen (TcStep L X) y x → False := fun h1 h2 =>
    tcStep_acyclic hX hG _ (h1.trans h2)
  obtain ⟨ba, w, j, hba, rfl, hj, hc⟩ := hcell
  obtain ⟨c1, c2, c3⟩ := p_cols (L := L) (g := src.1) (w := w) hba hj
  rw [← hc] at c1 c2 c3
  have hmc := mma_read_write hp hX hf base hrd
  obtain ⟨pc1, d1, s1, acc1, mask1, he1, cta, lo, hi, -, -, kind⟩ :=
    mma_write_cell hp hX hf base hmc
  obtain ⟨d0, s0, mask0, row, col, ⟨pc0, he0⟩, -⟩ := id hrd
  rw [he1] at he0
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he0
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he0
  rcases kind with ⟨jq, hpc, hd, -⟩ | ⟨jp, -, hd, -⟩
  swap
  · omega
  obtain ⟨kR, lt, ⟨j', d', s', a', m', get0⟩, pe, hw0, hwb0⟩ :=
    qk_prev hp hX hf hu base hrd he1 hpc
  have hd1 : d1 = ba := by omega
  obtain ⟨b, hbd, q1, -⟩ := Mma.Export.qk_block hp hX hf base he1 ⟨jq, hpc⟩
  obtain ⟨b', hbd', q1', -⟩ := Mma.Export.qk_block hp hX hf base get0 ⟨j', rfl⟩
  have hbb : b' = b := by omega
  have hd2 : d' = ba := by rw [hbd', hbb, ← hbd, hd1]
  have hmod : (ba + w * 2 ^ 21) % 2 ^ 21 = ba := by omega
  have ctax : (g, kp).1 / L.block = src.1 / L.block := by rw [← c3]; exact cta.symm
  obtain ⟨bx, r, pb, s1', -, o1⟩ := qk_store_round hp hX hf safe base rows init he1 ⟨jq, hpc⟩ hy
    ctax (by rw [hmod, hd1])
  obtain ⟨bx', r', pb', s2', -, o0⟩ := qk_store_round hp hX hf safe base rows init get0 ⟨j', rfl⟩ hy
    ctax (by rw [hmod, hd2])
  simp only at pb pb' s1' s2' q1 q1'
  have hrr : r' = r := by omega
  have hbx : bx' = bx := by omega
  subst hbx
  subst hrr
  obtain ⟨hne, -, hwb, h4, -⟩ := readSource_acc.mp hs
  rcases h4 (g, kR) hw0 with h | h | h | h
  · rw [h, hy] at get0
    simp at get0
  · simp only [Prod.mk.injEq, true_and] at h
    omega
  · rcases o1 with ⟨-, dn⟩ | ⟨l1, -⟩
    · exact cyc dn.tcStep hwb.tcStep
    · rcases o0 with ⟨l0, -⟩ | ⟨-, sd⟩
      · omega
      · exact cyc sd.tcStep h.tcStep
  · exact cyc h.tcStep hwb0.tcStep

/-- **The `store` field of `Elements`**: the word of a store that is the source of an accumulator
read is an f32 number, given that the rescale store writes them. -/
theorem store_element (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (hG : SyncGuarded L kernel X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    {i src : EvId} {cell : Cell} {old : Value} (hrd : X.MmaReadCell i cell)
    (hs : ReadSource L X .acc src i cell) (hv : StoreValue L X src cell old)
    (W : ∀ {a vals sh}, X.get src = some ⟨2328, .tc (.st a vals sh)⟩ →
      ∀ v ∈ vals, ∃ r : ℝ, v = .float .f32 r) :
    ∃ r : ℝ, valFloat .f32 old = .ok r := by
  obtain ⟨a, vals, sh, j, ⟨pc, hst⟩, hj, hc⟩ := hv
  have hlen : j < vals.length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨-, -, h1 | h2⟩ := st_write_cell hp hX hf base (x := src) (cell := cell)
    ⟨a, vals, sh, j, ⟨pc, hst⟩, hlen, hc⟩
  · obtain ⟨a', vals', ba, w, j', g1, ha, hba, hj', hc'⟩ := h1
    exact (pst_not_acc_source hp hX hf hu hG safe base rows init hrd hs g1
      ⟨ba, w, j', hba, ha, hj', hc'⟩).elim
  · obtain ⟨a', vals', w, j', g2, -⟩ := h2
    rw [hst] at g2
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at g2
    obtain ⟨rfl, rfl, rfl, -⟩ := g2
    obtain ⟨r, hr⟩ := W hst _ (List.mem_of_getElem? hj)
    exact ⟨r, by rw [hr]; rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
