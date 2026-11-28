-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.Wrote
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
public import Lemmas.Tcgen05.TcMmaIdealEval
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder

@[expose] public section

/-! # The source of an accumulator read is done

An accumulator read's source MMA is done: by the observed commit, or by the D to D pipeline with the
reader (an earlier MMA of the lane with the same accumulator), whose completion the done reader
forces (`CompletionClosed`). The two MMAs have the same footprint: their descriptors are those of
their D column class (QK below 256, PV at 256), and their masks are zero. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.TcMma

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The descriptor, masks and CTAs of an MMA writing a cell are determined by its D column. -/
theorem mma_class (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {x : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat} {pc : Nat}
    (he : X.get x = some ⟨pc, .tc (.mma d s acc mask)⟩) :
    mask = [0, 0, 0, 0] ∧ s.lowCta = x.1 / L.block ∧ s.highCta = x.1 / L.block ∧
      ((d < 256 ∧ s.descriptor = Lib.qkDesc) ∨ (d = 256 ∧ s.descriptor = Lib.pvDesc)) := by
  obtain ⟨g, k⟩ := x
  obtain ⟨hmask, lo, hi, b, qk | pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j, -, hd, -, desc⟩ := qk
    exact ⟨hmask, lo, hi, .inl ⟨by omega, desc⟩⟩
  · obtain ⟨j, -, hd, -, desc⟩ := pv
    exact ⟨hmask, lo, hi, .inr ⟨hd, desc⟩⟩

/-- **An accumulator read's source MMA is done**, given the reader is. -/
theorem acc_mma_done (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some) (hG : SyncGuarded L kernel X)
    {r : EvId} {cell : Cell} (hdr : X.async.mmaDone r = true) (hr : X.MmaReadCell r cell)
    {src : EvId} (hs : ReadSource L X .acc src r cell) (hm : X.MmaCell src cell) :
    X.async.mmaDone src = true := by
  have hrw := mma_read_write hp hX hf base hr
  rcases hs.2.2.1 with (hdn | hpl) | ⟨⟨a', vals', sh', hst⟩, -⟩ | ⟨-, -, c, d, s, acc, mask, hcc, -⟩
  · exact hdn.done hX.tcCommit
  · obtain ⟨hw, hbc, d1, s1, a1, m1, d2, s2, a2, m2, ⟨p1, h1⟩, ⟨p2, h2⟩, same⟩ := id hpl
    obtain ⟨d0, s0, a0, m0, row, col, ⟨pc0, h0⟩, hc0⟩ := hm
    obtain ⟨dr, sr, ar, mr, rowr, colr, ⟨pcr, hr0⟩, hcr⟩ := hrw
    have e1 := get_tc_inj h0 h1
    have e2 := get_tc_inj hr0 h2
    simp only [TcKind.mma.injEq] at e1 e2
    obtain ⟨hd1, hs1, -, hm1⟩ := e1
    obtain ⟨hd2, hs2, -, hm2⟩ := e2
    subst hd1 hs1 hm1 hd2 hs2 hm2
    obtain ⟨hmk1, lo1, hi1, c1⟩ := mma_class hp hX hf base h0
    obtain ⟨hmk2, lo2, hi2, c2⟩ := mma_class hp hX hf base hr0
    have cta : src.1 / L.block = r.1 / L.block :=
      ((mma_cells hp hX hf base (.inl ⟨_, _, _, _, row, col, ⟨_, h0⟩, hc0⟩)).1.symm).trans
        (mma_cells hp hX hf base (.inl ⟨_, _, _, _, rowr, colr, ⟨_, hr0⟩, hcr⟩)).1
    have hthr : src.1 = r.1 := mma_thread hp hX hf h0 hr0 cta
    have hg : src.1 < L.threads := Frame.lt_of_get hX h0
    obtain ⟨hsd, hsm, hsn, hslo, hshi⟩ : SameAccumulator d0 s0 dr sr := same
    have hdd : s0.descriptor = sr.descriptor := by
      rcases c1 with ⟨h1', e1'⟩ | ⟨h1', e1'⟩ <;> rcases c2 with ⟨h2', e2'⟩ | ⟨h2', e2'⟩
      · rw [e1', e2']
      · omega
      · omega
      · rw [e1', e2']
    have hlo : s0.lowCta = sr.lowCta := by rw [lo1, lo2, hthr]
    have hhi : s0.highCta = sr.highCta := by rw [hi1, hi2, hthr]
    have hlt : src.2 < r.2 := by
      rcases Nat.lt_trichotomy src.2 r.2 with h | h | h
      · exact h
      · exact absurd (Prod.ext hthr h) hs.1
      · exact (writeBefore_asymm hX hG hs.2.2.1 (.inl (Before.of_mma_po ⟨_, hr0⟩ ⟨_, h0⟩
          (hthr ▸ hg) hthr.symm h ⟨hsd.symm, hsm.symm, hsn.symm, hslo.symm,
            hshi.symm⟩))).elim
    exact hX.mmaCompletion src r ⟨hthr, hlt, hpl, d0, s0, a0, m0, dr, sr, ar, mr, ⟨_, h0⟩,
      ⟨_, hr0⟩, fun row' col' => by
        rw [hmk1, hmk2, ← hsd]
        exact writeCell_congr hdd hlo hhi _ _ _ _,
      row, col, cell, hc0⟩ hdr
  · obtain ⟨pc, hst⟩ := hst
    obtain ⟨d0, s0, a0, m0, row, col, ⟨pc0, h0⟩, -⟩ := hm
    cases get_tc_inj h0 hst
  · obtain ⟨d0, s0, a0, m0, row, col, ⟨pc0, h0⟩, -⟩ := hm
    obtain ⟨pcc, hcc'⟩ := hcc
    cases get_tc_inj h0 hcc'

end PTX.Kernels.InklingRelDecode.Proof.Tmem
