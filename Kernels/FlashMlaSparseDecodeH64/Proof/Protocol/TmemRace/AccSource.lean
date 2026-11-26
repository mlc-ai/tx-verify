-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Live
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Order
public import Lemmas.Tcgen05.TmemLatestSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Prev

@[expose] public section

/-! # The accumulator reads of the MMAs have a source

An accumulating MMA of the MMA lane (QK MMA `k ≥ 1`, PV MMA `k ≥ 2` or in a block past the
first) has an earlier MMA of the lane with its D column (`mma_prev`): a write of the cell it
reads, ordered before it by the accumulator pipeline of the lane (`Before.of_mma_po`). Every
write of the cell is ordered with the read (`reads_safe`), the read is live (`source_live_mma`),
so the latest write ordered before the read is its source (`readSourceOfCandidate`): the
previous MMA, or warpgroup 0's rescale store of the PV accumulator. The words the source
leaves are `Result` and `StoreValue`, not stated here. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An MMA of the rows**: at an MMA pc of the lane, zero output masks, and the operands of one
of the two instruction words, by its D column. -/
private theorem mma_row (hR : TmemRows P L X) (hX : Consistent L kernel Assumptions.all m X)
    {x : EvId} {pc d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get x = some ⟨pc, .tc (.mma d s acc mask)⟩) :
    MmaOn L x.1 pc ∧ mask = [0, 0, 0, 0] ∧
      ((d = 400 ∧ ∃ aT, TmemRow.MmaOps L x.1 s aT TmemRow.qkIdesc) ∨
        (d < 256 ∧ ∃ aT, TmemRow.MmaOps L x.1 s aT TmemRow.pvIdesc)) := by
  rcases tc_role hR (Frame.lt_of_get hX he) he rfl with ⟨-, hW⟩ | ⟨hat, hM⟩ | ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · rcases hM with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨_, k, hk, hpc, h, hops⟩ |
      ⟨_, _, k, hk, hpc, h, -, hops⟩ <;> cases h
    · refine ⟨⟨hat, ?_⟩, rfl, .inl ⟨rfl, _, hops⟩⟩
      simp only [TmemRow.qkPc] at hpc
      split at hpc <;> omega
    · refine ⟨⟨hat, ?_⟩, rfl, .inr ⟨by omega, _, hops⟩⟩
      simp only [TmemRow.pvPc] at hpc
      split at hpc <;> omega
  · cases hc'

/-- The cell of an MMA's result depends on its descriptor and CTAs only. -/
private theorem resultCell_congr {s s' : TcMma.OperandSpec} {b r c : Nat}
    (hd : s.descriptor = s'.descriptor) (hl : s.lowCta = s'.lowCta) (hh : s.highCta = s'.highCta) :
    TcMma.resultCell s b r c = TcMma.resultCell s' b r c := by
  unfold TcMma.resultCell
  rw [hd, hl, hh]

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hT : TmemRows P L X) (hO : MmaOne L X) (hPS : PvStoreOrder L X)
  (hG : SyncGuarded L kernel X) (ht : Tmem.One.Tmem1Facts L X 0)
  (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
include hp hX hFw hT hO hPS hG ht hmd

/-- **Every accumulator read of an MMA has a source**: the latest write of the cell ordered before
the read. -/
theorem acc_source {i : EvId} {cell : TcMma.Cell} (hr : X.MmaReadCell i cell) :
    ∃ source, TcMma.ReadSource L X .acc source i cell := by
  have hwr := acc_write hX hT hr
  obtain ⟨g, j⟩ := i
  obtain ⟨d, s, mask, row, col, ⟨pc, he⟩, hc⟩ := hr
  obtain ⟨hon, rfl, hcls⟩ := mma_row hT hX he
  have hg := Frame.lt_of_get hX he
  obtain ⟨j', hj, pc', s', acc', mask', he', hr'⟩ := mma_prev hp hX hFw he ⟨hon.1.2.1, hon.1.2.2⟩
  obtain ⟨hon', rfl, hcls'⟩ := mma_row hT hX he'
  obtain ⟨i, hi, ⟨aT, hs⟩, ⟨aT', hs'⟩⟩ : ∃ i, (i = TmemRow.qkIdesc ∨ i = TmemRow.pvIdesc) ∧
      (∃ aT, TmemRow.MmaOps L g s aT i) ∧ ∃ aT', TmemRow.MmaOps L g s' aT' i := by
    rcases hcls with ⟨h1, aT, h2⟩ | ⟨h1, aT, h2⟩ <;>
      rcases hcls' with ⟨h3, aT', h4⟩ | ⟨h3, aT', h4⟩
    · exact ⟨_, .inl rfl, ⟨_, h2⟩, _, h4⟩
    · omega
    · omega
    · exact ⟨_, .inr rfl, ⟨_, h2⟩, _, h4⟩
  obtain ⟨hl, hh⟩ := ops_cta hp hg hi hs
  obtain ⟨hl', hh'⟩ := ops_cta hp hg hi hs'
  have hdd : s.descriptor = s'.descriptor := by
    obtain ⟨-, hd1, -⟩ := hs
    obtain ⟨-, hd2, -⟩ := hs'
    exact Option.some.inj (hd1.symm.trans hd2)
  have hcell : TcMma.resultCell s' d row col = some cell := by
    rw [← resultCell_congr hdd (hl.trans hl'.symm) (hh.trans hh'.symm)]
    exact hc
  have hW : TcMma.TmemWrite L X (g, j') cell :=
    .inl ⟨d, s', acc', [0, 0, 0, 0], row, col, ⟨pc', he'⟩,
      writeCell_zeroMask (ops_group hi hs') (ops_m64 hi hs') hcell⟩
  have hB : TcMma.WriteBefore L X (g, j') (g, j) :=
    .inl (TcMma.Before.of_mma_po ⟨_, he'⟩ ⟨_, he⟩ hg rfl hj
      ⟨rfl, by rw [hdd], by rw [hdd], by rw [hl, hl'], by rw [hh, hh']⟩)
  have hcta : cell.cta = g / L.block := (writer_cases hp hX hT hwr).1
  refine TcMma.readSourceOfCandidate hX hG (writes_safe hp hX hFw hT hO hPS) ?_
    (fun _ _ _ => source_live_mma hX ht hmd ⟨pc, he⟩ hcta) hW hB
  intro w hw
  rcases (TcMma.readsSafe_iff.mp (reads_safe hp hX hFw hT hO hPS)).1 (g, j) w cell
      ⟨d, s, [0, 0, 0, 0], row, col, ⟨pc, he⟩, hc⟩ hw with h | h | h
  · exact .inr (.inl h.symm)
  · exact .inl h
  · exact .inr h

end

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
