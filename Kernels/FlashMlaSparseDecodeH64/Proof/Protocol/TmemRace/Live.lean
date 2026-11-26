-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Dealloc

@[expose] public section

/-! # An MMA's source is live

`TcMma.SourceLive` of a read by an MMA: the MMA is completed before every release of an
allocation covering the cell. Re-derived as `Tmem.AccessCp.no_access_unsafe_cp` does: a release is
a deallocation of the cell's CTA (`release_info`), and every MMA is done before every deallocation
of its CTA (`dealloc_async`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX Tmem.Pair TcMma Tmem.One Tmem.Access

noncomputable section

variable {L : Launch} {m : Mem0} {X : Execution}

/-- **The source of a read by an MMA is live**, given that every MMA is done before every
deallocation of its CTA and the cell is of the MMA's CTA. -/
theorem source_live_mma (hX : Consistent L kernel Assumptions.all m X) (ht : Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) {source e : EvId} {cell : Cell} {d : Nat}
    {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.MmaIssue e d s acc mask) (hc : cell.cta = e.1 / L.block) :
    SourceLive L X source e cell := by
  intro cta r hr hcov rel hrel
  refine .inl ?_
  obtain ⟨⟨pc, grp, a, n, hd⟩, hdc⟩ := release_info hX ht.toTmem1Ops hr hrel
  have hown := covers_owner hcov
  obtain ⟨hlc, -⟩ := record_info hX ht.toTmem1Ops hr
  have hcell : rel.1 / L.block = e.1 / L.block := by rw [hdc, ← hlc, ← hown, hc]
  obtain ⟨pce, hge⟩ := he
  refine ⟨fun ⟨a', vals, sh, pc', h⟩ => ?_, fun ⟨a', vals, sh, pc', h⟩ => ?_, fun _ => ?_⟩
  · rw [hge] at h
    cases h
  · rw [hge] at h
    cases h
  · exact hmd (.inl ⟨d, s, acc, mask, pce, hge⟩) hd hcell

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
