-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Tmem.AccessCp
public import Lemmas.Tcgen05.TcMmaSource

@[expose] public section

/-! # The source of a Tensor Memory read is live

`TcMma.SourceLive` of a read by an MMA or a load: the reader is completed before every release of
an allocation covering the cell. A release is a deallocation of the cell's CTA (`release_info`);
every MMA is done before every deallocation of its CTA, and every load is waited for. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX Tmem.Pair TcMma Tmem.One Tmem.Access

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

/-- **The source of a load register is live**, given that every load is waited for before every
deallocation of its CTA and the cell is of the load's CTA. -/
theorem source_live_ld (hX : Consistent L kernel Assumptions.all m X) (ht : Tmem1Facts L X 0)
    (hwd : ∀ {e d : EvId} {a : Nat} {vals : List Value} {sh : TcShape} {pc : Nat}
      {grp : CtaGroup} {dst : Option Loc} {da n : Nat},
      X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc da n))⟩ →
      d.1 / L.block = e.1 / L.block → X.TLd e a vals sh → WaitBefore L X .waitLd e d)
    {source e : EvId} {cell : Cell} {a : Nat} {vals : List Value} {sh : TcShape}
    (hld : X.TLd e a vals sh) (hc : cell.cta = e.1 / L.block) :
    SourceLive L X source e cell := by
  intro cta r hr hcov rel hrel
  refine .inl ?_
  obtain ⟨⟨pc, grp, a', n, hd⟩, hdc⟩ := release_info hX ht.toTmem1Ops hr hrel
  have hown := covers_owner hcov
  obtain ⟨hlc, -⟩ := record_info hX ht.toTmem1Ops hr
  have hcell : rel.1 / L.block = e.1 / L.block := by rw [hdc, ← hlc, ← hown, hc]
  obtain ⟨pce, hge⟩ := hld
  refine ⟨fun _ => hwd hd hcell ⟨pce, hge⟩, fun ⟨a', vals, sh, pc', h⟩ => ?_, fun h => ?_⟩
  · rw [hge] at h
    cases h
  · rcases h with ⟨d, s, acc, mask, pc', h⟩ | ⟨c, pc', h⟩ | ⟨s, pc', h⟩ <;> rw [hge] at h <;>
      cases h

end PTX.Kernels.InklingRelDecode.Proof.Tmem
