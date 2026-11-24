-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderBase

@[expose] public section

/-! # The loader's first query half of an item (`q0`)

The poll of the stage-0 Q slot's empty barrier, the leader CTA's arrival on its full barrier,
the two copies of the query half (one per 64-column half), and after them the KV ring's next
slot and parity (`add`, `setp.eq 6`, `selp`, `xor`): the segment is cut at the `selp`, whose
predicate (the slot wraps) is a case. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work
open Prologue (sb)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- After the second copy: the next KV slot and parity, then the poll of the stage-1 Q slot. -/
theorem afterQ0 (hpre : Pre P L mem0) (d : D) (hs : d.s < 6) (hph : d.ph < 2) :
    SegTo L g 316 (factsAt L g 316 d) { d with site := .wait .q1 } := by
  refine ⟨2 + 3, seg_wrap (p := 65) (pcS := 318) (d := d) (c := d.s + 1 = 6)
    (fun t h => by loader_seg h hpre) (tbl_mem (by live_dec) (by
      simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some])) fun b hb t h => ?_⟩
  cases b
  · have hw : ¬ d.s + 1 = 6 := by simpa using hb
    loader_seg h hpre [snext, pnext, hw, xor_bit_zero hph]
  · have hw : d.s + 1 = 6 := by simpa using hb
    loader_seg h hpre [snext, pnext, hw, xor_bit_one hph]

variable {d : D} {t u : TState} {e : Event} {ins : Instr}

theorem step_wait_q0 (hpre : Pre P L mem0) (hs : d.site = .wait .q0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_1)
  refine step_wait_of (dok := if rank L g = 0 then ⟨.elA .q0, i, tt, s, ph, qp⟩
      else ⟨.elC .q0 0, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ => by simp [next]) (fun _ _ _ _ => by simp [next])
    ⟨2, fun t h => by loader_seg h hpre⟩
    (seg_wait_ok (w := 291) rfl Flow.code_292 Flow.code_294 rfl (by live_dec) (by live_dec)
      (segTo_here rfl rfl (by live_dec)) (by live_dec)) hi ?_ h hf
  split_ifs with hr
  · inv_site hi hr
  · inv_site hi hr

theorem step_elA_q0 (hpre : Pre P L mem0) (hs : d.site = .elA .q0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_18)
  have hr : rank L g = 0 := hi.lead rfl
  refine step_elect_of (dl := ⟨.arrive .q0, i, tt, s, ph, qp⟩)
    (ds := ⟨.elC .q0 0, i, tt, s, ph, qp⟩) rfl (by live_dec) (by live_dec) (by decide)
    (fun _ _ _ => by simp only [next]; split_ifs <;> rfl)
    (fun ld => ⟨3, fun t h => by loader_seg h hpre⟩) (fun ld => ?_)
    (by inv_site hi hr) (by inv_site hi hr) h hf
  exact ⟨2, fun t h => by loader_seg h hpre⟩

theorem step_arrive_q0 (hs : d.site = .arrive .q0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_1)
  have hr : rank L g = 0 := hi.lead rfl
  exact step_arrive_of (d' := ⟨.elC .q0 0, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ _ _ => by simp only [next])
    (segTo_here rfl rfl (by live_dec)) (by inv_site hi hr) h hf

theorem step_elC_q0_0 (hpre : Pre P L mem0) (hs : d.site = .elC .q0 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_19)
  refine step_elect_of (dl := ⟨.copy .q0 0, i, tt, s, ph, qp⟩)
    (ds := ⟨.elC .q0 1, i, tt, s, ph, qp⟩) rfl (by live_dec) (by live_dec) (by decide)
    (fun _ _ _ => by simp only [next, afterCopy, UseK.copies]; split_ifs <;> rfl)
    (fun ld => ⟨6, fun t h => by loader_seg h hpre⟩)
    (fun ld => ⟨2, fun t h => by loader_seg h hpre⟩)
    (by inv_site hi hi.lead) (by inv_site hi hi.lead) h hf

theorem step_copy_q0_0 (hs : d.site = .copy .q0 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_2)
  exact step_copy_of (d' := ⟨.elC .q0 1, i, tt, s, ph, qp⟩) rfl
    (fun _ _ => by simp [next, afterCopy, UseK.copies])
    (segTo_here rfl rfl (by live_dec)) (by inv_site hi hi.lead) h hf

theorem step_elC_q0_1 (hpre : Pre P L mem0) (hs : d.site = .elC .q0 1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_20)
  obtain ⟨k, hT⟩ := afterQ0 (g := g) hpre ⟨.elC .q0 1, i, tt, s, ph, qp⟩ hi.s hi.ph
  refine step_elect_of (dl := ⟨.copy .q0 1, i, tt, s, ph, qp⟩)
    (ds := ⟨.wait .q1, i, tt, s, ph, qp⟩) rfl (by live_dec) (by live_dec) (by decide)
    (fun _ _ _ => by simp only [next, afterCopy, afterUse, UseK.copies]; split_ifs <;> rfl)
    (fun ld => ⟨6, fun t h => by loader_seg h hpre⟩)
    (fun ld => ⟨2 + k, Seg.comp (show Seg kernel asms L g 2 _ _ 316
      (factsAt L g 316 ⟨.elC .q0 1, i, tt, s, ph, qp⟩) from
      fun t h => by loader_seg h hpre) hT⟩)
    (by inv_site hi hi.lead) (by inv_site hi hi.lead) h hf

theorem step_copy_q0_1 (hpre : Pre P L mem0) (hs : d.site = .copy .q0 1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_3)
  exact step_copy_of (d' := ⟨.wait .q1, i, tt, s, ph, qp⟩) rfl
    (fun _ _ => by simp [next, afterCopy, afterUse, UseK.copies])
    (segTo_of (afterQ0 hpre ⟨.copy .q0 1, i, tt, s, ph, qp⟩ hi.s hi.ph) rfl
      (by live_dec)) (by inv_site hi hi.lead) h hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
