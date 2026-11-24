-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderBase

@[expose] public section

/-! # The loader's second query half of an item (`q1`)

The poll of the stage-1 Q slot's empty barrier, the leader CTA's arrival on its full barrier
and the two copies of the query half; before them the half's row (`+256`), after them the Q
parity's flip and the next KV slot's addresses. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work
open Prologue (sb)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- From the instruction after the arrival to the first copy election: the half's row. -/
theorem toElC_q1 (hpre : Pre P L mem0) (d : D) :
    SegTo L g 330 (factsAt L g 330 d) { d with site := .elC .q1 0 } :=
  ⟨1, fun t h => by loader_seg h hpre⟩

/-- After the second copy: the Q parity's flip, then the poll of the item's last V tile. -/
theorem afterQ1 (hpre : Pre P L mem0) (d : D) (hs : d.s < 6) (hqp : d.qp < 2) :
    SegTo L g 347 (factsAt L g 347 d) { d with site := .wait .v0, qp := 1 - d.qp } := by
  have h6 := snext_lt hs
  exact ⟨4, fun t h => by loader_seg h hpre [xor_one hqp]⟩

variable {d : D} {t u : TState} {e : Event} {ins : Instr}

theorem step_wait_q1 (hpre : Pre P L mem0) (hs : d.site = .wait .q1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_2)
  refine step_wait_of (dok := if rank L g = 0 then ⟨.elA .q1, i, tt, s, ph, qp⟩
      else ⟨.elC .q1 0, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ => by simp [next]) (fun _ _ _ _ => by simp [next])
    ⟨2, fun t h => by loader_seg h hpre⟩
    (seg_wait_ok (w := 321) rfl Flow.code_322 Flow.code_324 rfl (by live_dec) (by live_dec)
      (toElC_q1 hpre ⟨.wait .q1, i, tt, s, ph, qp⟩) (by live_dec)) hi ?_ h hf
  split_ifs with hr
  · inv_site hi hr
  · inv_site hi hr

theorem step_elA_q1 (hpre : Pre P L mem0) (hs : d.site = .elA .q1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_21)
  have hr : rank L g = 0 := hi.lead rfl
  refine step_elect_of (dl := ⟨.arrive .q1, i, tt, s, ph, qp⟩)
    (ds := ⟨.elC .q1 0, i, tt, s, ph, qp⟩) rfl (by live_dec) (by live_dec) (by decide)
    (fun _ _ _ => by simp only [next]; split_ifs <;> rfl)
    (fun ld => ⟨3, fun t h => by loader_seg h hpre⟩) (fun ld => ?_)
    (by inv_site hi hr) (by inv_site hi hr) h hf
  obtain ⟨k, hT⟩ := (toElC_q1 (g := g) hpre ⟨.elA .q1, i, tt, s, ph, qp⟩)
  exact ⟨2 + k, Seg.comp (show Seg kernel asms L g 2 _ _ 330
      (factsAt L g 330 ⟨.elA .q1, i, tt, s, ph, qp⟩) from fun t h => by loader_seg h hpre) hT⟩

theorem step_arrive_q1 (hpre : Pre P L mem0) (hs : d.site = .arrive .q1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_2)
  have hr : rank L g = 0 := hi.lead rfl
  exact step_arrive_of (d' := ⟨.elC .q1 0, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ _ _ => by simp only [next])
    (segTo_of (toElC_q1 hpre ⟨.arrive .q1, i, tt, s, ph, qp⟩) rfl (by live_dec)) (by inv_site hi
        hr) h hf

theorem step_elC_q1_0 (hpre : Pre P L mem0) (hs : d.site = .elC .q1 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_22)
  refine step_elect_of (dl := ⟨.copy .q1 0, i, tt, s, ph, qp⟩)
    (ds := ⟨.elC .q1 1, i, tt, s, ph, qp⟩) rfl (by live_dec) (by live_dec) (by decide)
    (fun _ _ _ => by simp only [next, afterCopy, UseK.copies]; split_ifs <;> rfl)
    (fun ld => ⟨6, fun t h => by loader_seg h hpre⟩)
    (fun ld => ⟨2, fun t h => by loader_seg h hpre⟩)
    (by inv_site hi hi.lead) (by inv_site hi hi.lead) h hf

theorem step_copy_q1_0 (hs : d.site = .copy .q1 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_4)
  exact step_copy_of (d' := ⟨.elC .q1 1, i, tt, s, ph, qp⟩) rfl
    (fun _ _ => by simp [next, afterCopy, UseK.copies])
    (segTo_here rfl rfl (by live_dec)) (by inv_site hi hi.lead) h hf

theorem step_elC_q1_1 (hpre : Pre P L mem0) (hs : d.site = .elC .q1 1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_23)
  obtain ⟨k, hT⟩ := afterQ1 (g := g) hpre ⟨.elC .q1 1, i, tt, s, ph, qp⟩ hi.s hi.qp
  refine step_elect_of (dl := ⟨.copy .q1 1, i, tt, s, ph, qp⟩)
    (ds := ⟨.wait .v0, i, tt, s, ph, 1 - qp⟩) rfl (by live_dec) (by live_dec) (by decide)
    (fun _ _ _ => by simp only [next, afterCopy, afterUse, UseK.copies]; split_ifs <;> rfl)
    (fun ld => ⟨6, fun t h => by loader_seg h hpre⟩)
    (fun ld => ⟨2 + k, Seg.comp (show Seg kernel asms L g 2 _ _ 347
      (factsAt L g 347 ⟨.elC .q1 1, i, tt, s, ph, qp⟩) from
      fun t h => by loader_seg h hpre) hT⟩)
    (by inv_site hi hi.lead) ?_ h hf
  exact ⟨hi.s, hi.ph, by dsimp only; omega, fun _ => hi.item rfl, fun h => by simp [Site.inTrip]
      at h,
    fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩

theorem step_copy_q1_1 (hpre : Pre P L mem0) (hs : d.site = .copy .q1 1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_5)
  refine step_copy_of (d' := ⟨.wait .v0, i, tt, s, ph, 1 - qp⟩) rfl
    (fun _ _ => by simp [next, afterCopy, afterUse, UseK.copies])
    (segTo_of (afterQ1 hpre ⟨.copy .q1 1, i, tt, s, ph, qp⟩ hi.s hi.qp) rfl (by live_dec)) ?_ h hf
  exact ⟨hi.s, hi.ph, by dsimp only; omega, fun _ => hi.item rfl, fun h => by simp [Site.inTrip]
      at h,
    fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
