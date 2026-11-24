-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderBase

@[expose] public section

/-! # The loader's last K tile of an item (`k0`)

The poll of the slot's empty barrier, the leader CTA's arrival on its full barrier, and the
two copies of the K tile into the slot (one per 64-column half). Before the first copy
election the code computes the K row and the full barrier's address with the peer-bit mask
(`seg_peer`); after it, the copy destination as the CTA's window pointer plus the slot's
offset (`seg_ptr`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work
open Prologue (sb)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- From the instruction after the arrival to the first copy election. -/
theorem toElC_k0 (hpre : Pre P L mem0) (hg : g < L.threads) (d : D) (hs : d.s < 6) :
    SegTo L g 270 (factsAt L g 270 d) { d with site := .elC .k0 0 } := by
  have hb := (shape hpre).1
  have h1 : Seg kernel asms L g 3 270 (factsAt L g 270 d) 273 (factsAt L g 273 d) :=
    fun t h => by loader_seg h hpre
  have h2 := seg_peer (L := L) (g := g) (F := factsAt L g 273 d) hpre hg Flow.code_273 (by decide)
    (tbl_mem (r := 751) (by live_dec)
      (by simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]))
    (k := 32 + 8 * d.s) (by omega) (facts_ne (by live_dec))
  exact ⟨3 + 1, Seg.weaken_end (Seg.comp h1 h2) fun _ hR => holds_cons_relive hR
    (by simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]) rfl
    (by live_dec)⟩

variable {d : D} {t u : TState} {e : Event} {ins : Instr}

theorem step_wait_k0 (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .wait .k0) (hi :
    Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_0)
  refine step_wait_of (dok := if rank L g = 0 then ⟨.elA .k0, i, tt, s, ph, qp⟩
      else ⟨.elC .k0 0, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ => by simp [next]) (fun _ _ _ _ => by simp [next])
    ⟨2, fun t h => by loader_seg h hpre⟩
    (seg_wait_ok (w := 261) rfl Flow.code_262 Flow.code_264 rfl (by live_dec) (by live_dec)
      (toElC_k0 hpre hg _ hi.s) (by live_dec)) hi ?_ h hf
  split_ifs with hr
  · inv_site hi hr
  · inv_site hi hr

theorem step_elA_k0 (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .elA .k0) (hi : Inv
    L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_15)
  have hr : rank L g = 0 := hi.lead rfl
  refine step_elect_of (dl := ⟨.arrive .k0, i, tt, s, ph, qp⟩)
    (ds := ⟨.elC .k0 0, i, tt, s, ph, qp⟩) rfl (by live_dec) (by live_dec) (by decide)
    (fun _ _ _ => by simp only [next]; split_ifs <;> rfl)
    (fun ld => ⟨3, fun t h => by loader_seg h hpre⟩) (fun ld => ?_)
    (by inv_site hi hr) (by inv_site hi hr) h hf
  obtain ⟨k, hT⟩ := toElC_k0 (g := g) hpre hg ⟨.elA .k0, i, tt, s, ph, qp⟩ hi.s
  have h1 : Seg kernel asms L g 2 266
      ((53, .pred false) :: (748, .bits 32 (BitVec.ofNat 64 ld)) ::
        facts L g ⟨.elA .k0, i, tt, s, ph, qp⟩) 270
      (factsAt L g 270 ⟨.elA .k0, i, tt, s, ph, qp⟩) :=
    fun t h => by loader_seg h hpre
  exact ⟨2 + k, Seg.comp h1 hT⟩

theorem step_arrive_k0 (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .arrive .k0) (hi
    : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_0)
  have hr : rank L g = 0 := hi.lead rfl
  exact step_arrive_of rfl (by live_dec) (fun _ _ _ _ _ _ => by simp only [next])
    (segTo_of (toElC_k0 hpre hg _ hi.s) rfl (by live_dec)) (by inv_site hi hr) h hf

theorem step_elC_k0_0 (hpre : Pre P L mem0) (hs : d.site = .elC .k0 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_16)
  have hb := (shape hpre).1
  have hs6 : s < 6 := hi.s
  have hptr : ∀ (b : Bool) ld, Seg kernel asms L g 1 275
      ((55, .pred b) :: (752, .bits 32 (BitVec.ofNat 64 ld)) ::
        facts L g ⟨.elC .k0 0, i, tt, s, ph, qp⟩) 276
      ((368, .ptr 32 false (.shared (ctaOf L g) (ctaOf L g))
            (BitVec.ofNat 64 (L.sharedBase + 16384 * s))) ::
        (55, .pred b) :: (752, .bits 32 (BitVec.ofNat 64 ld)) ::
        facts L g ⟨.elC .k0 0, i, tt, s, ph, qp⟩) := fun b ld =>
    seg_ptr (L := L) (g := g) (a := L.sharedBase + 0) (k := 16384 * s) Flow.code_275
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (tbl_mem (r := 356) (by live_dec)
        (by simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, win]))))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (tbl_mem (r := 750) (by live_dec)
        (by simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]))))
      (by omega) (by omega) (by omega)
      (cons_ne (ex := [(55, _), (752, _)]) (by simp) (by live_dec))
  refine step_elect_of (dl := ⟨.copy .k0 0, i, tt, s, ph, qp⟩)
    (ds := ⟨.elC .k0 1, i, tt, s, ph, qp⟩) rfl (by live_dec) (by live_dec) (by decide)
    (fun _ _ _ => by simp only [next, afterCopy, UseK.copies]; split_ifs <;> rfl)
    (fun ld => ⟨1 + 6, Seg.comp (hptr true ld) fun t h => by loader_seg h hpre⟩)
    (fun ld => ⟨1 + 2, Seg.comp (hptr false ld) fun t h => by loader_seg h hpre⟩)
    (by inv_site hi hi.lead) (by inv_site hi hi.lead) h hf

theorem step_copy_k0_0 (hs : d.site = .copy .k0 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_0)
  exact step_copy_of (d' := ⟨.elC .k0 1, i, tt, s, ph, qp⟩) rfl
    (fun _ _ => by simp [next, afterCopy, UseK.copies]) (segTo_here rfl rfl (by live_dec))
    (by inv_site hi hi.lead) h hf

theorem step_elC_k0_1 (hpre : Pre P L mem0) (hs : d.site = .elC .k0 1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_17)
  refine step_elect_of (dl := ⟨.copy .k0 1, i, tt, s, ph, qp⟩)
    (ds := ⟨.wait .q0, i, tt, s, ph, qp⟩) rfl (by live_dec) (by live_dec) (by decide)
    (fun _ _ _ => by simp only [next, afterCopy, afterUse, UseK.copies]; split_ifs <;> rfl)
    (fun ld => ⟨6, fun t h => by loader_seg h hpre⟩)
    (fun ld => ⟨2, fun t h => by loader_seg h hpre⟩)
    (by inv_site hi hi.lead) (by inv_site hi hi.lead) h hf

theorem step_copy_k0_1 (hs : d.site = .copy .k0 1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_1)
  exact step_copy_of (d' := ⟨.wait .q0, i, tt, s, ph, qp⟩) rfl
    (fun _ _ => by simp [next, afterCopy, afterUse, UseK.copies])
    (segTo_here rfl rfl (by live_dec)) (by inv_site hi hi.lead) h hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
