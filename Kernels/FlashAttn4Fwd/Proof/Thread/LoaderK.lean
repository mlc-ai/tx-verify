-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderBase

@[expose] public section

/-! # The loader's K tile of a trip (`k`)

Trip `t` of an item's KV loop loads K tile `n - 2 - t`: the poll of the slot's empty barrier,
the leader CTA's arrival on its full barrier and the two copies; before the first copy
election the tile's row and the full barrier's address with the peer-bit mask, after it the
destination pointer. After the copies the KV ring's next slot (cut at the wrap `selp`) and the
poll of the trip's V tile. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work
open Prologue (sb)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- From the instruction after the arrival to the first copy election. -/
theorem toElC_k (hpre : Pre P L mem0) (hg : g < L.threads) (d : D) (hs : d.s < 6)
    (htr : d.t + 2 ≤ n L) : SegTo L g 391 (factsAt L g 391 d) { d with site := .elC .k 0 } := by
  have hb := (shape hpre).1
  have h1 : Seg kernel asms L g 5 391 (factsAt L g 391 d) 396 (factsAt L g 396 d) :=
    fun t h => by loader_seg h hpre [kRow]
  have h2 := seg_peer (L := L) (g := g) (F := factsAt L g 396 d) hpre hg Flow.code_396
    (by decide) (tbl_mem (r := 789) (by live_dec)
      (by simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]))
    (k := 32 + 8 * d.s) (by omega) (facts_ne (by live_dec))
  exact ⟨5 + 1, Seg.weaken_end (Seg.comp h1 h2) fun _ hR => holds_cons_relive hR
    (by simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]) rfl
    (by live_dec)⟩

/-- After the second copy: the next KV slot and parity, then the poll of the trip's V tile. -/
theorem afterK (hpre : Pre P L mem0) (d : D) (hs : d.s < 6) (hph : d.ph < 2) :
    SegTo L g 414 (factsAt L g 414 d) { d with site := .wait .v } := by
  refine ⟨2 + 6, seg_wrap (p := 84) (pcS := 416) (d := d) (c := d.s + 1 = 6)
    (fun t h => by loader_seg h hpre) (tbl_mem (by live_dec) (by
      simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some])) fun b hb t h => ?_⟩
  cases b
  · have hw : ¬ d.s + 1 = 6 := by simpa using hb
    loader_seg h hpre [snext, pnext, hw, xor_bit_zero hph]
  · have hw : d.s + 1 = 6 := by simpa using hb
    loader_seg h hpre [snext, pnext, hw, xor_bit_one hph]

variable {d : D} {t u : TState} {e : Event} {ins : Instr}

theorem step_wait_k (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .wait .k)
    (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_4)
  refine step_wait_of (dok := if rank L g = 0 then ⟨.elA .k, i, tt, s, ph, qp⟩
      else ⟨.elC .k 0, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ => by simp [next]) (fun _ _ _ _ => by simp [next])
    ⟨2, fun t h => by loader_seg h hpre⟩
    (seg_wait_ok (w := 382) rfl Flow.code_383 Flow.code_385 rfl (by live_dec) (by live_dec)
      (toElC_k hpre hg ⟨.wait .k, i, tt, s, ph, qp⟩ hi.s (hi.trip rfl)) (by live_dec)) hi ?_ h hf
  split_ifs with hr
  · inv_site hi hr
  · inv_site hi hr

theorem step_elA_k (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .elA .k)
    (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_26)
  have hr : rank L g = 0 := hi.lead rfl
  refine step_elect_of (dl := ⟨.arrive .k, i, tt, s, ph, qp⟩)
    (ds := ⟨.elC .k 0, i, tt, s, ph, qp⟩) rfl (by live_dec) (by live_dec) (by decide)
    (fun _ _ _ => by simp only [next]; split_ifs <;> rfl)
    (fun ld => ⟨3, fun t h => by loader_seg h hpre⟩) (fun ld => ?_)
    (by inv_site hi hr) (by inv_site hi hr) h hf
  obtain ⟨k, hT⟩ := (toElC_k (g := g) hpre hg ⟨.elA .k, i, tt, s, ph, qp⟩ hi.s (hi.trip rfl))
  exact ⟨2 + k, Seg.comp (show Seg kernel asms L g 2 _ _ 391
      (factsAt L g 391 ⟨.elA .k, i, tt, s, ph, qp⟩) from fun t h => by loader_seg h hpre) hT⟩

theorem step_arrive_k (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .arrive .k)
    (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_4)
  have hr : rank L g = 0 := hi.lead rfl
  exact step_arrive_of (d' := ⟨.elC .k 0, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ _ _ => by simp only [next])
    (segTo_of (toElC_k hpre hg ⟨.arrive .k, i, tt, s, ph, qp⟩ hi.s (hi.trip rfl)) rfl (by
        live_dec)) (by inv_site hi hr) h hf

theorem step_elC_k_0 (hpre : Pre P L mem0) (hs : d.site = .elC .k 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_27)
  have hb := (shape hpre).1
  have hs6 : s < 6 := hi.s
  have hptr : ∀ (b : Bool) ld, Seg kernel asms L g 1 398
      ((80, .pred b) :: (790, .bits 32 (BitVec.ofNat 64 ld)) :: facts L g ⟨.elC .k 0, i, tt, s,
          ph, qp⟩) 399
      ((376, .ptr 32 false (.shared (ctaOf L g) (ctaOf L g))
            (BitVec.ofNat 64 (L.sharedBase + 16384 * s))) ::
        (80, .pred b) :: (790, .bits 32 (BitVec.ofNat 64 ld)) :: facts L g ⟨.elC .k 0, i, tt, s,
            ph, qp⟩) := fun b ld =>
    seg_ptr (L := L) (g := g) (a := L.sharedBase + 0) (k := 16384 * s) Flow.code_398
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (tbl_mem (r := 356) (by live_dec)
        (by simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, win]))))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (tbl_mem (r := 787) (by live_dec)
        (by simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]))))
      (by omega) (by omega) (by omega)
      (cons_ne (ex := [(80, _), (790, _)]) (by simp) (by live_dec))
  refine step_elect_of (dl := ⟨.copy .k 0, i, tt, s, ph, qp⟩)
    (ds := ⟨.elC .k 1, i, tt, s, ph, qp⟩) rfl (by live_dec) (by live_dec) (by decide)
    (fun _ _ _ => by simp only [next, afterCopy, UseK.copies]; split_ifs <;> rfl)
    (fun ld => ⟨1 + 6, Seg.comp (hptr true ld) fun t h => by loader_seg h hpre⟩)
    (fun ld => ⟨1 + 2, Seg.comp (hptr false ld) fun t h => by loader_seg h hpre⟩)
    (by inv_site hi hi.lead) (by inv_site hi hi.lead) h hf

theorem step_copy_k_0 (hs : d.site = .copy .k 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_7)
  exact step_copy_of (d' := ⟨.elC .k 1, i, tt, s, ph, qp⟩) rfl
    (fun _ _ => by simp [next, afterCopy, UseK.copies])
    (segTo_here rfl rfl (by live_dec)) (by inv_site hi hi.lead) h hf

theorem step_elC_k_1 (hpre : Pre P L mem0) (hs : d.site = .elC .k 1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_28)
  obtain ⟨k, hT⟩ := afterK (g := g) hpre ⟨.elC .k 1, i, tt, s, ph, qp⟩ hi.s hi.ph
  refine step_elect_of (dl := ⟨.copy .k 1, i, tt, s, ph, qp⟩)
    (ds := ⟨.wait .v, i, tt, s, ph, qp⟩) rfl (by live_dec) (by live_dec) (by decide)
    (fun _ _ _ => by simp only [next, afterCopy, afterUse, UseK.copies]; split_ifs <;> rfl)
    (fun ld => ⟨6, fun t h => by loader_seg h hpre⟩)
    (fun ld => ⟨2 + k, Seg.comp (show Seg kernel asms L g 2 _ _ 414
      (factsAt L g 414 ⟨.elC .k 1, i, tt, s, ph, qp⟩) from fun t h => by loader_seg h hpre) hT⟩)
    (by inv_site hi hi.lead) (by inv_site hi hi.lead) h hf

theorem step_copy_k_1 (hpre : Pre P L mem0) (hs : d.site = .copy .k 1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_8)
  exact step_copy_of (d' := ⟨.wait .v, i, tt, s, ph, qp⟩) rfl
    (fun _ _ => by simp [next, afterCopy, afterUse, UseK.copies])
    (segTo_of (afterK hpre ⟨.copy .k 1, i, tt, s, ph, qp⟩ hi.s hi.ph) rfl (by live_dec)) (by
        inv_site hi hi.lead) h hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
