-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderItemEnd

@[expose] public section

/-! # The loader's last V tile of an item (`v0`)

The poll of the next KV slot's empty barrier, the leader CTA's arrival on its full barrier and
the one copy of the V tile; before the copy the full barrier's address with the peer-bit mask
and the destination as the window pointer plus the slot's offset. After it the KV ring moves
past the slot (cut at the wrap `selp`), and the item either enters its trip loop (`n ≥ 2`) or
ends (`itemEnd`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work
open Prologue (sb)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- After the copy: the KV ring past the slot, then the first trip's K poll or the item's end. -/
theorem afterV0 (hpre : Pre P L mem0) (d : D) (hi : d.i < T L g) (hs : d.s < 6)
    (hph : d.ph < 2) : SegTo L g 371 (factsAt L g 371 d) (afterUse L g d .v0) := by
  have h1 := snext_lt hs
  have h2 := pnext_lt (s := d.s) hph
  let d' : D := { d with s := sAfter 2 d.s, ph := pAfter 2 d.s d.ph }
  have hA : Seg kernel asms L g (3 + 3) 371 (factsAt L g 371 d) 377 (factsAt L g 377 d') := by
    refine seg_wrap (p := 77) (pcS := 374) (d := d) (c := snext d.s + 1 = 6)
      (fun t h => by loader_seg h hpre) (tbl_mem (by live_dec) (by
        simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some])) fun b hb t h => ?_
    cases b
    · have hw : ¬ snext d.s + 1 = 6 := by simpa using hb
      loader_seg h hpre [d', sAfter_two, pAfter_two, snext_nowrap hw, pnext_nowrap hw,
        xor_bit_zero h2]
    · have hw : snext d.s + 1 = 6 := by simpa using hb
      loader_seg h hpre [d', sAfter_two, pAfter_two, snext_wrap hw, pnext_wrap hw,
        xor_bit_one h2]
  have hs' : d'.s < 6 := sAfter_lt hs 2
  obtain ⟨k, hB⟩ := segTo_bra (L := L) (g := g) (pc := 377) (c := decide (n L < 2))
    (d1 := afterUse.itemEndOf L g d') (d2 := { d' with site := .wait .k, t := 0 })
    Flow.code_377 (tbl_mem (pc := 377) (d := d') (r := 76) (by live_dec) (by
      simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]))
    (fun _ => segTo_of (itemEnd hpre d' hi hs') rfl (by live_dec))
    (fun _ => ⟨4, fun t h => by loader_seg h hpre⟩)
  refine ⟨3 + 3 + k, ?_⟩
  simp only [afterUse]
  by_cases hn : n L < 2
  · simp only [hn, decide_true, ↓reduceIte, show ¬ 2 ≤ n L by omega] at hB ⊢
    exact Seg.comp hA hB
  · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte, show 2 ≤ n L by omega]
      at hB ⊢
    exact Seg.comp hA hB

theorem afterV0_inv (hpre : Pre P L mem0) {d : D} (hi : Inv L g d) (hit : d.i < T L g) :
    Inv L g (afterUse L g d .v0) := by
  have hn := (shape hpre).2.2.2.2.2.1
  simp only [afterUse]
  split_ifs with h2
  · exact ⟨sAfter_lt hi.s 2, pAfter_lt hi.ph 2, hi.qp, fun _ => hit, fun _ => by dsimp only; omega,
      fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩
  · exact itemEnd_inv _ (sAfter_lt hi.s 2) (pAfter_lt hi.ph 2) hi.qp

variable {d : D} {t u : TState} {e : Event} {ins : Instr}

theorem step_wait_v0 (hpre : Pre P L mem0) (hs : d.site = .wait .v0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_3)
  refine step_wait_of (dok := if rank L g = 0 then ⟨.elA .v0, i, tt, s, ph, qp⟩
      else ⟨.elC .v0 0, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ => by simp [next]) (fun _ _ _ _ => by simp [next])
    ⟨2, fun t h => by loader_seg h hpre⟩
    (seg_wait_ok (w := 351) rfl Flow.code_352 Flow.code_354 rfl (by live_dec) (by live_dec)
      (segTo_here rfl rfl (by live_dec)) (by live_dec)) hi ?_ h hf
  split_ifs with hr
  · inv_site hi hr
  · inv_site hi hr

theorem step_elA_v0 (hpre : Pre P L mem0) (hs : d.site = .elA .v0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_24)
  have hr : rank L g = 0 := hi.lead rfl
  refine step_elect_of (dl := ⟨.arrive .v0, i, tt, s, ph, qp⟩)
    (ds := ⟨.elC .v0 0, i, tt, s, ph, qp⟩) rfl (by live_dec) (by live_dec) (by decide)
    (fun _ _ _ => by simp only [next]; split_ifs <;> rfl)
    (fun ld => ⟨3, fun t h => by loader_seg h hpre⟩) (fun ld => ?_)
    (by inv_site hi hr) (by inv_site hi hr) h hf
  exact ⟨2, fun t h => by loader_seg h hpre⟩

theorem step_arrive_v0 (hs : d.site = .arrive .v0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_3)
  have hr : rank L g = 0 := hi.lead rfl
  exact step_arrive_of (d' := ⟨.elC .v0 0, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ _ _ => by simp only [next])
    (segTo_here rfl rfl (by live_dec)) (by inv_site hi hr) h hf

theorem step_elC_v0 (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .elC .v0 j)
    (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_25)
  obtain rfl : j = 0 := Fin.ext (by
    have := hi.one .v0 j (.inl rfl)
    simp [UseK.copies] at this
    omega)
  have hb := (shape hpre).1
  have hs6 : s < 6 := hi.s
  have h1 := snext_lt hs6
  have hit : i < T L g := hi.item rfl
  obtain ⟨k, hT⟩ := afterV0 (g := g) hpre ⟨.elC .v0 0, i, tt, s, ph, qp⟩ hit hs6 hi.ph
  refine step_elect_of (dl := ⟨.copy .v0 0, i, tt, s, ph, qp⟩)
    (ds := afterUse L g ⟨.elC .v0 0, i, tt, s, ph, qp⟩ .v0) rfl (by live_dec) (by live_dec) (by
        decide)
    (fun _ _ _ => by simp only [next, afterCopy, UseK.copies]; split_ifs <;> rfl)
    (fun ld => ?_)
    (fun ld => ⟨2 + k, Seg.comp (show Seg kernel asms L g 2 _ _ 371
      (factsAt L g 371 ⟨.elC .v0 0, i, tt, s, ph, qp⟩) from fun t h => by loader_seg h hpre) hT⟩)
    (by inv_site hi hi.lead) (afterV0_inv hpre hi hit) h hf
  have hA : Seg kernel asms L g 4 361 ((74, .pred true) ::
      (776, .bits 32 (BitVec.ofNat 64 ld)) :: facts L g ⟨.elC .v0 0, i, tt, s, ph, qp⟩) 365
          (factsAt L g 365 ⟨.elC .v0 0, i, tt, s, ph, qp⟩) :=
    fun t h => by loader_seg h hpre
  have hP := seg_peer (L := L) (g := g) (F := factsAt L g 365 ⟨.elC .v0 0, i, tt, s, ph, qp⟩) hpre
      hg Flow.code_365
    (by decide) (tbl_mem (r := 778) (by live_dec)
      (by simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]))
    (k := 32 + 8 * snext s) (by omega) (facts_ne (by live_dec))
  have hQ := seg_ptr (L := L) (g := g) (i := ctaOf L g) (c := ctaOf L g)
    (a := L.sharedBase + 0) (k := 16384 * snext s) (b := L.sharedBase + 16384 * snext s)
    (F := (779, peerV L g (32 + 8 * snext s)) :: factsAt L g 365 ⟨.elC .v0 0, i, tt, s, ph, qp⟩)
        Flow.code_366
    (List.mem_cons_of_mem _ (tbl_mem (r := 356) (by live_dec)
      (by simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, win])))
    (List.mem_cons_of_mem _ (tbl_mem (r := 777) (by live_dec)
      (by simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some])))
    (by omega) (by omega) (by omega) (cons_ne (ex := [(779, _)]) (by simp) (by live_dec))
  have hR : Seg kernel asms L g 3 367 ((780, .ptr 32 false (.shared (ctaOf L g) (ctaOf L g))
        (BitVec.ofNat 64 (L.sharedBase + 16384 * snext s))) ::
      (779, peerV L g (32 + 8 * snext s)) :: factsAt L g 365 ⟨.elC .v0 0, i, tt, s, ph, qp⟩) 370
      (facts L g ⟨.copy .v0 0, i, tt, s, ph, qp⟩) := fun t h => by loader_seg h hpre
  exact ⟨4 + (1 + (1 + 3)), Seg.comp hA (Seg.comp hP (Seg.comp hQ hR))⟩

theorem step_copy_v0 (hpre : Pre P L mem0) (hs : d.site = .copy .v0 j) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_6)
  obtain rfl : j = 0 := Fin.ext (by
    have := hi.one .v0 j (.inr rfl)
    simp [UseK.copies] at this
    omega)
  have hit : i < T L g := hi.item rfl
  exact step_copy_of (d' := afterUse L g ⟨.copy .v0 0, i, tt, s, ph, qp⟩ .v0) rfl
    (fun _ _ => by simp [next, afterCopy, UseK.copies])
    (segTo_of (afterV0 hpre ⟨.copy .v0 0, i, tt, s, ph, qp⟩ hit hi.s hi.ph) rfl (by live_dec))
    (afterV0_inv hpre hi hit) h hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
