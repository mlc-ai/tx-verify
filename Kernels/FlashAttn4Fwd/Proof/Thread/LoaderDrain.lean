-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderBase

@[expose] public section

/-! # The loader's drain and tail

After its last item the loader polls each KV slot's empty barrier once more, in ring order
from the next slot (`drain k`: the slot `sAfter k s` with parity `pAfter k s ph`, the ring
advancing between the polls, cut at each wrap `selp`), then the stage-1 Q slot's empty barrier
(`drainQ`); on the leader CTA one elected lane arrives on the stage-1 Q full barrier once more
(`elTail`, `arriveTail`). Every path then leaves through the role tests to the exit. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work
open Prologue (sb)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

variable {d : D} {t u : TState} {e : Event} {ins : Instr}

theorem step_drain0 (hpre : Pre P L mem0) (hs : d.site = .drain 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_6)
  have hs6 : s < 6 := hi.s
  have hph : ph < 2 := hi.ph
  have h2 := pAfter_lt (s := s) hph 0
  have h1 := sAfter_lt hs6 0
  refine step_wait_of (dok := ⟨.drain 1, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ => by simp [next]) (fun _ _ _ _ => by simp [next])
    ⟨2, fun t h => by loader_seg h hpre⟩ ⟨3 + 6, ?_⟩ hi
    ⟨hi.s, hi.ph, hi.qp, fun h => by simp [Site.inItem] at h, fun h => by simp [Site.inTrip] at h,
      fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩ h hf
  refine seg_wrap (p := 93) (pcS := 476) (d := ⟨.drain 0, i, tt, s, ph, qp⟩) (c := s + 1 = 6)
    (fun t h => by loader_seg h hpre [sAfter_zero]) (tbl_mem (by live_dec) (by
      simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]))
    fun b hb t h => ?_
  cases b
  · have hw : ¬ s + 1 = 6 := by simpa using hb
    simp only [sAfter_zero, pAfter_zero] at h1 h2
    loader_seg h hpre [sAfter_zero, pAfter_zero, sAfter_succ, pAfter_succ, snext_nowrap hw,
      pnext_nowrap hw, xor_bit_zero h2]
  · have hw : s + 1 = 6 := by simpa using hb
    simp only [sAfter_zero, pAfter_zero] at h1 h2
    loader_seg h hpre [sAfter_zero, pAfter_zero, sAfter_succ, pAfter_succ, snext_wrap hw,
      pnext_wrap hw, xor_bit_one h2]

theorem step_drain1 (hpre : Pre P L mem0) (hs : d.site = .drain 1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_7)
  have hs6 : s < 6 := hi.s
  have hph : ph < 2 := hi.ph
  have h2 := pAfter_lt (s := s) hph 1
  have h1 := sAfter_lt hs6 1
  refine step_wait_of (dok := ⟨.drain 2, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ => by simp [next]) (fun _ _ _ _ => by simp [next])
    ⟨2, fun t h => by loader_seg h hpre⟩ ⟨3 + 6, ?_⟩ hi
    ⟨hi.s, hi.ph, hi.qp, fun h => by simp [Site.inItem] at h, fun h => by simp [Site.inTrip] at h,
      fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩ h hf
  refine seg_wrap (p := 94) (pcS := 487) (d := ⟨.drain 1, i, tt, s, ph, qp⟩) (c := sAfter 1 s + 1
      = 6)
    (fun t h => by loader_seg h hpre [sAfter_zero]) (tbl_mem (by live_dec) (by
      simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]))
    fun b hb t h => ?_
  cases b
  · have hw : ¬ sAfter 1 s + 1 = 6 := by simpa using hb
    simp only [sAfter_succ, sAfter_zero, pAfter_succ, pAfter_zero] at hw h1 h2
    loader_seg h hpre [sAfter_zero, pAfter_zero, sAfter_succ, pAfter_succ, snext_nowrap hw,
      pnext_nowrap hw, xor_bit_zero h2]
  · have hw : sAfter 1 s + 1 = 6 := by simpa using hb
    simp only [sAfter_succ, sAfter_zero, pAfter_succ, pAfter_zero] at hw h1 h2
    loader_seg h hpre [sAfter_zero, pAfter_zero, sAfter_succ, pAfter_succ, snext_wrap hw,
      pnext_wrap hw, xor_bit_one h2]

theorem step_drain2 (hpre : Pre P L mem0) (hs : d.site = .drain 2) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_8)
  have hs6 : s < 6 := hi.s
  have hph : ph < 2 := hi.ph
  have h2 := pAfter_lt (s := s) hph 2
  have h1 := sAfter_lt hs6 2
  refine step_wait_of (dok := ⟨.drain 3, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ => by simp [next]) (fun _ _ _ _ => by simp [next])
    ⟨2, fun t h => by loader_seg h hpre⟩ ⟨3 + 6, ?_⟩ hi
    ⟨hi.s, hi.ph, hi.qp, fun h => by simp [Site.inItem] at h, fun h => by simp [Site.inTrip] at h,
      fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩ h hf
  refine seg_wrap (p := 95) (pcS := 498) (d := ⟨.drain 2, i, tt, s, ph, qp⟩) (c := sAfter 2 s + 1
      = 6)
    (fun t h => by loader_seg h hpre [sAfter_zero]) (tbl_mem (by live_dec) (by
      simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]))
    fun b hb t h => ?_
  cases b
  · have hw : ¬ sAfter 2 s + 1 = 6 := by simpa using hb
    simp only [sAfter_succ, sAfter_zero, pAfter_succ, pAfter_zero] at hw h1 h2
    loader_seg h hpre [sAfter_zero, pAfter_zero, sAfter_succ, pAfter_succ, snext_nowrap hw,
      pnext_nowrap hw, xor_bit_zero h2]
  · have hw : sAfter 2 s + 1 = 6 := by simpa using hb
    simp only [sAfter_succ, sAfter_zero, pAfter_succ, pAfter_zero] at hw h1 h2
    loader_seg h hpre [sAfter_zero, pAfter_zero, sAfter_succ, pAfter_succ, snext_wrap hw,
      pnext_wrap hw, xor_bit_one h2]

theorem step_drain3 (hpre : Pre P L mem0) (hs : d.site = .drain 3) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_9)
  have hs6 : s < 6 := hi.s
  have hph : ph < 2 := hi.ph
  have h2 := pAfter_lt (s := s) hph 3
  have h1 := sAfter_lt hs6 3
  refine step_wait_of (dok := ⟨.drain 4, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ => by simp [next]) (fun _ _ _ _ => by simp [next])
    ⟨2, fun t h => by loader_seg h hpre⟩ ⟨3 + 6, ?_⟩ hi
    ⟨hi.s, hi.ph, hi.qp, fun h => by simp [Site.inItem] at h, fun h => by simp [Site.inTrip] at h,
      fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩ h hf
  refine seg_wrap (p := 96) (pcS := 509) (d := ⟨.drain 3, i, tt, s, ph, qp⟩) (c := sAfter 3 s + 1
      = 6)
    (fun t h => by loader_seg h hpre [sAfter_zero]) (tbl_mem (by live_dec) (by
      simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]))
    fun b hb t h => ?_
  cases b
  · have hw : ¬ sAfter 3 s + 1 = 6 := by simpa using hb
    simp only [sAfter_succ, sAfter_zero, pAfter_succ, pAfter_zero] at hw h1 h2
    loader_seg h hpre [sAfter_zero, pAfter_zero, sAfter_succ, pAfter_succ, snext_nowrap hw,
      pnext_nowrap hw, xor_bit_zero h2]
  · have hw : sAfter 3 s + 1 = 6 := by simpa using hb
    simp only [sAfter_succ, sAfter_zero, pAfter_succ, pAfter_zero] at hw h1 h2
    loader_seg h hpre [sAfter_zero, pAfter_zero, sAfter_succ, pAfter_succ, snext_wrap hw,
      pnext_wrap hw, xor_bit_one h2]

theorem step_drain4 (hpre : Pre P L mem0) (hs : d.site = .drain 4) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_10)
  have hs6 : s < 6 := hi.s
  have hph : ph < 2 := hi.ph
  have h2 := pAfter_lt (s := s) hph 4
  have h1 := sAfter_lt hs6 4
  refine step_wait_of (dok := ⟨.drain 5, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ => by simp [next]) (fun _ _ _ _ => by simp [next])
    ⟨2, fun t h => by loader_seg h hpre⟩ ⟨3 + 6, ?_⟩ hi
    ⟨hi.s, hi.ph, hi.qp, fun h => by simp [Site.inItem] at h, fun h => by simp [Site.inTrip] at h,
      fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩ h hf
  refine seg_wrap (p := 97) (pcS := 520) (d := ⟨.drain 4, i, tt, s, ph, qp⟩) (c := sAfter 4 s + 1
      = 6)
    (fun t h => by loader_seg h hpre [sAfter_zero]) (tbl_mem (by live_dec) (by
      simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]))
    fun b hb t h => ?_
  cases b
  · have hw : ¬ sAfter 4 s + 1 = 6 := by simpa using hb
    simp only [sAfter_succ, sAfter_zero, pAfter_succ, pAfter_zero] at hw h1 h2
    loader_seg h hpre [sAfter_zero, pAfter_zero, sAfter_succ, pAfter_succ, snext_nowrap hw,
      pnext_nowrap hw, xor_bit_zero h2]
  · have hw : sAfter 4 s + 1 = 6 := by simpa using hb
    simp only [sAfter_succ, sAfter_zero, pAfter_succ, pAfter_zero] at hw h1 h2
    loader_seg h hpre [sAfter_zero, pAfter_zero, sAfter_succ, pAfter_succ, snext_wrap hw,
      pnext_wrap hw, xor_bit_one h2]

theorem step_drain5 (hpre : Pre P L mem0) (hs : d.site = .drain 5) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_11)
  exact step_wait_of (dok := ⟨.drainQ, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ => by simp [next]) (fun _ _ _ _ => by simp [next])
    ⟨2, fun t h => by loader_seg h hpre⟩ ⟨1, fun t h => by loader_seg h hpre⟩ hi
    ⟨hi.s, hi.ph, hi.qp, fun h => by simp [Site.inItem] at h, fun h => by simp [Site.inTrip] at h,
      fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩ h hf

theorem step_drainQ (hpre : Pre P L mem0) (hs : d.site = .drainQ) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_12)
  refine step_wait_of (dok := if rank L g = 0 then ⟨.elTail, i, tt, s, ph, qp⟩ else ⟨.exit, i, tt,
      s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ => by simp [next]) (fun _ _ _ _ => by simp [next])
    ⟨2, fun t h => by loader_seg h hpre⟩ ?_ hi ?_ h hf
  · have h1 := Seg.bra (K := kernel) (A := asms) (L := L) (g := g) Flow.code_530
      (List.mem_cons_self (a := (5341, Value.pred true)) (l := factsAt L g 529 ⟨.drainQ, i, tt, s,
          ph, qp⟩)) (fun _ _ => asms_localRule_none)
    simp only [↓reduceIte] at h1
    have h2 := seg_rank (L := L) (g := g) Flow.code_532
      (List.mem_cons_of_mem (5341, Value.pred true) (tbl_mem (pc := 529) (d := ⟨.drainQ, i, tt, s,
          ph, qp⟩)
        (by live_dec) (val92 L g _)))
    by_cases hr : rank L g = 0
    · simp only [hr, ↓reduceIte] at h2 ⊢
      exact ⟨1 + 1, Seg.weaken_end (Seg.comp h1 h2) fun R hR => holds_relive hR.2 rfl
        (by live_dec)⟩
    · simp only [hr, ↓reduceIte] at h2 ⊢
      have h3 : Seg kernel asms L g 9 538 ((5341, .pred true) :: factsAt L g 529 ⟨.drainQ, i, tt,
          s, ph, qp⟩) 4896
          (facts L g ⟨.exit, i, tt, s, ph, qp⟩) := fun t h => by loader_seg h hpre
      exact ⟨1 + 1 + 9, Seg.comp (Seg.comp h1 h2) h3⟩
  · split_ifs with hr
    · exact ⟨hi.s, hi.ph, hi.qp, fun h => by simp [Site.inItem] at h,
        fun h => by simp [Site.inTrip] at h, fun _ => hr,
        fun u j h => by rcases h with h | h <;> cases h⟩
    · exact ⟨hi.s, hi.ph, hi.qp, fun h => by simp [Site.inItem] at h, fun h => by simp
        [Site.inTrip] at h,
      fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩

theorem step_elTail (hpre : Pre P L mem0) (hs : d.site = .elTail) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_31)
  refine step_elect_of (dl := ⟨.arriveTail, i, tt, s, ph, qp⟩) (ds := ⟨.exit, i, tt, s, ph, qp⟩)
      rfl (by live_dec)
    (by live_dec) (by decide) (fun _ _ _ => by simp only [next]; split_ifs <;> rfl)
    (fun ld => ⟨3, fun t h => by loader_seg h hpre⟩)
    (fun ld => ⟨11, fun t h => by loader_seg h hpre⟩)
    ⟨hi.s, hi.ph, hi.qp, fun h => by simp [Site.inItem] at h,
      fun h => by simp [Site.inTrip] at h, fun _ => hi.lead rfl,
      fun u j h => by rcases h with h | h <;> cases h⟩ ⟨hi.s, hi.ph, hi.qp, fun h => by simp
          [Site.inItem] at h, fun h => by simp [Site.inTrip] at h,
      fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩ h hf

theorem step_arriveTail (hpre : Pre P L mem0) (hs : d.site = .arriveTail) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, s, ph, qp⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_6)
  exact step_arrive_of (d' := ⟨.exit, i, tt, s, ph, qp⟩) rfl (by live_dec)
    (fun _ _ _ _ _ _ => by simp only [next]) ⟨9, fun t h => by loader_seg h hpre⟩ ⟨hi.s, hi.ph,
        hi.qp, fun h => by simp [Site.inItem] at h, fun h => by simp [Site.inTrip] at h,
      fun h => by simp [Site.leadOnly] at h, fun u j h => by rcases h with h | h <;> cases h⟩ h hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
