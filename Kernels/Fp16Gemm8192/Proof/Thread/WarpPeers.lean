-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.WarpLane

@[expose] public section

/-! # The lanes of a warp at a collective site

For a thread `g` at a collective site and a lane `h` of its warp (`coll_lane_fact`): `h` has made an
event of an instance of the site, or stopped before the site without exiting, or is at the site, or
at a site whose time is at least 2 below `g`'s. The lanes of a warp run the same prologue path (the
shuffle at event 0, warp 0's election at event 1 and warp barrier at `wbIdx`), and a role warp's
lane without an election is before it (`loader_unelected_thm`, `mma_unelected_thm`,
`sched_unelected_thm`), while one with an election made it at event 6 (`elect_pos`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow Prologue

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
include hpre hX

/-- A role warp's lane with an election has made its full-mask role election at event 6. -/
theorem role_lane_event {h j pc' mask inst leader : Nat} (hh : h < L.threads)
    (hel : X.Elect (h, j) pc' mask inst leader) {d : ThreadD} {s : CollSite}
    (h6 : Frame.stateAt (code L) X h 6 = some (some d)) (hs : d.coll = some s) (hw0 : warpOf L h ≠
      0) :
    ∃ e, X.get (h, 6) = some e ∧ s.Matches e := by
  obtain ⟨rfl, hlt⟩ := role_elect_event hpre hX hh hel hw0
  obtain ⟨e, he⟩ : ∃ e, (X.tr h)[6]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
  refine ⟨e, he, ?_⟩
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he h6
  rcases d with ⟨site, w⟩ | (l | ⟨site, w', q, fp, ap, cp, r, x⟩ | ⟨site, ap, cp, r, x⟩ | c)
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs <;> subst hs
    · obtain ⟨-, -, hc'⟩ := pro_end hpre hX hh hlt.le h6
      have := (pro_end hpre hX hh hlt.le h6).1
      simp [Prologue.index] at this
    · have := (pro_end hpre hX hh hlt.le h6).1
      simp [Prologue.index] at this
    · obtain ⟨-, h2, hc'⟩ := pro_end hpre hX hh hlt.le h6
      have := hc'.1 (.inr (.inr rfl))
      have := h2 (by omega)
      omega
    · change kernel.code[Prologue.Site.roleElect.pc]? = some ins at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_1)
      have hm : readBits L h t 32 (.reg 649) = .ok (BitVec.ofNat 64 4294967295) :=
        readBits_b32 (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
          (show 649 ∈ Flow.live Prologue.Site.roleElect.pc by table_decide))) (by decide)
      obtain ⟨inst', leader', rfl⟩ := fires_elect_full hm (by decide) hf
      exact ⟨inst', leader', rfl⟩
  · simp [ThreadD.coll] at hs
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs
    subst hs
    change kernel.code[Mma.Site.elect.pc]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_3)
    have hm : readBits L h t 32 (.reg 836) = .ok (BitVec.ofNat 64 4294967295) :=
      readBits_b32 (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
        (show 836 ∈ Flow.live Mma.Site.elect.pc by table_decide))) (by decide)
    obtain ⟨inst', leader', rfl⟩ := fires_elect_full hm (by decide) hf
    exact ⟨inst', leader', rfl⟩
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs
    subst hs
    change kernel.code[Scheduler.Site.elect.pc]? = some ins at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_2)
    have hm : readBits L h t 32 (.reg 630) = .ok (BitVec.ofNat 64 4294967295) :=
      readBits_b32 (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
        (show 630 ∈ Flow.live Scheduler.Site.elect.pc by table_decide))) (by decide)
    obtain ⟨inst', leader', rfl⟩ := fires_elect_full hm (by decide) hf
    exact ⟨inst', leader', rfl⟩
  · simp [ThreadD.coll] at hs

/-- **Where a lane of the warp stands**, for a thread at a collective site. -/
theorem coll_lane_fact (hg : g < L.threads) {d : ThreadD} {s : CollSite}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hs : d.coll =
      some s) {h : Nat}
    (hwh : SameWarp L g h) (hnu : ∀ k pc f, X.get (h, k) ≠ some ⟨pc, .ub f⟩) :
    (∃ j e, X.get (h, j) = some e ∧ s.Matches e) ∨
    (Frame.stateAt (code L) X h (X.tr h).length = none ∧
      (∀ pc, (X.tr h).getLast? ≠ some ⟨pc, .exit⟩) ∧
      s ≠ .shfl) ∨
    ∃ d', Frame.stateAt (code L) X h (X.tr h).length = some (some d') ∧
      (d'.coll = some s ∨ (d'.exitOff = none ∧ d'.vtime L h (X.tr h) + 2 ≤ d.vtime L g (X.tr g))) :=
        by
  have hh : h < L.threads := hwh.1.2.1
  have hwarp : warpOf L h = warpOf L g := hwh.2.symm
  rcases d with ⟨site, w⟩ | (l | ⟨site, w', q, fp, ap, cp, r, x⟩ | ⟨site, ap, cp, r, x⟩ | c)
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs <;> subst hs
    · -- the shuffle: a lane has made its shuffle, or is at its first state
      by_cases h0 : X.tr h = []
      · right; right
        refine ⟨.inl ⟨.shfl, 0⟩, ?_, .inl rfl⟩
        rw [h0]
        exact stateAt_zero L X h
      · left
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil h0
        have he : X.get (h, 0) = some x := by change (X.tr h)[0]? = _; rw [hx]; rfl
        rw [first_event hpre hX hh he] at he
        exact ⟨0, _, he, _, _, _, _, _, _, _, rfl⟩
    · -- warp 0's election
      have hl := (pro_end hpre hX hg le_rfl hσ).1
      simp only [Prologue.index] at hl
      have hw0 : warpOf L g = 0 := by
        rw [← (pro_end hpre hX hg le_rfl hσ).2.1 (by omega)]
        exact (pro_end hpre hX hg le_rfl hσ).2.2.1 (.inl rfl)
      have hvg : (ThreadD.vtime L g (X.tr g) (.inl ⟨.elect, w⟩)) = 2 := rfl
      rcases Nat.lt_trichotomy (X.tr h).length 1 with hlt | heq | hgt
      · right; right
        refine ⟨.inl ⟨.shfl, 0⟩, ?_, .inr ⟨rfl, ?_⟩⟩
        · rw [show (X.tr h).length = 0 by omega]
          exact stateAt_zero L X h
        · rw [hvg]; rfl
      · right; right
        have h1 := stateAt_one hpre hX hh (by omega)
        rw [hwarp, hw0, heq] at *
        refine ⟨_, h1, .inl ?_⟩
        rfl
      · left
        obtain ⟨inst, leader, he⟩ := elect_event hpre hX hh (by omega) hgt
        exact ⟨1, _, he, inst, leader, rfl⟩
    · -- warp 0's warp barrier
      obtain ⟨hl, hw0⟩ := wb_end hpre hX hg hσ
      have hw0h : warpOf L h = 0 := hwarp.trans hw0
      have hvg : (ThreadD.vtime L g (X.tr g) (.inl ⟨.warpBar, w⟩)) = 44 := rfl
      by_cases hlt : wbIdx L h < (X.tr h).length
      · left
        obtain ⟨inst, he⟩ := warpBar_event hpre hX hh hw0h hnu hlt
        exact ⟨_, _, he, _, inst, rfl⟩
      · cases hσh : Frame.stateAt (code L) X h (X.tr h).length with
        | none =>
          right; left
          refine ⟨rfl, not_exit_before_wait hpre hX hh ?_, by simp⟩
          have := wbIdx_lt_wait (L := L) (g := h)
          rw [hw0h]
          omega
        | some σ =>
          cases σ with
          | none => exact absurd hσh (tracked hpre hX h _ hh)
          | some d' =>
            right; right
            refine ⟨d', rfl, ?_⟩
            rcases d' with q | r
            · obtain ⟨h1, h2, hc⟩ := pro_end hpre hX hh le_rfl hσh
              have hq0 : q.site ≠ .shfl → q.w = 0 := fun hq =>
                (h2 (by have := Prologue.index_pos (L := L) (g := h) hq; omega)).trans hw0h
              obtain ⟨hat, hbefore⟩ := w0_site hq0 hc (by omega)
              rcases Nat.lt_or_ge (index L h q) (wbIdx L h) with hlt' | hge
              · refine .inr ⟨rfl, ?_⟩
                rw [hvg]
                exact hbefore hlt'
              · have hsite := hat (by omega)
                obtain ⟨site, w2⟩ := q
                simp only at hsite
                subst hsite
                exact .inl rfl
            · exfalso
              have := (onPath_all hpre hX hh _ le_rfl).2 r hσh
              have h2 := wbIdx_lt_wait (L := L) (g := h)
              rw [hw0h] at this
              omega
    · -- warp 11's role election
      obtain ⟨hl, hw11⟩ := roleElect_end hpre hX hg hσ
      have hw11h : warpOf L h = 11 := hwarp.trans hw11
      have hvg : (ThreadD.vtime L g (X.tr g) (.inl ⟨.roleElect, w⟩)) = 56 := rfl
      by_cases hel : ∃ j pc' mask inst leader, X.Elect (h, j) pc' mask inst leader
      · left
        obtain ⟨j, pc', mask, inst, leader, hj⟩ := hel
        have h6 := (role_elect_event hpre hX hh hj (by omega)).2
        obtain ⟨e, he, hm⟩ := role_lane_event hpre hX hh hj
          (loaderPath6 hpre hX hh hw11h (by omega)) rfl (by omega)
        exact ⟨6, e, he, hm⟩
      · push Not at hel
        obtain ⟨d', hσh, ⟨q, rfl⟩, hx, hv⟩ := loader_unelected_thm hpre hX hh hw11h hel
        right; right
        refine ⟨_, hσh, ?_⟩
        by_cases hq : q.site = .roleElect
        · obtain ⟨site, w2⟩ := q
          simp only at hq
          subst hq
          exact .inl rfl
        · refine .inr ⟨hx, ?_⟩
          rw [hvg]
          have := Prologue.Site.vtime_le_of_ne q.site hq
          change q.site.vtime + 2 ≤ 56
          omega
  · simp [ThreadD.coll] at hs
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs
    subst hs
    obtain ⟨hl, hw89, hlead⟩ := mma_elect_len hpre hX hg hσ rfl
    have hw89h : warpOf L h = 8 ∨ warpOf L h = 9 := by rw [hwarp]; exact hw89
    have hleadh : h / L.block % 2 = 0 := by rw [← hwh.1.2.2]; exact hlead
    have hvg : (ThreadD.vtime L g (X.tr g) (.inr (.mma ⟨.elect, w', q, fp, ap, cp, r, x⟩))) = 58 :=
      rfl
    by_cases hel : ∃ j pc' mask inst leader, X.Elect (h, j) pc' mask inst leader
    · left
      obtain ⟨j, pc', mask, inst, leader, hj⟩ := hel
      have h6 := (role_elect_event hpre hX hh hj (by omega)).2
      have hs6 := mmaPath6 hpre hX hh hw89h (by omega)
      have hld : Loader.leader L h = true := by simp [Loader.leader, hleadh]
      obtain ⟨e, he, hm⟩ := role_lane_event (s := .mmaElect) hpre hX hh hj hs6
        (by simp [ThreadD.coll, mmaStart, hld]) (by omega)
      exact ⟨6, e, he, hm⟩
    · push Not at hel
      obtain ⟨d', hσh, hx, hv⟩ := mma_unelected_thm hpre hX hh hleadh hw89h hel
      right; right
      refine ⟨_, hσh, ?_⟩
      rcases d' with q' | r'
      · refine .inr ⟨hx, ?_⟩
        rw [hvg]
        have := Prologue.Site.vtime_le q'.site
        change q'.site.vtime + 2 ≤ 58
        omega
      · have hrw := role_warp hpre hX hh _ le_rfl _ hσh
        cases r' with
        | loader l' => simp only [roleWarp] at hrw; omega
        | sched s' => simp only [roleWarp] at hrw; omega
        | cons c' => simp only [roleWarp] at hrw; omega
        | mma m' =>
          by_cases hm' : m'.site = .elect
          · obtain ⟨site, w2, q2, fp2, ap2, cp2, r2, x2⟩ := m'
            simp only at hm'
            subst hm'
            exact .inl rfl
          · exfalso
            have := Mma.vtime_ge (D := mmaCount L h (X.tr h)) hx hm'
            change Mma.vtime (mmaCount L h (X.tr h)) m' ≤ 58 at hv
            omega
  · cases site <;> simp only [ThreadD.coll, reduceCtorEq, Option.some.injEq] at hs
    subst hs
    obtain ⟨hl, hw10⟩ := sched_elect_len hpre hX hg hσ rfl
    have hw10h : warpOf L h = 10 := hwarp.trans hw10
    have hvg : (ThreadD.vtime L g (X.tr g) (.inr (.sched ⟨.elect, ap, cp, r, x⟩))) = 58 := rfl
    by_cases hel : ∃ j pc' mask inst leader, X.Elect (h, j) pc' mask inst leader
    · left
      obtain ⟨j, pc', mask, inst, leader, hj⟩ := hel
      have h6 := (role_elect_event hpre hX hh hj (by omega)).2
      obtain ⟨e, he, hm⟩ := role_lane_event hpre hX hh hj
        (schedPath6 hpre hX hh hw10h (by omega)) rfl (by omega)
      exact ⟨6, e, he, hm⟩
    · push Not at hel
      obtain ⟨d', hσh, hcase, hx, hv⟩ := sched_unelected_thm hpre hX hh hw10h hel
      right; right
      refine ⟨_, hσh, ?_⟩
      rcases hcase with ⟨q', rfl⟩ | rfl
      · refine .inr ⟨hx, ?_⟩
        rw [hvg]
        have := Prologue.Site.vtime_le q'.site
        change q'.site.vtime + 2 ≤ 58
        omega
      · exact .inl rfl
  · simp [ThreadD.coll] at hs

end

end
end PTX.Kernels.Fp16Gemm8192.Proof
