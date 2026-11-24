-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrOAcc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrValues

@[expose] public section

/-! # A correction store and the rescale's wait (`OAccFacts.corr_st`)

A correction `tcgen05.st` is the store of rescale chunk `j` of stage `st` (`corr_tst`), in the
trip's credit `q = n i + 1 + t` of the stage's P-ready barrier, after the chunk's load in the
same credit (`Counts.rsLd`). From its state the machine runs through the rescale's sites (the
remaining chunks' loads, waits and stores) to the rescale's wait, each in the same item and trip
(`Correction.rs_next`); a chunk's wait may stop the machine. A later event that is neither a
`tcgen05` event nor undefined behaviour fires from a followed state (`Frame.event_state`) that is
not a site of the rescale but the wait (whose event is a `tcgen05` event), so the rescale's
`wait::st` is before it, in the same credit (`OAccFacts_corr_st`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Correction

/-- A site of stage `st`'s rescale. -/
def RsIn (st : Fin 2) (d : D) : Prop :=
  (∃ j, d.site = .rld st j) ∨ (∃ j, d.site = .rldW st j) ∨ (∃ j, d.site = .rst st j) ∨
    d.site = .rwait st

theorem rs_freePos {L : Launch} {st : Fin 2} {d : D} (h : RsIn st d) :
    freePos L st.val d = 1 + d.t := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  simp only [RsIn] at h ⊢
  rcases h with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl <;> fin_cases st <;> simp [freePos]

/-- **A step from a rescale site before its wait** stops the machine or is at a site of the
rescale, in the same item and trip. -/
theorem rs_next {L : Launch} {g : Nat} {st : Fin 2} {d : D} {e : Event} (h : RsIn st d)
    (hne : d.site ≠ .rwait st) (hev : Ev L g d e) :
    next L g d e = none ∨
      ∃ d', next L g d e = some (some d') ∧ RsIn st d' ∧ d'.i = d.i ∧ d'.t = d.t := by
  obtain ⟨-, hk⟩ := hev
  obtain ⟨epc, ek⟩ := e
  obtain ⟨site, i, t, aw, a, o⟩ := d
  simp only [RsIn] at h hne hk ⊢
  rcases h with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl
  · obtain ⟨vals, hk⟩ := hk
    subst hk
    exact .inr ⟨_, rfl, .inr (.inl ⟨j, rfl⟩), rfl, rfl⟩
  · simp only [next]
    split_ifs
    · exact .inr ⟨_, rfl, .inr (.inr (.inl ⟨j, rfl⟩)), rfl, rfl⟩
    · exact .inl rfl
  · simp only [next]
    split_ifs with hj
    · exact .inr ⟨_, rfl, .inl ⟨_, rfl⟩, rfl, rfl⟩
    · exact .inr ⟨_, rfl, .inr (.inr (.inr rfl)), rfl, rfl⟩
  · exact absurd rfl hne

/-- The event of a rescale site is a `tcgen05` event. -/
theorem rs_tc {L : Launch} {g : Nat} {st : Fin 2} {d : D} {e : Event} (h : RsIn st d)
    (hev : Ev L g d e) : ∃ tk, e.kind = .tc tk := by
  obtain ⟨-, hk⟩ := hev
  obtain ⟨site, i, t, aw, a, o⟩ := d
  simp only [RsIn] at h
  rcases h with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl <;> simp only at hk
  · obtain ⟨vals, hk⟩ := hk; exact ⟨_, hk⟩
  · exact ⟨_, hk⟩
  · obtain ⟨vals, hk⟩ := hk; exact ⟨_, hk⟩
  · exact ⟨_, hk⟩

end Correction

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **`OAccFacts.corr_st`**: a correction store of credit `q ≥ 1` writes its row of one stage's
accumulator, after a load of the same credit; every later event of the thread that is neither a
`tcgen05` event nor undefined behaviour comes after the rescale's `wait::st`, of the same
credit. -/
theorem OAccFacts_corr_st {h i a : Nat} {vals : List Value} (_hh : h < L.threads)
    (hw : 8 ≤ warpOf L h) (hw' : warpOf L h < 12) (hs : X.TSt (h, i) a vals .s32x32b) :
    ∃ st < 2, (∀ j < vals.length, InO st (tcDataCell32 L h a j)) ∧ 1 ≤ pArr L X h st i ∧
      (∃ i' a' vals', i' < i ∧ X.TLd (h, i') a' vals' .s32x32b ∧
        (∀ j < vals'.length, InO st (tcDataCell32 L h a' j)) ∧
          pArr L X h st i' = pArr L X h st i) ∧
      ∀ e, NonTcAfter X h i e →
        ∃ w pc, i < w ∧ w < e ∧ X.get (h, w) = some ⟨pc, .tc .waitSt⟩ ∧
          pArr L X h st w = pArr L X h st i := by
  obtain ⟨pc, he⟩ := hs
  obtain ⟨d, st, j0, hσ, hc, hi, hsd, rfl, hl⟩ := corr_tst hpre hX ht hw hw' he
  have hrs : Correction.RsIn st d := .inr (.inr (.inl ⟨j0, hsd⟩))
  have hcell : ∀ j < 16, InO st.val
      (tcDataCell32 L h (Correction.tmem L h (256 + 128 * st.val + 16 * j0.val)) j) := by
    intro j hj
    have hcol := tmem_column L h h (256 + 128 * st.val + 16 * j0.val) j (by omega)
    simp only [InO, hcol]
    omega
  -- the credit of a state of the rescale
  have hq : ∀ {q : Nat} {dq : Correction.D}, Correction.Counts L h dq ((X.tr h).take q) →
      Correction.RsIn st dq → dq.i = d.i → dq.t = d.t →
      pArr L X h st.val q = Correction.trips L * d.i + (1 + d.t) := by
    intro q dq hcq hr hi' ht'
    rw [pArr, pReadyBar_lead, hcq.free st.val st.isLt, Correction.rs_freePos hr, hi', ht']
  have hqi := hq hc hrs rfl rfl
  refine ⟨st.val, st.isLt, fun j hj => hcell j (by omega), by rw [hqi]; omega, ?_, ?_⟩
  · -- the chunk's load in the same credit
    obtain ⟨r, hr, pcl, hgl, hcl⟩ := hc.rsLd st j0 (by unfold Correction.rsChunk; exact .inr hsd)
    rw [List.length_take] at hr
    have hri : r < i := by omega
    rw [take_get hri] at hgl
    rw [take_take_le hri.le] at hcl
    obtain ⟨_, _, _, -, -, -, -, -, hlen⟩ := corr_tld hpre hX ht hw hw' hgl
    refine ⟨r, _, d.o, hri, ⟨pcl, hgl⟩, fun j hj => hcell j (by omega), ?_⟩
    rw [hqi, pArr, pReadyBar_lead, hcl]
  · rintro e ⟨hie, ev, hev, hnt, hnu⟩
    have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
    -- along the rescale: a site of it, or past its wait
    have hR : ∀ m, i + m ≤ e →
        (∃ w pc, i < w ∧ w < i + m ∧ X.get (h, w) = some ⟨pc, .tc .waitSt⟩ ∧
          pArr L X h st.val w = pArr L X h st.val i) ∨
        ∃ dq : Correction.D, Frame.stateAt (code L) X h (i + m) = some (some (.inr (.corr dq))) ∧
          Correction.RsIn st dq ∧ dq.i = d.i ∧ dq.t = d.t := by
      intro m
      induction m with
      | zero => intro _; exact .inr ⟨d, hσ, hrs, rfl, rfl⟩
      | succ m ih =>
        intro hle
        rcases ih (by omega) with ⟨w, pcw, h1, h2, h3, h4⟩ | ⟨dq, hσq, hr, hiq, htq⟩
        · exact .inl ⟨w, pcw, h1, by omega, h3, h4⟩
        -- the event at `i + m`
        have hlen : i + m < (X.tr h).length := by
          have : e < (X.tr h).length := (List.getElem?_eq_some_iff.mp hev).1
          omega
        obtain ⟨eq, heq⟩ : ∃ eq, X.get (h, i + m) = some eq :=
          ⟨_, List.getElem?_eq_getElem hlen⟩
        rcases corr_origin hpre hX ht heq hw hw' (corr_noUb hpre hX hσq heq) with
          ⟨p0, hp0, -⟩ | ⟨dq', t, ins, o, hσq', hcq, -, -, -, -, hevq⟩
        · rw [hσq] at hp0; cases hp0
        rw [hσq] at hσq'
        simp only [Option.some.injEq, Sum.inr.injEq, Role.corr.injEq] at hσq'
        subst hσq'
        have hnx : eq.kind ≠ .exit := by
          intro hx
          obtain ⟨epc, ek⟩ := eq
          simp only at hx
          subst hx
          obtain ⟨d5, hσ5, -, -, hs5⟩ := corr_exit_state hpre hX ht hw hw' heq
          rw [hσq] at hσ5
          simp only [Option.some.injEq, Sum.inr.injEq, Role.corr.injEq] at hσ5
          rw [← hσ5] at hs5
          rcases hr with ⟨_, h5⟩ | ⟨_, h5⟩ | ⟨_, h5⟩ | h5 <;> rw [h5] at hs5 <;> cases hs5
        have hevq' := hevq hnx
        by_cases hw8 : dq.site = .rwait st
        · -- the rescale's wait
          have hk := hevq'.2
          obtain ⟨epc, ek⟩ := eq
          simp only [hw8] at hk
          subst hk
          have him : 0 < m := by
            rcases Nat.eq_zero_or_pos m with h0 | h0
            · subst h0
              rw [Nat.add_zero, hσ] at hσq
              simp only [Option.some.injEq, Sum.inr.injEq, Role.corr.injEq] at hσq
              rw [← hσq, hsd] at hw8
              cases hw8
            · exact h0
          exact .inl ⟨i + m, epc, by omega, by omega, heq, by rw [hq hcq hr hiq htq, hqi]⟩
        · have hsucc := corr_succ heq hσq
          rcases Correction.rs_next hr hw8 hevq' with hn | ⟨d', hn, hr', hi', ht'⟩
          · -- the machine stopped: no followed state after it
            exfalso
            have hnone : Frame.stateAt (code L) X h (i + m + 1) = none := by
              have : Frame.stateAt (code L) X h (i + m + 1) = _ := hsucc
              rw [this, hn]; rfl
            obtain ⟨dz, hz⟩ := Frame.event_state hC hX ht hev
              (fun pc f hf => hnu f (by rw [hf]))
            rw [Frame.stateAt_none_mono hnone (show i + m + 1 ≤ e by omega)] at hz
            cases hz
          · refine .inr ⟨d', ?_, hr', by rw [hi', hiq], by rw [ht', htq]⟩
            have : Frame.stateAt (code L) X h (i + m + 1) = _ := hsucc
            rw [show i + (m + 1) = i + m + 1 by omega, this, hn]
            rfl
    rcases hR (e - i) (by omega) with ⟨w, pcw, h1, h2, h3, h4⟩ | ⟨dq, hσq, hr, -, -⟩
    · exact ⟨w, pcw, h1, by omega, h3, h4⟩
    · -- the event at `e` would be a `tcgen05` event
      exfalso
      rw [show i + (e - i) = e by omega] at hσq
      rcases corr_origin hpre hX ht hev hw hw' (fun pc f hf => hnu f (by rw [hf])) with
        ⟨p0, hp0, -⟩ | ⟨dq', t, ins, o, hσq', -, -, -, -, -, hevq⟩
      · rw [hσq] at hp0; cases hp0
      rw [hσq] at hσq'
      simp only [Option.some.injEq, Sum.inr.injEq, Role.corr.injEq] at hσq'
      subst hσq'
      have hnx : ev.kind ≠ .exit := by
        intro hx
        obtain ⟨epc, ek⟩ := ev
        simp only at hx
        subst hx
        obtain ⟨d5, hσ5, -, -, hs5⟩ := corr_exit_state hpre hX ht hw hw' hev
        rw [hσq] at hσ5
        simp only [Option.some.injEq, Sum.inr.injEq, Role.corr.injEq] at hσ5
        rw [← hσ5] at hs5
        rcases hr with ⟨_, h5⟩ | ⟨_, h5⟩ | ⟨_, h5⟩ | h5 <;> rw [h5] at hs5 <;> cases hs5
      obtain ⟨tk, htk⟩ := Correction.rs_tc hr (hevq hnx)
      exact hnt tk htk

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
