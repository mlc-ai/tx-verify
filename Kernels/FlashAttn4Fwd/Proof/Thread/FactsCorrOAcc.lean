-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrUb
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrStep
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrTc

@[expose] public section

/-! # A correction load and its wait (`OAccFacts.corr_ld`); no register request after the start

* An event at a correction state is not undefined behaviour: the site's template is not
  (`corr_noUb`, from `corr_tmpl_ok`).
* A correction `tcgen05.ld` is a rescale or final chunk's load of stage `st`'s columns of the
  thread's lane, made after the stage's first O-free arrival; the next state is the chunk's
  implicit wait, so the thread's next event, when there is one, is a `wait::ld`
  (`OAccFacts_corr_ld`).
* The correction machine never returns to its register request (`Cross.NoRegReentry_corr`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Correction

set_option maxHeartbeats 4000000 in
theorem next_ne_setMaxReg {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : next L g d e = some (some d')) : d'.site ≠ .setMaxReg := by
  obtain ⟨site, i, t, aw, a, o⟩ := d
  corr_cases hn
  all_goals simp

end Correction

/-- **The correction part of `Cross.NoRegReentry`.** -/
theorem Cross.NoRegReentry_corr {g : Nat} {d : Correction.D} {r' : Role} {e : Event}
    (h : (code L g).next (.inr (.corr d)) e = some (some (.inr r'))) :
    nextKind (.inr r') ≠ .reg := by
  simp only [code] at h
  rcases hm : Correction.next L g d e with _ | _ | d'
  · rw [hm] at h; cases h
  · rw [hm] at h; cases h
  · rw [hm] at h
    simp only [Option.map_some, Function.comp_apply, Option.some.injEq, Sum.inr.injEq] at h
    subst h
    have hs := Correction.next_ne_setMaxReg hm
    simp only [nextKind]
    cases hd : d'.site <;> simp_all [corrKind]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

omit ht in
/-- An event at a correction state is not undefined behaviour. -/
theorem corr_noUb {g k : Nat} {d : Correction.D} {e : Event}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.corr d))))
    (he : X.get (g, k) = some e) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := Frame.fired_site hC hX he hσ
  intro pc f hef
  subst hef
  exact corr_tmpl_ok hpre hg hi hat hc f (fires_ub hf rfl)

/-- **`OAccFacts.corr_ld`**: a correction load reads stage `st`'s columns of the thread's lane,
after the stage's first O-free arrival, and the thread's next event is the load's wait. -/
theorem OAccFacts_corr_ld {h i a : Nat} {vals : List Value} (_hh : h < L.threads)
    (hw : 8 ≤ warpOf L h) (hw' : warpOf L h < 12) (hld : X.TLd (h, i) a vals .s32x32b) :
    ∃ st < 2, (∀ j < vals.length, InO st (tcDataCell32 L h a j)) ∧
      (i + 1 < (X.tr h).length → ∃ pc, X.get (h, i + 1) = some ⟨pc, .tc .waitLd⟩) ∧
      1 ≤ pArr L X h st i := by
  obtain ⟨pc, he⟩ := hld
  obtain ⟨d, st, j0, hσ, hc, hi, hs, rfl, hl⟩ := corr_tld hpre hX ht hw hw' he
  refine ⟨st.val, st.isLt, fun j hj => ?_, fun hlt => ?_, ?_⟩
  · rw [hl] at hj
    have hcol := tmem_column L h h (256 + 128 * st.val + 16 * j0.val) j (by omega)
    simp only [InO, hcol]
    omega
  · -- the state after the load is the chunk's wait
    have h1 := corr_succ he hσ
    obtain ⟨e', he'⟩ : ∃ e', X.get (h, i + 1) = some e' :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    have hw2 : ∃ d', Frame.stateAt (code L) X h (i + 1) = some (some (.inr (.corr d'))) ∧
        (d'.site = .rldW st j0 ∨ d'.site = .fldW st j0) := by
      have h1' : Frame.stateAt (code L) X h (i + 1) =
          (Correction.next L h d ⟨pc, .tc (.ld _ vals .s32x32b)⟩).map
            (Option.map (.inr ∘ .corr)) := h1
      obtain ⟨site, ii, tt, aw, aa, o⟩ := d
      simp only at hs
      rcases hs with rfl | rfl
      · exact ⟨_, by rw [h1']; rfl, .inl rfl⟩
      · exact ⟨_, by rw [h1']; rfl, .inr rfl⟩
    obtain ⟨d', hσ', hs'⟩ := hw2
    rcases corr_origin hpre hX ht he' hw hw' (corr_noUb hpre hX hσ' he') with
      ⟨p, hp, -⟩ | ⟨d'', t, ins, o, hσ'', -, -, -, -, -, hev⟩
    · rw [hσ'] at hp; cases hp
    rw [hσ'] at hσ''
    simp only [Option.some.injEq, Sum.inr.injEq, Role.corr.injEq] at hσ''
    subst hσ''
    by_cases hx : e'.kind = .exit
    · obtain ⟨epc, ek⟩ := e'
      simp only at hx
      subst hx
      obtain ⟨d3, hσ3, -, -, hs3⟩ := corr_exit_state hpre hX ht hw hw' he'
      rw [hσ'] at hσ3
      simp only [Option.some.injEq, Sum.inr.injEq, Role.corr.injEq] at hσ3
      subst hσ3
      rcases hs' with hs' | hs' <;> rw [hs'] at hs3 <;> cases hs3
    · obtain ⟨hpc, hk⟩ := hev hx
      obtain ⟨epc, ek⟩ := e'
      refine ⟨epc, ?_⟩
      rw [he']
      obtain ⟨site, ii, tt, aw, aa, o⟩ := d'
      simp only at hs' hk
      rcases hs' with rfl | rfl <;> simp only at hk <;> rw [hk]
  · rw [pArr, pReadyBar_lead, hc.free st.val st.isLt]
    obtain ⟨site, ii, tt, aw, aa, o⟩ := d
    simp only at hs
    have hT := corr_trips_pos hpre
    rcases hs with rfl | rfl <;> fin_cases st <;> simp [Correction.freePos] <;> omega

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
