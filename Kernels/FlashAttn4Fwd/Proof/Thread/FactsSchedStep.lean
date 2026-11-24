-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBarW
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrStep

@[expose] public section

/-! # The state after a named-barrier event (`Cross.BarStepUp`)

After a named-barrier event a thread's machine is at a later state, or has stopped:

* the softmax warps: the start barrier moves to the first item's first statistics poll (or the
  tail's), a `gen` to the tile's first store (or the machine stops when the exponent run rejects
  its inputs), the item's last `gen` to the next item's first poll or the tail, the end barrier to
  the exit (`barStepUp_soft`);
* the MMA warp: the start barrier to the base's read-back, the second `bar.sync` to the hand-off
  arrival (`barStepUp_mma`);
* the correction warps: `Cross.barStepUp_corr`;
* no other site is a named barrier (`barIdOf`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The state after a softmax event, from the state before it. -/
theorem soft_succ {g j : Nat} {e : Event} {d : Softmax.D}
    (he : X.get (g, j) = some e) (hσ : St L X g j = some (some (.inr (.softmax d)))) :
    St L X g (j + 1) = (Softmax.next L g d e).map (Option.map (.inr ∘ .softmax)) := by
  unfold St at hσ ⊢
  rw [Frame.stateAt_succ he, hσ]
  rfl

/-- The state after an MMA event, from the state before it. -/
theorem mma_succ {g j : Nat} {e : Event} {d : Mma.D}
    (he : X.get (g, j) = some e) (hσ : St L X g j = some (some (.inr (.mma d)))) :
    St L X g (j + 1) = (Mma.next L g d e).map (Option.map (.inr ∘ .mma)) := by
  unfold St at hσ ⊢
  rw [Frame.stateAt_succ he, hσ]
  rfl

/-- **`BarStepUp`, softmax part.** -/
theorem barStepUp_soft {g j : Nat} {e : Event} {s : Softmax.D} (hi : Softmax.Inv L g s)
    (he : X.get (g, j) = some e) (hσ : St L X g j = some (some (.inr (.softmax s))))
    (hb : (barIdOf L g (.inr (.softmax s))).isSome) :
    (∃ d', St L X g (j + 1) = some (some d') ∧
      stateTime L g (.inr (.softmax s)) < stateTime L g d') ∨ St L X g (j + 1) = none := by
  rw [soft_succ he hσ]
  obtain ⟨site, i, t, w, m, l⟩ := s
  have hitem := hi.item
  simp only at hitem
  have hI : Softmax.items L g = Work.T L g := rfl
  rw [hI] at hitem
  have hb' : ∀ o, o < 600 → bandS (Softmax.stOf L g) + o < span := fun o ho => by
    have := hi.warp; simp only [bandS, span, Softmax.stOf]; omega
  cases site with
  | bar0 =>
    left
    simp only [Softmax.next]
    split_ifs
    · exact ⟨_, rfl, by
        simp only [stateTime, softmax]; exact Progress.Time.fixed_lt (by decide)⟩
    · exact ⟨_, rfl, by
        simp only [stateTime, softmax, tailTime]; exact Progress.Time.fixed_lt (by decide)⟩
  | barEnd =>
    left
    exact ⟨_, rfl, by simp only [stateTime, softmax]; exact Progress.Time.tail_lt (by decide)⟩
  | gen jj =>
    rcases Softmax.fin3_cases jj with rfl | rfl | rfl
    · simp only [Softmax.next]
      split_ifs
      · left
        exact ⟨_, rfl, by
          simp only [stateTime, softmax, Function.comp, softSlot]
          exact Progress.Time.lt_of_off (by simp)⟩
      · right; rfl
    · simp only [Softmax.next]
      split_ifs
      · left
        exact ⟨_, rfl, by
          simp only [stateTime, softmax, Function.comp, softSlot]
          exact Progress.Time.lt_of_off (by simp)⟩
      · right; rfl
    · left
      have hiT : i < Work.T L g := hitem rfl
      simp only [Softmax.next, Softmax.nextItem]
      split_ifs
      · exact ⟨_, rfl, by
          simp only [stateTime, softmax, Function.comp]
          exact Progress.Time.lt_of_item le_rfl (by omega) (hb' _ (by decide))⟩
      · refine ⟨_, rfl, ?_⟩
        simp only [stateTime, softmax, Function.comp]
        exact Progress.Time.lt_tail le_rfl hiT (hb' _ (by decide))
  | _ => simp [barIdOf] at hb

/-- **`BarStepUp`, MMA part.** -/
theorem barStepUp_mma {g j : Nat} {e : Event} {m : Mma.D}
    (he : X.get (g, j) = some e) (hσ : St L X g j = some (some (.inr (.mma m))))
    (hb : (barIdOf L g (.inr (.mma m))).isSome) :
    ∃ d', St L X g (j + 1) = some (some d') ∧
      stateTime L g (.inr (.mma m)) < stateTime L g d' := by
  rw [mma_succ he hσ]
  obtain ⟨site, i, t, b, pro⟩ := m
  cases site with
  | bar0 => exact ⟨_, rfl, by simp only [stateTime, mma, Function.comp]; decide⟩
  | bar1 =>
    exact ⟨_, rfl, by
      simp only [stateTime, mma, mmaTail, Function.comp]; exact Progress.Time.tail_lt (by decide)⟩
  | _ => simp [barIdOf] at hb

/-- **`TcStepUp`, MMA part**: after an allocation, relinquishment or deallocation. -/
theorem tcStepUp_mma {g j : Nat} {e : Event} {m : Mma.D}
    (he : X.get (g, j) = some e) (hσ : St L X g j = some (some (.inr (.mma m))))
    (hk : mmaKind m.site = .tmem) :
    ∃ d', St L X g (j + 1) = some (some d') ∧
      stateTime L g (.inr (.mma m)) < stateTime L g d' := by
  rw [mma_succ he hσ]
  obtain ⟨site, i, t, b, pro⟩ := m
  cases site <;> simp only [mmaKind, reduceCtorEq] at hk
  · simp only [Mma.next]
    split_ifs
    · exact ⟨_, rfl, by simp only [stateTime, mma, Function.comp]; decide⟩
    · exact ⟨_, rfl, by simp only [stateTime, mma, Function.comp]; decide⟩
  · exact ⟨_, rfl, by
      simp only [stateTime, mma, mmaTail, Function.comp]; exact Progress.Time.tail_lt (by decide)⟩
  · exact ⟨_, rfl, by
      simp only [stateTime, mma, mmaTail, Function.comp]; exact Progress.Time.tail_lt (by decide)⟩

/-- **`TcStepUp`, softmax part**: after a load, its wait, a store or a store wait; the machine
stops at a load's wait whose words it rejects. -/
theorem tcStepUp_soft {g j : Nat} {e : Event} {s : Softmax.D}
    (he : X.get (g, j) = some e) (hσ : St L X g j = some (some (.inr (.softmax s))))
    (hev : Softmax.Ev L g s e) (hk : tcKind (softmaxKind s.site) = true) :
    (∃ d', St L X g (j + 1) = some (some d') ∧
      stateTime L g (.inr (.softmax s)) < stateTime L g d') ∨ St L X g (j + 1) = none := by
  rw [soft_succ he hσ]
  obtain ⟨site, i, t, w, m, l⟩ := s
  cases site with
  | ld lp c =>
    obtain ⟨vals, hv⟩ := hev
    left
    simp only [Softmax.next, hv]
    exact ⟨_, rfl, by
      simp only [stateTime, softmax, Function.comp]; exact Progress.Time.lt_of_off (by omega)⟩
  | ldW lp c =>
    simp only [Softmax.next]
    split_ifs
    · left
      rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl
      all_goals (try cases lp)
      all_goals exact ⟨_, rfl, by
        simp only [stateTime, softmax, Function.comp, Softmax.afterLoad, softSlot]
        exact Progress.Time.lt_of_off (by simp)⟩
    · right; rfl
  | pst lp c =>
    left
    rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl
    all_goals exact ⟨_, rfl, by
      simp only [stateTime, softmax, Function.comp]; exact Progress.Time.lt_of_off (by simp)⟩
  | pwait lp h =>
    left
    rcases Softmax.fin2_cases h with rfl | rfl
    all_goals exact ⟨_, rfl, by
      simp only [stateTime, softmax, Function.comp]; exact Progress.Time.lt_of_off (by simp)⟩
  | _ => simp [softmaxKind, tcKind] at hk

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

/-- **`Cross.TcStepUp`.** -/
theorem tcStepUp : TcStepUp L X := by
  intro g j k d hg hK hσ
  obtain ⟨⟨e, he, hp⟩, -⟩ := hK
  have hj : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hkind := (fired_kind hpre hX hok hg hσ he).2.1
  rw [hp] at hkind
  obtain ⟨-, hinv, hw⟩ := state_facts hpre hX ht hok hg hj.le hσ
  rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', s, rfl⟩ | ⟨hw', l, rfl⟩ | ⟨hw', m, rfl⟩ |
      ⟨hw', s, rfl⟩ | ⟨hw', s, rfl⟩ | ⟨hw', hw'', c, rfl⟩
  · rw [prologue_tcKind p] at hkind; cases hkind
  · obtain ⟨site⟩ := s; cases site <;> simp [nextKind, idleKind, tcKind] at hkind
  · cases hs : l.site <;> simp [nextKind, loaderKind, tcKind, hs] at hkind
  · refine .inl (tcStepUp_mma he hσ ?_)
    have := mma_tcKind m.site
    simp only [nextKind] at hkind
    rw [this] at hkind
    exact beq_iff_eq.mp hkind.symm
  · cases hs : s.site <;> simp [nextKind, storeKind, tcKind, hs] at hkind
  · rcases soft_origin hpre hX ht he hw' (not_ub hpre hX ht hok hg hσ he) with
      ⟨p, hp', -⟩ | ⟨s', t, ins, o, hs', -, -, -, -, -, hev⟩
    · have hp'' : St L X g j = some (some (.inl p)) := hp'
      rw [hσ] at hp''; cases hp''
    have hs'' : St L X g j = some (some (.inr (.softmax s'))) := hs'
    rw [hσ] at hs''
    cases hs''
    exact tcStepUp_soft he hσ hev hkind.symm
  · exact Cross.tcStepUp_corr hpre hX ht hw' hw'' ⟨⟨e, he, hp⟩, rfl⟩ hσ

/-- **`Cross.BarStepUp`.** -/
theorem barStepUp : BarStepUp L X := by
  intro g j pc id cnt md d hg he hσ
  have hid := bar_site hpre hX ht hok hg he hσ
  have hj : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨-, hinv, hw⟩ := state_facts hpre hX ht hok hg hj.le hσ
  rcases role_cases hw with ⟨p, rfl⟩ | ⟨hw', s, rfl⟩ | ⟨hw', l, rfl⟩ | ⟨hw', m, rfl⟩ |
      ⟨hw', s, rfl⟩ | ⟨hw', s, rfl⟩ | ⟨hw', hw'', c, rfl⟩
  · simp [barIdOf] at hid
  · simp [barIdOf] at hid
  · simp [barIdOf] at hid
  · exact .inl (barStepUp_mma he hσ (by rw [hid]; rfl))
  · simp [barIdOf] at hid
  · exact barStepUp_soft hinv he hσ (by rw [hid]; rfl)
  · exact .inl (Cross.barStepUp_corr hpre hX ht hw' hw'' he hσ)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
