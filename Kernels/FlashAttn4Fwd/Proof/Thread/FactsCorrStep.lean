-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrSync
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Time

@[expose] public section

/-! # The correction warps' states after their named-barrier and `tcgen05` events

The times of the correction sites (`Progress.Time.correction`) follow the role's program order:
after a named-barrier event (the start barrier, a statistics sync, the end barrier) the machine is
at a later state (`Cross.barStepUp_corr`); after a warp-collective `tcgen05` event (a chunk's load,
its implicit wait, a rescale store, the rescale's `wait::st`) it is at a later state, or it has
stopped at a load's wait whose chunk the products reject (`Cross.tcStepUp_corr`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

omit hpre hX ht in
/-- The state after a correction event, from the state before it. -/
theorem corr_succ {g j : Nat} {e : Event} {d : Correction.D}
    (he : X.get (g, j) = some e) (hσ : St L X g j = some (some (.inr (.corr d)))) :
    St L X g (j + 1) = (Correction.next L g d e).map (Option.map (.inr ∘ .corr)) := by
  unfold St at hσ ⊢
  rw [Frame.stateAt_succ he, hσ]
  rfl

/-- **`BarStepUp`, correction part**: after a named-barrier event a correction thread is at a later
state. -/
theorem Cross.barStepUp_corr {g j pc id : Nat} {cnt : Option Nat} {m : BarMode} {d : ThreadD}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (he : X.get (g, j) = some ⟨pc, .bar id cnt m⟩) (hσ : St L X g j = some (some d)) :
    ∃ d', St L X g (j + 1) = some (some d') ∧ stateTime L g d < stateTime L g d' := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨dc, t, ins, o, hσ', -, hi, -, -, -, hev⟩
  · cases hk
  have hσ0 : Frame.stateAt (code L) X g j = some (some d) := hσ
  rw [hσ0] at hσ'
  obtain rfl := Option.some.inj (Option.some.inj hσ')
  obtain ⟨-, hk⟩ := hev (by simp)
  have hT := corr_trips_pos hpre
  have hn : Correction.trips L = Work.n L := rfl
  rw [corr_succ he hσ]
  obtain ⟨site, i, tt, aw, a, o'⟩ := dc
  cases site <;> simp at hk
  case bar0 =>
    exact ⟨_, rfl, by simp [stateTime, Progress.Time.correction, Progress.Time.freeT,
      Progress.Time.bar0T]⟩
  case sync st gen =>
    fin_cases st <;> cases gen <;> simp only [Correction.next] <;>
      (try split_ifs) <;>
      exact ⟨_, rfl, by
        simp only [Function.comp, stateTime, Progress.Time.correction, Progress.Time.slotTime,
          Progress.Time.gslot, Progress.Time.bandC, Fin.val_one, Fin.val_zero, Fin.isValue]
        nlinarith⟩
  case barEnd =>
    exact ⟨_, rfl, by simp [stateTime, Progress.Time.correction, Progress.Time.tailTime,
      Progress.Time.slotTime]⟩

/-- **`TcStepUp`, correction part**: after a warp-collective `tcgen05` event a correction thread
is at a later state, or its machine has stopped (at a load's wait whose chunk the products
reject). -/
theorem Cross.tcStepUp_corr {g j k : Nat} {d : ThreadD} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hK : X.TcK (g, j) k) (hσ : St L X g j = some (some d)) :
    (∃ d', St L X g (j + 1) = some (some d') ∧ stateTime L g d < stateTime L g d') ∨
      St L X g (j + 1) = none := by
  obtain ⟨⟨e, he, hp⟩, -⟩ := hK
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by rw [h] at hp; cases hp) with
    ⟨p, -, hk⟩ | ⟨dc, t, ins, o, hσ', -, hi, -, -, -, hev⟩
  · obtain ⟨epc, ek⟩ := e
    cases ek <;> simp only [Prologue.ProKind] at hk <;> simp [isTcColl] at hp
  have hσ0 : Frame.stateAt (code L) X g j = some (some d) := hσ
  rw [hσ0] at hσ'
  obtain rfl := Option.some.inj (Option.some.inj hσ')
  have hne : e.kind ≠ .exit := by
    intro h; obtain ⟨epc, ek⟩ := e; simp only at h; subst h; simp [isTcColl] at hp
  obtain ⟨-, hk⟩ := hev hne
  rw [corr_succ he hσ]
  obtain ⟨epc, ek⟩ := e
  obtain ⟨site, i, tt, aw, a, o'⟩ := dc
  cases site
  case rld st jj =>
    obtain ⟨vals, hk⟩ := hk
    simp only at hk
    subst hk
    exact .inl ⟨_, by simp [Correction.next]; rfl, by
      simp only [stateTime, Progress.Time.correction, Progress.Time.slotTime]; omega⟩
  case fld st jj =>
    obtain ⟨vals, hk⟩ := hk
    simp only at hk
    subst hk
    exact .inl ⟨_, by simp [Correction.next]; rfl, by
      simp only [stateTime, Progress.Time.correction, Progress.Time.slotTime]; omega⟩
  case rldW st jj =>
    simp only [Correction.next]
    split_ifs
    · exact .inl ⟨_, rfl, by
      simp only [Function.comp, stateTime, Progress.Time.correction, Progress.Time.slotTime]; omega⟩
    · exact .inr rfl
  case fldW st jj =>
    simp only [Correction.next]
    split_ifs
    · exact .inl ⟨_, rfl, by
      simp only [Function.comp, stateTime, Progress.Time.correction, Progress.Time.slotTime]; omega⟩
    · exact .inr rfl
  case rst st jj =>
    simp only [Correction.next]
    split_ifs with hj
    · exact .inl ⟨_, rfl, by
      simp only [Function.comp, stateTime, Progress.Time.correction, Progress.Time.slotTime]; omega⟩
    · exact .inl ⟨_, rfl, by
      simp only [Function.comp, stateTime, Progress.Time.correction, Progress.Time.slotTime]; omega⟩
  case rwait st =>
    fin_cases st <;>
      exact .inl ⟨_, rfl, by
        simp only [Function.comp, stateTime, Progress.Time.correction, Progress.Time.slotTime]
        omega⟩
  all_goals exfalso
  all_goals simp only at hk
  all_goals first
    | (subst hk; simp [isTcColl] at hp)
    | (obtain ⟨_, hk⟩ := hk; subst hk; simp [isTcColl] at hp)
    | (obtain ⟨_, _, hk⟩ := hk; subst hk; simp [isTcColl] at hp)
    | (obtain ⟨_, _, _, hk⟩ := hk; subst hk; simp [isTcColl] at hp)
    | (obtain ⟨_, _, hk, -⟩ := hk; subst hk; simp [isTcColl] at hp)

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
