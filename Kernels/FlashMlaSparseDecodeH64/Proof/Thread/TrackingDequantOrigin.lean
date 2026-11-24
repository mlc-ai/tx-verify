-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingConsumerControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingReadGuards
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # The followed first dequantizer read anchors the concrete continuation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def BeforeDequantBody (d : Wg2.D) : Prop :=
  d.block = 0 ∧ (d.site = .lenOrig ∨ d.site = .lenExtra ∨ d.site = .qUtccp ∨
    d.site = .rawReady ∨ d.site = .svDone)

private theorem init_before_dequant_body : BeforeDequantBody (Wg2.init P L g) := by
  unfold BeforeDequantBody Wg2.init Wg2.firstSite
  split_ifs <;> simp

private theorem wg2_origin {q : Machine.ThreadD} {d : Wg2.D} {e : Event}
    (hn : Machine.next P L g q e = some (some (.wg2 d))) :
    d = Wg2.init P L g ∨
      ∃ old, q = .wg2 old ∧ Wg2.next P L g old e = some (some d) := by
  cases q
  case wg2 old =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i new hnext
      cases hn
      exact .inr ⟨old, rfl, hnext⟩
    · split at hn <;> cases hn
    · cases hn
  case prologue p =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          exact .inl rfl
        · cases hn
      · cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

private theorem step_before_dequant_body {d next : Wg2.D} {e : Event}
    (hBefore : BeforeDequantBody d) (hNext : Wg2.next P L g d e = some (some next)) :
    BeforeDequantBody next ∨ (next.site = .scale 0 0 ∧ next.block = 0) := by
  obtain ⟨hBlock, hSite | hSite | hSite | hSite | hSite⟩ := hBefore
  all_goals
    simp only [Wg2.next, Wg2.nextSite, hSite] at hNext
    repeat' split at hNext
  all_goals cases hNext
  all_goals
    simp only [BeforeDequantBody, Wg2.lenOrigNext, Wg2.lenExtraNext, Wg2.init]
    (try split_ifs) <;> simp_all

/-- A followed WG2 state is still before the first scale load or has the first block's
scale load state somewhere in its followed history. -/
private theorem followed_wg2_before_or_at_first_scale {i : Nat} {d : Wg2.D}
    (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d))) :
    BeforeDequantBody d ∨
      ∃ start ≤ i, ∃ initial, initial.site = .scale 0 0 ∧ initial.block = 0 ∧
        Frame.stateAt (Machine.code P L) X g start = some (some (.wg2 initial)) := by
  induction i generalizing d with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ i ih =>
    have hBound : i < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hBound⟩
    obtain ⟨role, hState⟩ := FollowedPrefix.state_at hd (Nat.le_succ _)
    have hNext := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd, hState] at hNext
    rcases wg2_origin hNext.symm with rfl | ⟨old, rfl, hOld⟩
    · exact .inl init_before_dequant_body
    · rcases ih (Nat.le_of_lt hBound) hState with hBefore | ⟨j, hj, initial, hSite, hBlock, hFirst⟩
      · rcases step_before_dequant_body hBefore hOld with h | ⟨hSite, hBlock⟩
        · exact .inl h
        · exact .inr ⟨i + 1, le_rfl, d, hSite, hBlock, hd⟩
      · exact .inr ⟨j, by omega, initial, hSite, hBlock, hFirst⟩

/-- The followed first scale event precedes any dequantizer dismissal. -/
theorem dequant_first_scale_of_dismissal {i : Nat} {d : Wg2.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hDismiss : Machine.next P L g (.wg2 d) e = some none) :
    ∃ start ≤ i, ∃ initial, initial.site = .scale 0 0 ∧ initial.block = 0 ∧
      Frame.stateAt (Machine.code P L) X g start = some (some (.wg2 initial)) := by
  rcases followed_wg2_before_or_at_first_scale (PTX.len_of_get he).le hd with hBefore | h
  · obtain ⟨_, hBad | hBad | hBad | hBad | hBad⟩ := hBefore
    all_goals
      have h := (dequant_dismissal_is_read hpre hX
        (hs g (Frame.lt_of_get hX he)).machine he hd hDismiss).2.1
      simp [hBad] at h
  · exact h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
