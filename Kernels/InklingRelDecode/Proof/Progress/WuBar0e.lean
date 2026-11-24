-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WuBar1
public import Kernels.InklingRelDecode.Proof.Interface.BarOrdinal

@[expose] public section

/-!
# `BarTime.lag0e`: the two `bar.sync 0` of the common start

A thread with at most `m < 2` barrier-0 events is at a site of the common start (`ordinal_inv`:
`tLb ≤ count`, exact below 2), timed at most `10 (m + 1)`; and so is a thread whose machine
stopped at its last event (a stopped machine is timed one above the state before its last event).
The barrier-0 events of the two sites of the common start are timed at 10 and 20. A thread that
exits has at least two barrier-0 events.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger PTX.Kernels.InklingRelDecode.Proof.BarOrd
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The times of the common start.** A state below two barrier-0 events is timed at most
`10 (tLb + 1)`, and one above `10 (tLb + tInc + 1)` after a step; the sites of `bar.sync 0` are at
`10 (tLb + 1)`. -/
theorem start_time (g : Nat) {s : TSt} (h : tLb s < 2) :
    time g s ≤ 10 * (tLb s + 1) ∧ time g s + 1 ≤ 10 * (tLb s + tInc s + 1) ∧
      (tInc s = 1 → time g s = 10 * (tLb s + 1)) := by
  cases s with
  | d s0 =>
    cases s0 with
    | dstart d =>
      obtain ⟨site, tm⟩ := d
      cases site <;> simp [tLb, tInc, dLb, dInc, time_d, dcompT, dstartT] at h ⊢
    | _ => simp [tLb, dLb] at h
  | w s0 =>
    cases s0 with
    | worker w =>
      obtain ⟨site, P⟩ := w
      cases site <;> simp [tLb, tInc, wLb, wInc, time_w, wcompT, workerT] at h ⊢
    | _ => simp [tLb, wLb] at h

theorem exit_tLb {s : TSt} {g j pc : Nat} (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (htr : Frame.Tracked (code L Q) X)
    (hx : X.get (g, j) = some ⟨pc, .exit⟩) (hσ : St Q L X g j = some (some s)) : tLb s = 2 := by
  rcases exit_event_state hX hS htr hx with ⟨e, hσh, -⟩ | ⟨x, hσh, -⟩
  · rw [hσ] at hσh
    obtain rfl := Option.some.inj (Option.some.inj hσh)
    rfl
  · rw [hσ] at hσh
    obtain rfl := Option.some.inj (Option.some.inj hσh)
    rfl

/-- **`BarTime.lag0e` for `Wt.time`.** -/
theorem bar_lag0e (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (htr : Frame.Tracked (code L Q) X)
    (hub : ¬ HasUb X) {g k pc y : Nat} {d : TSt} (_hg : g < L.threads)
    (hget : X.get (g, k) = some ⟨pc, .bar 0 none .sync⟩)
    (hm : ((X.tr g).take k).countP (Execution.isBarId 0) < 2)
    (hσ : St Q L X g k = some (some d)) (hy : y < L.threads) (_hdiv : y / L.block = g / L.block)
    (hle : (X.tr y).countP (Execution.isBarId 0) ≤ ((X.tr g).take k).countP (Execution.isBarId 0)) :
    (∀ j pc', X.get (y, j) ≠ some ⟨pc', .exit⟩) ∧
      Sched.threadTime (timed Wt.time Q L) X y ≤ Wt.time g d := by
  obtain ⟨hlb, hex⟩ := ordinal_inv hX hS k d (event_le hget) hσ
  have hl2 : tLb d < 2 := by omega
  have hmk := hex hl2
  have hTg : time g d = 10 * (tLb d + 1) := by
    rcases start_event hX hS hget hσ hl2 with ⟨hi, -⟩ | ⟨-, hnb⟩
    · exact (start_time g hl2).2.2 hi
    · exact absurd rfl (hnb 0 none .sync)
  have hnx : ∀ j pc', X.get (y, j) ≠ some ⟨pc', .exit⟩ := by
    intro j pc' hx
    obtain ⟨s, hs⟩ : ∃ s, St Q L X y j = some (some s) :=
      Frame.event_state hS hX htr hx (fun pc f h => by cases h)
    have h1 := exit_tLb hX hS htr hx hs
    obtain ⟨h2, -⟩ := ordinal_inv hX hS j s (event_le hx) hs
    have h3 : ((X.tr y).take j).countP (Execution.isBarId 0) ≤
        (X.tr y).countP (Execution.isBarId 0) :=
      List.Sublist.countP_le (List.take_sublist _ _)
    omega
  refine ⟨hnx, ?_⟩
  rw [threadTime_unfold]
  rcases end_cases hX hS htr hub hy hnx with ⟨s, hσs, hinv⟩ | ⟨s, e, hlen, hσs, hσn, hinv, he⟩
  · rw [hσs]
    simp only
    obtain ⟨h1, -⟩ := ordinal_inv hX hS _ s le_rfl hσs
    have hc : ((X.tr y).take (X.tr y).length).countP (Execution.isBarId 0) =
        (X.tr y).countP (Execution.isBarId 0) := by simp
    rw [hc] at h1
    have h2 : tLb s < 2 := by omega
    have := (start_time y h2).1
    omega
  · rw [hσn]
    simp only
    rw [hσs]
    simp only
    have hk : (X.tr y).length - 1 ≤ (X.tr y).length := by omega
    obtain ⟨h1, h2⟩ := ordinal_inv hX hS _ s hk hσs
    have he' : (X.tr y)[(X.tr y).length - 1]? = some e := he
    have hs1 := countP_succ he'
    rw [Nat.sub_add_cancel hlen, List.take_length] at hs1
    have h3 : tLb s < 2 := by
      by_contra hc
      have : tInc s = 0 := tInc_zero_of hc
      by_cases hbe : Execution.isBarId 0 e = true <;> simp [hbe] at hs1 <;> omega
    have h4 := h2 h3
    have h5 := (start_time y h3).2.1
    rcases start_event hX hS he hσs h3 with ⟨hi, pc1, rfl⟩ | ⟨hi, hnb⟩
    · have hb : Execution.isBarId 0 ⟨pc1, .bar 0 none .sync⟩ = true := by
        simp [Execution.isBarId]
      simp only [hb, ↓reduceIte] at hs1
      omega
    · have hb : Execution.isBarId 0 e = false := by
        obtain ⟨pc, kd⟩ := e
        cases kd <;> simp [Execution.isBarId]
        rename_i id c m
        intro hid
        exact hnb id c m (by simp [hid])
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at hs1
      omega

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
