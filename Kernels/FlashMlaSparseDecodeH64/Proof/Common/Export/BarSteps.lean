-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.BarGroup
public import Lemmas.Quiet.Progress.BarGroupU
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Bar12
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.BarLag0
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep

@[expose] public section

/-! # Progress at a named barrier

A pending lane blocked at a `bar.sync` steps (`bar_steps`, by `Sched.barGroup_sync_stepsUQ`) once
every barrier has its participant group (`hgroup`, the statement of `Protocol/Bar/Group.lean`'s
`bar_group`, the warps `barIn id`). The time table's two facts are taken privately here:

* after a barrier event the lane's state is later (`bar_after`): the startup's barrier 0 (time
  `99`) enters a warpgroup (time at least `100`), warpgroup 0's barriers raise its place
  (`Wg0.place_next`), barrier 12 of warps 4–11 is followed by the exit (`bar12_after`);
* the lag (`bar_lag`): a participant with no more events on the barrier than the lane before its
  event has not exited and is no later. Barrier 0: `bar0_at`, `bar0_lag`; barriers 9–11 and 12
  among warps 0–3: `w0_lagId`; barrier 12 otherwise: the lane is at `endSlot` with no earlier
  barrier-12 event (`w0_end`, `bar12_at`) and a lane without one is no later than `endSlot`
  (`w0_noBar12`, `bar12_lag`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g y : Nat}

private theorem w0IdCnt_end {R p B : Nat} (hp : p < 2) (h : B ≤ 3 * R + 6) :
    w0IdCnt R p 12 B = 0 := by
  unfold w0IdCnt
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro o ho
  simp only [List.mem_range] at ho
  unfold Wg0.idAt
  split_ifs <;> simp <;> omega

private theorem barPlace_end (R : Nat) : wg0Org + Wg0.barPlace R (3 * R + 6) = endSlot := by
  have h1 : ¬ 3 * R + 6 < 3 * R := by omega
  have h2 : 3 * R + 6 ≠ 3 * R := by omega
  have h3 : 3 * R + 6 ≠ 3 * R + 1 := by omega
  have h4 : ¬ 3 * R + 6 < 3 * R + 6 := by omega
  unfold Wg0.barPlace
  simp only [h1, h2, h3, h4, ↓reduceIte]
  have : wg0Org ≤ endSlot := by decide
  unfold Wg0.endPlace
  omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hnu : ¬ HasUb X)
include hp hX hFw hnu

/-- A barrier-12 event of warps 0–3 is at `endSlot`, with none before it. -/
private theorem w0_end (hw : warp L g < 4) {j pc : Nat} {c : Option Nat} {md : BarMode}
    {σ : (thread P L g).D} (he : X.get (g, j) = some ⟨pc, .bar 12 c md⟩) (h103 : 103 ≤ pc)
    (hσ : Frame.stateAt (thread P L) X g j = some (some σ)) :
    time P L g σ = endSlot ∧ ((X.tr g).take j).countP (Execution.isBarId 12) = 0 := by
  obtain ⟨ht, hB, hI⟩ := w0_atBar hp hX hFw hw he h103 hσ
  have hB' : w0BarCnt X g j = 3 * blocksOf P L (g / L.block) + 6 := by
    unfold Wg0.idAt at hI
    split_ifs at hI <;> omega
  refine ⟨by rw [ht, hB', barPlace_end], ?_⟩
  rw [w0_idCnt hp hX hFw hw (by omega) (Nat.le_refl _) j hnu, hB']
  exact w0IdCnt_end (Nat.mod_lt _ (by omega)) (Nat.le_refl _)

/-- A lane of warps 0–3 without a barrier-12 event is no later than `endSlot`. -/
private theorem w0_noBar12 (hw : warp L y < 4) (hy : y < L.threads)
    (h0 : (X.tr y).countP (Execution.isBarId 12) = 0) :
    (∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (timed P L) X y ≤ endSlot := by
  have hc := w0_idCnt hp hX hFw hw (by omega) (Nat.le_refl 12) (X.tr y).length hnu
  rw [List.take_length, h0] at hc
  have hle : w0BarCnt X y (X.tr y).length ≤ 3 * blocksOf P L (y / L.block) + 6 := by
    by_contra hlt
    have h1 := w0IdCnt_mono (R := blocksOf P L (y / L.block)) (p := warp L y % 2) (id := 12)
      (show 3 * blocksOf P L (y / L.block) + 6 + 1 ≤ w0BarCnt X y (X.tr y).length by omega)
    rw [w0IdCnt_succ, w0IdCnt_end (Nat.mod_lt _ (by omega)) (Nat.le_refl _)] at h1
    simp [Wg0.idAt] at h1
    omega
  obtain ⟨hx, ht⟩ := w0_lagB hp hX hFw hw hy (Nat.le_refl _) hle (noUbBefore_of_noUb hnu)
  exact ⟨hx, by rw [barPlace_end] at ht; exact ht⟩

end

/-- A state after a barrier-0 event is at time at least `100`. -/
private theorem after_bar0 (hFw : Follow P L X) (hg : g < L.threads) {i : Nat}
    {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g i = some (some σ))
    (hc : 0 < ((X.tr g).take i).countP isBar0) : 100 ≤ time P L g σ := by
  have hJ := (follow_iff.mp hFw g hg i).2 σ hσ
  have hn := state_count hσ .bar0
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨i | r, d⟩
  · have hx : Startup.exitOf d = none := by simpa [startupEnter] using glue_gate hσ
    obtain ⟨hR, -, -⟩ := hJ
    have h0 : n .bar0 = 0 := by
      obtain ⟨site, x1, x2⟩ := d
      cases site <;> simp only [Startup.Ref] at hR <;> first | exact hR.2 |
        simp [Startup.exitOf] at hx
    simp only [cls] at hn
    omega
  · cases i with
    | wg0 => simp only [time, fragTime, wg0Time, roleBase]; omega
    | dequant => simp only [time, fragTime, dequantTime, idleBase, roleBase]; omega
    | wg1 =>
      rcases d with s | ⟨j | r, d⟩
      · simp only [time, fragTime, wg1Time, roleBase]; omega
      · cases j
        case idle =>
          cases d <;> simp only [time, fragTime, wg1Time, idleTime, Wg1.itime, idleBase,
            roleBase, endSlot, loopBase, stride, blockCap] <;> omega
        all_goals simp only [time, fragTime, wg1Time, mmaTime, tmaTime, indexTime, idleBase,
          roleBase]; omega
      · simp [time, fragTime, wg1Time, idleBase, roleBase]
  · simp [time, roleBase]

/-- A barrier event of warpgroup 0 raises the lane's place. -/
private theorem w0_after (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hg : g < L.threads) (hw : warp L g < 4) {j pc id : Nat}
    {c : Option Nat} {md : BarMode} {σ σ' : (thread P L g).D}
    (he : X.get (g, j) = some ⟨pc, .bar id c md⟩) (h103 : 103 ≤ pc)
    (hσ : Frame.stateAt (thread P L) X g j = some (some σ))
    (hσ' : Frame.stateAt (thread P L) X g (j + 1) = some (some σ')) :
    time P L g σ < time P L g σ' := by
  obtain ⟨σm, hσm, hn⟩ := prev_state he hσ'
  rw [hσ] at hσm
  cases hσm
  rcases w0_bst hFw hnu hw hg hσ with ⟨d, n, rfl, -⟩ | ⟨d, n, rfl, hC, -, -⟩
  · obtain ⟨σ0, hσ0, -, hi, -, hpc⟩ := ev_at hp hX hFw he (noUb_kind hnu he)
    rw [hσ] at hσ0
    cases hσ0
    have h2 : (⟨pc, .bar id c md⟩ : Event).pc ≤ 97 := by rw [hpc]; exact startup_pc hi
    simp only at h2
    omega
  · rw [next_frag] at hn
    obtain ⟨d', hs, rfl⟩ := map_some hn
    have hs' : Proof.Wg0.Control.succ P L g (warpW L g) d ⟨pc, .bar id c md⟩ = some (some d') := hs
    rcases Wg0.place_next hC hs' with ⟨-, hk⟩ | hlt
    · simp [Event.counts] at hk
    · simp only [time, fragTime, wg0Time, Wg0.time]
      omega


section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hnu : ¬ HasUb X) (hR : BarRows P L X)
include hp hX hFw hnu hR

/-- **After a barrier event the lane's state is later**, or the lane has no state after it. -/
private theorem bar_after (hg : g < L.threads) {j pc id : Nat} {c : Option Nat} {md : BarMode}
    {σ : (thread P L g).D} (he : X.get (g, j) = some ⟨pc, .bar id c md⟩)
    (hσ : Frame.stateAt (thread P L) X g j = some (some σ)) :
    (∃ σ', Frame.stateAt (thread P L) X g (j + 1) = some (some σ') ∧
      time P L g σ < time P L g σ') ∨ Frame.stateAt (thread P L) X g (j + 1) = none := by
  rcases h1 : Frame.stateAt (thread P L) X g (j + 1) with _ | _ | σ'
  · exact .inr rfl
  · exact absurd h1 ((follow_iff.mp hFw g hg (j + 1)).1)
  refine .inl ⟨σ', rfl, ?_⟩
  rcases bar_use hR hg he rfl with ⟨-, -, h⟩ | ⟨⟨hw, h103, -⟩, -⟩ | ⟨⟨hw, -⟩, -, h⟩ |
    ⟨⟨hw, -⟩, -, h⟩ | ⟨⟨hw, -⟩, -, h⟩ | ⟨⟨hw, -⟩, -, h⟩ | ⟨⟨hw, -⟩, -, h⟩
  · simp only [BarRow.Cta, Kind.bar.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have ht := (bar0_at hp hX hFw hR he hσ).1
    have hc : 0 < ((X.tr g).take (j + 1)).countP isBar0 := by
      have he' : (X.tr g)[j]? = some ⟨pc, .bar 0 none .sync⟩ := he
      rw [List.take_add_one, he', Option.toList_some, List.countP_append]
      simp [isBar0_barId, Execution.isBarId]
    have := after_bar0 hFw hg h1 hc
    omega
  · exact w0_after hp hX hFw hnu hg hw he h103 hσ h1
  all_goals
    simp only [Kind.bar.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact bar12_after hp hX hFw hnu (by omega) hg he hσ h1

/-- **The lag at a barrier**: a participant with no more events on the barrier than the lane
before its event has not exited and is no later. -/
private theorem bar_lag (hg : g < L.threads) (hy : y < L.threads)
    (hc : y / L.block = g / L.block) {j pc id : Nat} {cnt : Option Nat} {σ : (thread P L g).D}
    (hG : barIn id (warp L y) = true) (he : X.get (g, j) = some ⟨pc, .bar id cnt .sync⟩)
    (hσ : Frame.stateAt (thread P L) X g j = some (some σ))
    (hle : (X.tr y).countP (Execution.isBarId id) ≤
      ((X.tr g).take j).countP (Execution.isBarId id)) :
    (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧
      Sched.threadTime (timed P L) X y ≤ time P L g σ := by
  have h12 : ∀ t, t = endSlot →
      (X.tr y).countP (Execution.isBarId 12) = 0 →
      (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ Sched.threadTime (timed P L) X y ≤ t := by
    rintro t rfl h0
    by_cases hwy : warp L y < 4
    · exact w0_noBar12 hp hX hFw hnu hwy hy h0
    · exact bar12_lag hp hX hFw hnu (by omega) hy h0
  rcases bar_use hR hg he rfl with ⟨-, -, h⟩ | ⟨⟨hw, h103, -⟩, -⟩ | ⟨⟨hw, -⟩, -, h⟩ |
    ⟨⟨hw, -⟩, -, h⟩ | ⟨⟨hw, -⟩, -, h⟩ | ⟨⟨hw, -⟩, -, h⟩ | ⟨⟨hw, -⟩, -, h⟩
  · simp only [BarRow.Cta, Kind.bar.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    obtain ⟨ht, h0⟩ := bar0_at hp hX hFw hR he hσ
    rw [h0] at hle
    obtain ⟨hx, hle'⟩ := bar0_lag hp hX hFw hnu hy (by omega)
    exact ⟨hx, by rw [ht]; exact hle'⟩
  · obtain ⟨-, -, hI⟩ := w0_atBar hp hX hFw hw he h103 hσ
    have hp2 : warp L g % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases hwy : warp L y < 4
    · refine w0_lagId hp hX hFw (noUbBefore_of_noUb hnu) hy hc hw hwy ?_ he h103 hσ hle
      unfold Wg0.idAt at hI
      unfold barIn at hG
      split_ifs at hI hG <;> simp at hG <;> omega
    · have hid : id = 12 := by
        unfold Wg0.idAt at hI
        unfold barIn at hG
        split_ifs at hI hG <;> simp at hG <;> omega
      subst hid
      obtain ⟨ht, h0⟩ := w0_end hp hX hFw hnu hw he h103 hσ
      rw [h0] at hle
      exact h12 _ ht (by omega)
  all_goals
    simp only [Kind.bar.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    obtain ⟨ht, h0⟩ := bar12_at hp hX hFw hnu (by omega) he hσ
    rw [h0] at hle
    exact h12 _ ht (by omega)

end

/-- The warp of a lane is its CTA-local warp index. -/
private theorem warp_eq (hp : Pre P L m) (y : Nat) : warp L y = y % L.block / 32 := by
  simp only [warp, tidOf_x_eq hp, hp.block]

/-- **A lane blocked at a `bar.sync` steps**, given every barrier's participant group
(`Protocol/Bar/Group.lean`, `bar_group`). -/
theorem bar_steps (hp : Pre P L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hFw : Follow P L X) (hR : BarRows P L X)
    (hgroup : ∀ {g i pc id : Nat} {cnt : Option Nat} {md : BarMode}, g < L.threads →
      X.get (g, i) = some ⟨pc, .bar id cnt md⟩ →
      ∃ q : Finset Nat, NamedBar.Shape L cnt q id ∧ NamedBar.Sources L X cnt q id ∧
        ∀ w ∈ q, barIn id w = true)
    {g : Nat} (hpd : Frame.Pending L X g) (hrel : ¬ Step.Released L X g)
    (hw : Sched.BarWait L X g) : Sched.Steps (timed P L) m X (.thread g) := by
  have hX := hmax.1
  have hnu := Sched.safe_noUb (hs.2 X hX)
  rw [timed_eq]
  exact Sched.barGroup_sync_stepsUQ (M := ⟨thread P L, time P L⟩) wfQuiet_all
    (fun _ _ => thread_sound hp) hs hgroup
    (fun hg he hσ => bar_after hp hX hFw hnu hR hg he hσ)
    (fun hg hy hc hG he hσ hle => by
      have h := bar_lag hp hX hFw hnu hR hg hy hc (by rw [warp_eq hp]; exact hG) he hσ hle
      rw [timed_eq] at h
      exact h)
    (fun h k hh => (follow_iff.mp hFw h hh k).1) hmax hpd hrel hw

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
