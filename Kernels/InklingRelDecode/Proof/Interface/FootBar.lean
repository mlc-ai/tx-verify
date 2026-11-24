-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.FootExist
public import Kernels.InklingRelDecode.Proof.Interface.FootTrack
public import Kernels.InklingRelDecode.Proof.Protocol.BarOne

@[expose] public section

/-!
# Barrier 1 along the threads of a CTA: arrivals, and the state at an arrival

* `arrival1_before`, `before_lt1`: the barrier-1 arrival of ordinal `r` of a thread whose count
  before an event is above `r`, and an event with at most `φ` earlier barrier-1 events is before
  the arrival of ordinal `φ` (the barrier-1 form of `Bar.arrival_before`, `Bar.before_lt`).
* `Bar1Exits`: **the premise on exits** that `Bar.bar1_member` takes as `hexited`, for every
  passed arrival: a thread that exits has made the arrivals the other threads of its CTA passed.
  The kernel's default-partition threads and its workers exit after at least four barrier-1
  events. It is proved for every consistent execution from `Consistent.dependency` by
  `Proof2.bar1Exits` (`Proof2/Safety/Bar1Exit.lean`), without `RoleReads`.
* `phase0_bar18`, `phase3_bar2`: the state of a default-partition thread at its barrier-1 arrival
  of ordinal 0 (3) is the prologue's `bar18` (the epilogue's `bar2`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem take_count1_lt {l : List Event} {j k : Nat} {e : Event} (hj : l[j]? = some e)
    (hq : Execution.isBarId 1 e = true) (hjk : j < k) :
    (l.take j).countP (Execution.isBarId 1) + 1 ≤ (l.take k).countP (Execution.isBarId 1) := by
  have h1 := countP_take_succ (Execution.isBarId 1) hj
  simp only [hq, ↓reduceIte] at h1
  have h2 := (List.take_sublist_take_left (l := l) (show j + 1 ≤ k by omega)).countP_le
    (p := Execution.isBarId 1)
  omega

/-- **A non-barrier event whose prefix has at most `φ` barrier-1 events is before every barrier-1
event of ordinal `φ`.** -/
theorem before_lt1 {l : List Event} {φ before i : Nat} {ev e : Event}
    (hc : (l.take before).countP (Execution.isBarId 1) ≤ φ) (hbev : l[before]? = some ev)
    (hnb : ¬ Execution.isBarId 1 ev = true) (hi : l[i]? = some e)
    (hq : Execution.isBarId 1 e = true) (hord : (l.take i).countP (Execution.isBarId 1) = φ) :
    before < i := by
  by_contra hle
  rcases Nat.lt_or_eq_of_le (Nat.not_lt.mp hle) with hlt | heq
  · have := take_count1_lt hi hq hlt
    omega
  · subst heq
    rw [hi] at hbev
    cases hbev
    exact hnb hq

/-- **The arrival of ordinal `r` of a thread whose barrier-1 count before an event exceeds
`r`.** -/
theorem arrival1_before (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) {h k r : Nat}
    (hr : r < b1N X h k) :
    ∃ j pc, j < k ∧ X.IsBarrier (h, j) 1 none pc ∧
      ((X.tr h).take j).countP (Execution.isBarId 1) = r := by
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  obtain ⟨j, e, hj, hq, hcnt⟩ := NamedBar.exists_ordinal (Execution.isBarId 1) _ hr
  rw [List.getElem?_take] at hj
  split at hj
  · rename_i hjk
    obtain ⟨pc, cnt, m, rfl⟩ := NamedBar.isBarId_form hq
    rw [List.take_take, Nat.min_eq_left (by omega)] at hcnt
    have hget : X.get (h, j) = some ⟨pc, .bar 1 cnt m⟩ := hj
    obtain ⟨hnone, hm⟩ := bar_one_static hX hb hget
    subst hnone hm
    exact ⟨j, pc, hjk, hget, hcnt⟩
  · cases hj

/-- **A thread that exits has made the barrier-1 arrivals the threads of its CTA passed.** -/
def Bar1Exits (L : Launch) (X : Execution) : Prop :=
  ∀ {f : EvId} {pc g : Nat}, X.IsBarrier f 1 none pc → f.2 + 1 < (X.tr f.1).length →
    g / L.block = f.1 / L.block → (∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩) →
      ∃ i pc', X.IsBarrier (g, i) 1 none pc' ∧
        ((X.tr g).take i).countP (Execution.isBarId 1) =
          ((X.tr f.1).take f.2).countP (Execution.isBarId 1)

/-- **Every thread of the CTA has the barrier-1 arrival a passed thread passed.** -/
theorem bar1_has (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hE : Bar1Exits L X)
    {g h j pc : Nat} (hf : X.IsBarrier (h, j) 1 none pc) (hp : j + 1 < (X.tr h).length)
    (hcta : g / L.block = h / L.block) :
    ∃ i pc', X.IsBarrier (g, i) 1 none pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId 1) = ((X.tr h).take j).countP
        (Execution.isBarId 1) :=
  Bar.bar1_member hpre hX hf hp hcta (hE hf hp hcta)

theorem dB1_phase0 {d : DComp.St} (h0 : (dPh d).2 = 0) (hb : dB1 d = true) :
    ∃ dd : ProA.D, d = .pro dd ∧ dd.site = .bar18 := by
  cases d with
  | dstart d => simp [dB1] at hb
  | pro d =>
    refine ⟨d, rfl, ?_⟩
    obtain ⟨site, dt⟩ := d
    cases site <;> simp [dB1, proB1] at hb ⊢
  | sm d =>
    exfalso
    revert h0
    simp only [dPh]
    split <;> simp
  | epi d =>
    exfalso
    revert h0
    simp only [dPh]
    split <;> simp

theorem dB1_phase3 {d : DComp.St} (h3 : (dPh d).2 = 3) (hb : dB1 d = true) :
    ∃ dd : Epi.D, d = .epi dd ∧ dd.site = .bar2 := by
  cases d with
  | dstart d => simp [dPh] at h3
  | pro d =>
    exfalso
    revert h3
    simp only [dPh]
    split <;> simp
  | sm d =>
    exfalso
    revert h3
    simp only [dPh]
    split <;> simp
  | epi d =>
    refine ⟨d, rfl, ?_⟩
    revert h3 hb
    simp only [dPh, dB1, epiB1]
    cases hs : d.site <;> simp

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
