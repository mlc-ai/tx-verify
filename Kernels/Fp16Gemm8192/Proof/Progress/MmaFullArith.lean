-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # The arithmetic of an MMA thread's full-wait blocker

An MMA thread at its full wait on slot `s` has made `D = 4 u + s` commits, where `u` is its phase.
A loader of its cluster that blocks it has issued (or arrived) fewer than `u + 1` rounds on that
slot's full barrier. Its successful empty polls are fixed by its site (`SiteK`) and by its count
`K`, and its exact counts give `K`'s slot count. The lemmas here bound the loader's next event by
the MMA's block: a loader at a K-loop site has its current block at most `D`, and a loader at a
task-end or drain site has at most `D / 128` tasks. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow

noncomputable section

/-- The ring steps are monotone. -/
theorem ringAt_mono {j k : Nat} (h : j ≤ k) : ringAt j ≤ ringAt k := by
  unfold ringAt blockAt blockSpan
  omega

/-- A task-end block of an earlier task is below every ring step of the MMA's block. -/
theorem blockAt_pred_le {R D : Nat} (h1 : 1 ≤ R) (h : 128 * R ≤ D) :
    blockAt (R - 1) + 4200 ≤ ringAt D := by
  unfold ringAt blockAt blockSpan
  omega

/-- A loader's site against its successful empty polls `K`: the same facts as
`ThreadFacts.loader_site_count`. -/
def SiteK (l : Loader.D) (K : Nat) : Prop :=
  match l.site with
  | .wait b => K % 128 = l.q + b.val ∧ l.q % 8 = 0
  | .load b _ | .arrive b => 0 < K ∧ (K - 1) % 128 = l.q + b.val
  | .clcWait | .clcLoad | .clcStatus | .clcFirst | .clcFence | .ack => 128 ≤ K ∧ K % 128 = 0
  | .drain i => 128 ≤ K ∧ K % 128 = i.val
  | _ => True

/-- A task-end site's time is below the block of its task's end, four thousand blocks in. -/
theorem vtime_clc_le (K : Nat) (d : Loader.D)
    (h : d.site = .clcWait ∨ d.site = .clcLoad ∨ d.site = .clcStatus ∨ d.site = .clcFirst ∨
      d.site = .clcFence ∨ d.site = .ack) :
    Loader.vtime K d ≤ blockAt (K / 128 - 1) + 4180 := by
  obtain ⟨site, m, n, q, cp, resp, x⟩ := d
  rcases h with h | h | h | h | h | h <;> dsimp only at h <;> subst h <;>
    dsimp only [Loader.vtime] <;> omega

/-- At a task-end site with `K` successful empty polls (a multiple of 128) and the MMA's phase `u`,
the loader's count on the slot is short only when its task is before the MMA's. -/
theorem clc_block_le {K D I u : Nat} {s : Fin 4} (hD : D = 4 * u + s.val)
    (hK : 128 ≤ K ∧ K % 128 = 0) (hI : I = 3 * ((K + 3 - s.val) / 4)) (hlt : I < 3 * (u + 1)) :
    blockAt (K / 128 - 1) + 4180 ≤ ringAt D := by
  have hs4 := s.isLt
  have h1 : 1 ≤ K / 128 := by omega
  have h2 : 128 * (K / 128) ≤ D := by omega
  have := blockAt_pred_le h1 h2
  omega

/-- A task-end site's loader, its time at most the block of the MMA's `D`, when its issues on the
slot are short. -/
theorem clc_vtime_of {K D I u : Nat} {d : Loader.D} {s : Fin 4} (hD : D = 4 * u + s.val)
    (hcl : d.site = .clcWait ∨ d.site = .clcLoad ∨ d.site = .clcStatus ∨ d.site = .clcFirst ∨
      d.site = .clcFence ∨ d.site = .ack)
    (hK : 128 ≤ K ∧ K % 128 = 0)
    (hI : I + Loader.remaining d s + 3 * Loader.drained d s = 3 * ((K + 3 - s.val) / 4))
    (hlt : I < 3 * (u + 1)) : Loader.vtime K d ≤ ringAt D + 8 := by
  have h0 : Loader.remaining d s = 0 ∧ Loader.drained d s = 0 := by
    obtain ⟨site, m, n, q, cp, resp, x⟩ := d
    rcases hcl with h | h | h | h | h | h <;> subst h <;> exact ⟨rfl, rfl⟩
  have hI' : I = 3 * ((K + 3 - s.val) / 4) := by
    rw [h0.1, h0.2] at hI
    omega
  have hb := clc_block_le hD hK hI' hlt
  have hv := vtime_clc_le K d hcl
  omega

/-- **A loader's time at its K-loop site, with its issues on the slot short.** A non-exit loader
whose successful empty polls fix its issues (`I + remaining + 3 drained = 3 polls`), with the MMA's
phase `u` and `D = 4 u + s`, is at most one block past the MMA's block `D`. -/
theorem vtime_of_issues {l : Loader.D} {K D I u : Nat} {s : Fin 4} (hD : D = 4 * u + s.val)
    (hdone : l.site.done = false) (hq8 : l.q % 8 = 0) (hK : SiteK l K)
    (hI : I + Loader.remaining l s + 3 * Loader.drained l s = 3 * ((K + 3 - s.val) / 4))
    (hlt : I < 3 * (u + 1)) : Loader.vtime K l ≤ ringAt D + 8 := by
  have hs4 := s.isLt
  obtain ⟨site, m, n, q, cp, resp, x⟩ := l
  cases site with
  | exitArrive => simp [Loader.Site.done] at hdone
  | exitWait => simp [Loader.Site.done] at hdone
  | exit => simp [Loader.Site.done] at hdone
  | wait b =>
    dsimp only [SiteK] at hK
    dsimp only [Loader.remaining, Loader.drained] at hI
    have hKD : K ≤ D := by omega
    have := ringAt_mono hKD
    show ringAt K ≤ ringAt D + 8
    omega
  | load b j =>
    dsimp only [SiteK] at hK
    dsimp only at hq8
    have hj := j.isLt
    have hb := b.isLt
    have hcur : K - 1 ≤ D := by
      by_cases hbs : b.val % 4 = s.val
      · have hslot : InputRing.slotOf b = s := Fin.ext hbs
        dsimp only [Loader.remaining, Loader.drained] at hI
        simp only [hslot, ↓reduceIte] at hI
        omega
      · have hslot : ¬ InputRing.slotOf b = s := fun h => hbs (congrArg Fin.val h)
        dsimp only [Loader.remaining, Loader.drained] at hI
        simp only [hslot, ↓reduceIte] at hI
        omega
    have := ringAt_mono hcur
    show ringAt (K - 1) + 2 + 2 * j.val ≤ ringAt D + 8
    omega
  | arrive b =>
    dsimp only [SiteK] at hK
    dsimp only [Loader.remaining, Loader.drained] at hI
    have hcur : K - 1 ≤ D := by omega
    have := ringAt_mono hcur
    show ringAt (K - 1) + 8 ≤ ringAt D + 8
    omega
  | clcWait =>
    exact clc_vtime_of hD (Or.inl rfl) hK hI hlt
  | clcLoad =>
    exact clc_vtime_of hD (Or.inr (Or.inl rfl)) hK hI hlt
  | clcStatus =>
    exact clc_vtime_of hD (Or.inr (Or.inr (Or.inl rfl))) hK
      hI hlt
  | clcFirst =>
    exact clc_vtime_of hD (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hK hI hlt
  | clcFence =>
    exact clc_vtime_of hD (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      hK hI hlt
  | ack =>
    exact clc_vtime_of hD (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      hK hI hlt
  | drain i =>
    dsimp only [SiteK] at hK
    dsimp only [Loader.remaining, Loader.drained] at hI
    have hi := i.isLt
    have hR : 128 * (K / 128) ≤ D := by
      split_ifs at hI <;> omega
    have hpos : 1 ≤ K / 128 := by omega
    have hb := blockAt_pred_le hpos hR
    show blockAt (K / 128 - 1) + 4190 + 2 * i.val ≤ ringAt D + 8
    omega

/-- The arrival form of `clc_block_le`: the leader's arrivals at a task-end site are its polls. -/
theorem clc_block_le_arr {K D A u : Nat} {s : Fin 4} (hD : D = 4 * u + s.val)
    (hK : 128 ≤ K ∧ K % 128 = 0) (hA : A = (K + 3 - s.val) / 4) (hlt : A < u + 1) :
    blockAt (K / 128 - 1) + 4180 ≤ ringAt D := by
  have hs4 := s.isLt
  have h1 : 1 ≤ K / 128 := by omega
  have h2 : 128 * (K / 128) ≤ D := by omega
  have := blockAt_pred_le h1 h2
  omega

/-- The arrival form of `clc_vtime_of`, at a task-end site. -/
theorem clc_vtime_of_arr {K D A u : Nat} {d : Loader.D} {s : Fin 4} (hD : D = 4 * u + s.val)
    (hcl : d.site = .clcWait ∨ d.site = .clcLoad ∨ d.site = .clcStatus ∨ d.site = .clcFirst ∨
      d.site = .clcFence ∨ d.site = .ack)
    (hK : 128 ≤ K ∧ K % 128 = 0)
    (hA : A + (if Loader.pending d s then 1 else 0) + Loader.drained d s = (K + 3 - s.val) / 4)
    (hlt : A < u + 1) : Loader.vtime K d ≤ ringAt D + 8 := by
  have h0 : (if Loader.pending d s then 1 else 0) = 0 ∧ Loader.drained d s = 0 := by
    obtain ⟨site, m, n, q, cp, resp, x⟩ := d
    rcases hcl with h | h | h | h | h | h <;> subst h <;> exact ⟨rfl, rfl⟩
  have hA' : A = (K + 3 - s.val) / 4 := by
    rw [h0.1, h0.2] at hA
    omega
  have hb := clc_block_le_arr hD hK hA' hlt
  have hv := vtime_clc_le K d hcl
  omega

/-- **A loader's time at its K-loop site, with its arrivals on the slot short.** A leader loader
whose arrivals (with its pending batch and drain) are its successful empty polls, with `A < u + 1`,
is at most one block past the MMA's block `D`. -/
theorem vtime_of_arrivals {l : Loader.D} {K D A u : Nat} {s : Fin 4} (hD : D = 4 * u + s.val)
    (hdone : l.site.done = false) (hq8 : l.q % 8 = 0) (hK : SiteK l K)
    (hA : A + (if Loader.pending l s then 1 else 0) + Loader.drained l s = (K + 3 - s.val) / 4)
    (hlt : A < u + 1) : Loader.vtime K l ≤ ringAt D + 8 := by
  have hs4 := s.isLt
  obtain ⟨site, m, n, q, cp, resp, x⟩ := l
  cases site with
  | exitArrive => simp [Loader.Site.done] at hdone
  | exitWait => simp [Loader.Site.done] at hdone
  | exit => simp [Loader.Site.done] at hdone
  | wait b =>
    dsimp only [SiteK] at hK
    dsimp only [Loader.pending, Loader.drained] at hA
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hA
    have hKD : K ≤ D := by omega
    have := ringAt_mono hKD
    show ringAt K ≤ ringAt D + 8
    omega
  | load b j =>
    dsimp only [SiteK] at hK
    dsimp only at hq8
    have hj := j.isLt
    have hb := b.isLt
    have hcur : K - 1 ≤ D := by
      by_cases hbs : b.val % 4 = s.val
      · have hslot : InputRing.slotOf b = s := Fin.ext hbs
        dsimp only [Loader.pending, Loader.drained] at hA
        simp only [hslot, decide_true, ↓reduceIte] at hA
        omega
      · have hslot : ¬ InputRing.slotOf b = s := fun h => hbs (congrArg Fin.val h)
        dsimp only [Loader.pending, Loader.drained] at hA
        simp only [hslot, decide_false, Bool.false_eq_true, ↓reduceIte] at hA
        omega
    have := ringAt_mono hcur
    show ringAt (K - 1) + 2 + 2 * j.val ≤ ringAt D + 8
    omega
  | arrive b =>
    dsimp only [SiteK] at hK
    dsimp only at hq8
    have hb := b.isLt
    have hcur : K - 1 ≤ D := by
      by_cases hbs : b.val % 4 = s.val
      · have hslot : InputRing.slotOf b = s := Fin.ext hbs
        dsimp only [Loader.pending, Loader.drained] at hA
        simp only [hslot, decide_true, ↓reduceIte] at hA
        omega
      · have hslot : ¬ InputRing.slotOf b = s := fun h => hbs (congrArg Fin.val h)
        dsimp only [Loader.pending, Loader.drained] at hA
        simp only [hslot, decide_false, Bool.false_eq_true, ↓reduceIte] at hA
        omega
    have := ringAt_mono hcur
    show ringAt (K - 1) + 8 ≤ ringAt D + 8
    omega
  | clcWait =>
    exact clc_vtime_of_arr hD (Or.inl rfl) hK hA hlt
  | clcLoad =>
    exact clc_vtime_of_arr hD (Or.inr (Or.inl rfl)) hK hA hlt
  | clcStatus =>
    exact clc_vtime_of_arr hD (Or.inr (Or.inr (Or.inl rfl))) hK
      hA hlt
  | clcFirst =>
    exact clc_vtime_of_arr hD (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      hK hA hlt
  | clcFence =>
    exact clc_vtime_of_arr hD (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      hK hA hlt
  | ack =>
    exact clc_vtime_of_arr hD (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      hK hA hlt
  | drain i =>
    dsimp only [SiteK] at hK
    dsimp only [Loader.pending, Loader.drained] at hA
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hA
    have hi := i.isLt
    have hR : 128 * (K / 128) ≤ D := by
      split_ifs at hA <;> omega
    have hpos : 1 ≤ K / 128 := by omega
    have hb := blockAt_pred_le hpos hR
    show blockAt (K / 128 - 1) + 4190 + 2 * i.val ≤ ringAt D + 8
    omega

end
end PTX.Kernels.Fp16Gemm8192.Proof.Progress
