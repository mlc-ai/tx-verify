-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LpProRank

@[expose] public section

/-!
# The prologue's arrival and copy sites: who passes them, and for which blocks

* `tid_of_p177`: the guard of `arr j` (`v_p177`) holds only for thread 0 of the CTA;
* `tid_of_p59`: the predicate of the copies (`v_p59`) holds only for warps 0 and 1;
* `numPre_of_gate`: a site of block `b` that passed the gate (`Gate`) is of a block below
  `num_pre` (the converse direction of `gate_of_numPre`);
* `next_into_ptc`: the step into a copy site is the election before it, which returned the
  thread's lane, with `v_p59`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

theorem p177_tab : ∀ t < 128,
    pEqB32 (wAnd32 (BitVec.ofNat 64 t) (BitVec.ofInt 64 127)) (BitVec.ofInt 64 0) =
      decide (t = 0) := by
  decide +kernel

theorem tid_of_p177 {L : Launch} {g : Nat} {dt : Dat} (ht : tidOf L g < 128)
    (h : v_p177 L g dt = true) : tidOf L g = 0 := by
  have := p177_tab (tidOf L g) ht
  simp only [v_p177, v_r27, v_r1] at h
  rw [this] at h
  simpa using h

theorem tid_of_p59 {L : Launch} {g : Nat} {dt : Dat} (ht : tidOf L g < 128)
    (h : v_p59 L g dt = true) : tidOf L g < 64 := by
  have := p59_tab (tidOf L g) ht
  simp only [v_p59, v_r27, v_r1] at h
  rw [this] at h
  simpa using h

theorem arr_blk : ∀ j < 3, arrSite j ∈ blkSites j := by decide

theorem ptc_blk : ∀ j < 12, ptcSite j ∈ blkSites (j / 4) := by decide

/-- **A site of block `b` that passed the gate is of a block below `num_pre`.** -/
theorem numPre_of_gate {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) {g : Nat}
    (hg : g < L.threads) {dt : Dat} (ha : ArgsOk L g dt.pro) (hs : dt.pro.w71 = P.splits)
    (hm : WordsMatch P (cta L g .z) dt) {s : Site} (hG : Gate L g s dt) {b : Nat}
    (hb : s ∈ blkSites b) : b < numPre P (cta L g .z) (cta L g .x) := by
  have hw := wordsOk_of_pre hpre hg ha hs hm
  have hx := (cta_lt hpre hg).1
  have h31 := v_r31_val L g dt ha hw
  have hit := itersN_eq hs hx hm
  have hol := oldN_eq hs hx hm
  have hl1 := itersN_lt L g dt ha hw
  have hmin : min (oldN L g dt) (itersN L g dt) < 2 ^ 31 :=
    lt_of_le_of_lt (Nat.min_le_right _ _) hl1
  obtain ⟨g0, g1, g2⟩ := hG
  unfold numPre
  rw [← hit, ← hol]
  match b, hb with
  | 0, hb =>
    have h := g0 hb
    simp only [v_p53, h31, pNe0 _ hmin, decide_eq_true_eq] at h
    omega
  | 1, hb =>
    obtain ⟨h, h'⟩ := g1 hb
    simp only [v_p53, v_p63, h31, pNe0 _ hmin, pEq1 _ hmin, decide_eq_true_eq,
      decide_eq_false_iff_not] at h h'
    omega
  | 2, hb =>
    obtain ⟨h, h', h''⟩ := g2 hb
    simp only [v_p53, v_p63, v_p72, h31, pNe0 _ hmin, pEq1 _ hmin, pLt3 _ hmin,
      decide_eq_true_eq, decide_eq_false_iff_not] at h h' h''
    omega
  | b + 3, hb => simp [blkSites] at hb

theorem qSite_not_ptc (L : Launch) (g : Nat) (dt : Dat) (n : Nat) :
    qSite L g dt n ∉ ptcSites := by
  unfold qSite
  split <;> (repeat' split) <;> decide

theorem p59_el {L : Launch} {g : Nat} (dt : Dat) (f : Nat → Bool) :
    v_p59 L g { dt with el := f } = v_p59 L g dt := rfl

/-- **The step into a copy site** is the election before it, which returned the thread's lane,
for a thread with `v_p59`. -/
theorem next_into_ptc {L : Launch} {g : Nat} {d0 d : D} {e : Event}
    (hn : next L g d0 e = some (some d)) (hs : d.site ∈ ptcSites) :
    (∃ mask inst, e.kind = .elect mask inst (laneOf L g)) ∧ v_p59 L g d0.dt = true := by
  obtain ⟨s, dt⟩ := d0
  cases s <;> simp only [next] at hn
  all_goals repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       first
         | (simp_all [ptcSites]; done)
         | (simp only [Bool.and_eq_true, beq_iff_eq, elDt, p59_el] at *
            first
              | exact absurd hs (qSite_not_ptc _ _ _ _)
              | simp_all))

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
