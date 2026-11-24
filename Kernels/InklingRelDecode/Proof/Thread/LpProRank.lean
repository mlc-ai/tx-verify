-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ClassBt

@[expose] public section

/-!
# The prologue's sites in program order, for the progress to its copies

A rank `prk` of the prologue's sites in program order up to the last copy of block 2 (the
query loads, the stores and the end of the region are one rank above it). A guarded site has the
rank of the site before it (`in_k` that of `el_k`, `arr_b` that of `pbA_b`), so a step of the
machine raises the rank by at most one, except where it skips a block's copies:

* at `bar2`, if the number of blocks to preload is 0 (`v_p53` false);
* at the end of block 0 (1), if it is 1 (2) (`v_p63`, `v_p72`);
* at an election before a copy, if the thread is not the elected lane or not of warps 0 and 1
  (`v_p59`).

`rank_step` states this for a thread that led every election and is of warp 0 or 1, given the
gate values; `gate_of_numPre` gives the gate values from the request's words for a block below
`num_pre`; `p59_of_tid` gives `v_p59` for a thread of warps 0 and 1.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The rank of a site: program order up to the last copy, `66` after it. -/
def prk : Site → Nat
  | .sMax => 0 | .ldCu0 => 1 | .ldCu1 => 2 | .ldSk => 3
  | .el0 | .in0 => 4 | .el1 | .in1 => 5 | .el2 | .in2 => 6 | .el3 | .in3 => 7
  | .el4 | .in4 => 8 | .el5 | .in5 => 9 | .el6 | .in6 => 10 | .el7 | .in7 => 11
  | .el8 | .in8 => 12 | .el9 | .in9 => 13 | .el10 | .in10 => 14 | .el11 | .in11 => 15
  | .fnc0 => 16 | .bar2 => 17
  | .pbA0 | .arr0 => 18 | .lbA0 => 19 | .pbB0 => 20 | .psh0 => 21 | .pel0_0 => 22
  | .ptc0_0 => 23 | .pbC0 => 24 | .pel0_1 => 25 | .ptc0_1 => 26 | .lbB0 => 27 | .pbD0 => 28
  | .pel0_2 => 29 | .ptc0_2 => 30 | .pbE0 => 31 | .pel0_3 => 32 | .ptc0_3 => 33
  | .pbA1 | .arr1 => 34 | .lbA1 => 35 | .pbB1 => 36 | .psh1 => 37 | .pel1_0 => 38
  | .ptc1_0 => 39 | .pbC1 => 40 | .pel1_1 => 41 | .ptc1_1 => 42 | .lbB1 => 43 | .pbD1 => 44
  | .pel1_2 => 45 | .ptc1_2 => 46 | .pbE1 => 47 | .pel1_3 => 48 | .ptc1_3 => 49
  | .pbA2 | .arr2 => 50 | .lbA2 => 51 | .pbB2 => 52 | .psh2 => 53 | .pel2_0 => 54
  | .ptc2_0 => 55 | .pbC2 => 56 | .pel2_1 => 57 | .ptc2_1 => 58 | .lbB2 => 59 | .pbD2 => 60
  | .pel2_2 => 61 | .ptc2_2 => 62 | .pbE2 => 63 | .pel2_3 => 64 | .ptc2_3 => 65
  | _ => 66

theorem prk_qSite (L : Launch) (g : Nat) (dt : Dat) (n : Nat) : prk (qSite L g dt n) = 66 := by
  unfold qSite
  split <;> (repeat' split) <;> rfl

/-- The rank of copy `j` (block `j / 4`). -/
theorem prk_ptc {j : Nat} (hj : j < 12) :
    23 + 16 * (j / 4) ≤ prk (ptcSite j) ∧ prk (ptcSite j) ≤ 23 + 16 * (j / 4) + 10 := by
  interval_cases j <;> decide

/-- The copy sites have ranks no other site has. -/
theorem prk_ptc_inj {j : Nat} (hj : j < 12) {s : Site} (h : prk s = prk (ptcSite j)) :
    s = ptcSite j := by
  revert h
  interval_cases j <;> cases s <;> decide

theorem prk_le (s : Site) : prk s ≤ 66 := by cases s <;> simp [prk]

/-- `v_p59` is `tid < 64` for a thread of the default partition. -/
theorem p59_tab : ∀ t < 128,
    pLtU32 (wAnd32 (BitVec.ofNat 64 t) (BitVec.ofInt 64 127)) (BitVec.ofInt 64 64) =
      decide (t < 64) := by
  decide +kernel

theorem p59_of_tid {L : Launch} {g : Nat} (dt : Dat) (ht : tidOf L g < 64) :
    v_p59 L g dt = true := by
  have := p59_tab (tidOf L g) (by omega)
  simp only [v_p59, v_r27, v_r1]
  rw [this]
  simp [ht]

/-- **The gate values of a block below `num_pre`.** -/
theorem gate_of_numPre {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) {g : Nat}
    (hg : g < L.threads) {dt : Dat} (ha : ArgsOk L g dt.pro) (hs : dt.pro.w71 = P.splits)
    (hm : WordsMatch P (cta L g .z) dt) {b : Nat}
    (hb : b < numPre P (cta L g .z) (cta L g .x)) :
    v_p53 L g dt = true ∧ (1 ≤ b → v_p63 L g dt = false) ∧
      (2 ≤ b → v_p72 L g dt = false) := by
  have hw := wordsOk_of_pre hpre hg ha hs hm
  have hx := (cta_lt hpre hg).1
  have h31 := v_r31_val L g dt ha hw
  have hit := itersN_eq hs hx hm
  have hol := oldN_eq hs hx hm
  have hl1 := itersN_lt L g dt ha hw
  have hmin : min (oldN L g dt) (itersN L g dt) < 2 ^ 31 :=
    lt_of_le_of_lt (Nat.min_le_right _ _) hl1
  have hle : b < min (oldN L g dt) (itersN L g dt) := by
    unfold numPre at hb
    rw [hit, hol]
    omega
  simp only [v_p53, v_p63, v_p72, h31, pNe0 _ hmin, pEq1 _ hmin, pLt3 _ hmin]
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · simp only [decide_eq_true_eq]; omega
  · simp only [decide_eq_false_iff_not]; omega
  · simp only [decide_eq_false_iff_not]
    unfold numPre at hb
    omega

/-- **One step of the prologue raises the rank by at most one** for a thread of warps 0 and 1 that
leads its elections, or it starts at or after the last copy of block `b`, given the gate values
of block `b`. -/
theorem rank_step {L : Launch} {g : Nat} {d0 d : D} {e : Event} {b : Nat}
    (hn : next L g d0 e = some (some d))
    (hl : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g)
    (h59 : ∀ dt, v_p59 L g dt = true)
    (h53 : d0.site.afterSk = true → v_p53 L g d0.dt = true)
    (h63 : d0.site.afterSk = true → v_p63 L g d0.dt = true → b = 0)
    (h72 : d0.site.afterSk = true → v_p72 L g d0.dt = true → b ≤ 1) :
    prk d.site ≤ prk d0.site + 1 ∨ 23 + 16 * b + 10 ≤ prk d0.site := by
  obtain ⟨s, dt⟩ := d0
  simp only at h53 h63 h72
  cases s <;> simp only [next] at hn <;> simp only [Site.afterSk, forall_const] at h53 h63 h72
  all_goals repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       first
         | (left; simp only [prk_qSite]; simp_all [prk]; done)
         | (right; simp_all [prk]; omega)
         | simp_all [prk])

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
