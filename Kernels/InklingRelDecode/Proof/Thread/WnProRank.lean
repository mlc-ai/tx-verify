-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LpProRank

@[expose] public section

/-!
# The prologue's sites in program order, for every thread

`prk` (`LpProRank.lean`) ranks a copy site one above the election before it, so its step lemma
`rank_step` needs the thread to lead its elections. `prq` gives a copy site the rank of the
election before it (as `prk` does for `in_k` and `el_k`), so a step of the machine raises the
rank by at most one for every thread, except where it skips a block's sites (at `bar2` if the
number of blocks to preload is 0, at the end of block 0 (1) if it is 1 (2)). `rankq_step` states
this given the gate values of block `b`, with no premise on the thread's elections.

`prq_lb` and `prq_lb_inj`: the load `lbA_b` after block `b`'s arrival has rank `19 + 12 b`, and
no other site has it. `next_into_lbA`: the step into `lbA_b` is from `arrSite b`, or the
arrival's guard `v_p177` is false.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The rank of a site for every thread: program order up to the last election of block 2, a
guarded site with the rank of the site before it, `54` after it. -/
def prq : Site → Nat
  | .sMax => 0 | .ldCu0 => 1 | .ldCu1 => 2 | .ldSk => 3
  | .el0 | .in0 => 4 | .el1 | .in1 => 5 | .el2 | .in2 => 6 | .el3 | .in3 => 7
  | .el4 | .in4 => 8 | .el5 | .in5 => 9 | .el6 | .in6 => 10 | .el7 | .in7 => 11
  | .el8 | .in8 => 12 | .el9 | .in9 => 13 | .el10 | .in10 => 14 | .el11 | .in11 => 15
  | .fnc0 => 16 | .bar2 => 17
  | .pbA0 | .arr0 => 18 | .lbA0 => 19 | .pbB0 => 20 | .psh0 => 21 | .pel0_0 | .ptc0_0 => 22
  | .pbC0 => 23 | .pel0_1 | .ptc0_1 => 24 | .lbB0 => 25 | .pbD0 => 26
  | .pel0_2 | .ptc0_2 => 27 | .pbE0 => 28 | .pel0_3 | .ptc0_3 => 29
  | .pbA1 | .arr1 => 30 | .lbA1 => 31 | .pbB1 => 32 | .psh1 => 33 | .pel1_0 | .ptc1_0 => 34
  | .pbC1 => 35 | .pel1_1 | .ptc1_1 => 36 | .lbB1 => 37 | .pbD1 => 38
  | .pel1_2 | .ptc1_2 => 39 | .pbE1 => 40 | .pel1_3 | .ptc1_3 => 41
  | .pbA2 | .arr2 => 42 | .lbA2 => 43 | .pbB2 => 44 | .psh2 => 45 | .pel2_0 | .ptc2_0 => 46
  | .pbC2 => 47 | .pel2_1 | .ptc2_1 => 48 | .lbB2 => 49 | .pbD2 => 50
  | .pel2_2 | .ptc2_2 => 51 | .pbE2 => 52 | .pel2_3 | .ptc2_3 => 53
  | _ => 54

theorem prq_qSite (L : Launch) (g : Nat) (dt : Dat) (n : Nat) : prq (qSite L g dt n) = 54 := by
  unfold qSite
  split <;> (repeat' split) <;> rfl

/-- The load after the arrival of block `b`. -/
def lbASite : Nat → Site
  | 0 => .lbA0 | 1 => .lbA1 | _ => .lbA2

theorem prq_lb {b : Nat} (hb : b < 3) : prq (lbASite b) = 19 + 12 * b := by
  interval_cases b <;> rfl

/-- No other site has the rank of `lbA_b`. -/
theorem prq_lb_inj {b : Nat} (hb : b < 3) {s : Site} (h : prq s = 19 + 12 * b) :
    s = lbASite b := by
  revert h
  interval_cases b <;> cases s <;> decide

theorem p63_el (L : Launch) (g : Nat) (dt : Dat) (a : Nat) (b : Bool) :
    v_p63 L g (elDt dt a b) = v_p63 L g dt := rfl

theorem p72_el (L : Launch) (g : Nat) (dt : Dat) (a : Nat) (b : Bool) :
    v_p72 L g (elDt dt a b) = v_p72 L g dt := rfl

/-- **One step of the prologue raises `prq` by at most one** for every thread, or it starts at
or after the last site of block `b`, given the gate values of block `b`. -/
theorem rankq_step {L : Launch} {g : Nat} {d0 d : D} {e : Event} {b : Nat}
    (hn : next L g d0 e = some (some d))
    (h53 : d0.site.afterSk = true → v_p53 L g d0.dt = true)
    (h63 : d0.site.afterSk = true → v_p63 L g d0.dt = true → b = 0)
    (h72 : d0.site.afterSk = true → v_p72 L g d0.dt = true → b ≤ 1) :
    prq d.site ≤ prq d0.site + 1 ∨ 29 + 12 * b ≤ prq d0.site := by
  obtain ⟨s, dt⟩ := d0
  simp only at h53 h63 h72
  cases s <;> simp only [next] at hn <;> simp only [Site.afterSk, forall_const] at h53 h63 h72
  all_goals repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       first
         | (left; simp only [prq_qSite]; simp_all [prq]; done)
         | (right; simp_all [prq, p63_el, p72_el]; omega)
         | simp_all [prq, p63_el])

/-- **The step into `lbA_b`** is from `arrSite b`, or the arrival's guard `v_p177` is false. -/
theorem next_into_lbA {L : Launch} {g : Nat} {d0 d : D} {e : Event} {b : Nat} (hb : b < 3)
    (hn : next L g d0 e = some (some d)) (hs : d.site = lbASite b) :
    d0.site = arrSite b ∨ v_p177 L g d0.dt = false := by
  have hr : prq d.site = 19 + 12 * b := by rw [hs]; exact prq_lb hb
  obtain ⟨s, dt⟩ := d0
  cases s <;> simp only [next] at hn
  all_goals repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       first
         | (exfalso; simp only [prq_qSite] at hr; omega)
         | (exfalso; simp only [prq] at hr; omega)
         | (simp only [prq] at hr; interval_cases b <;> simp_all [arrSite, arrSites]))

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
