-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # The times of a group's barrier arrivals in the rank table

A consumer's arrivals on its group's CLC barrier and output barrier are counted along its trace
from its accumulator polls and its site (`ThreadFacts.cons_bars`). The rank table puts the
`(m + 1)`-th arrival on the CLC barrier at the barrier site of block `m` (`clcBarTime`), and the
`(m + 1)`-th arrival on the output barrier at the slice's barrier site (`outBarTime`). A consumer
outside its exit stage that has made at most `m` arrivals has its next event at or before that
time (`bar_vtime_le`); one that has made more is after it (`bar_vtime_lt`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX

noncomputable section

/-- The time of the `(m + 1)`-th arrival on a group's CLC barrier: its site in block `m`. -/
def clcBarTime (m : Nat) : Nat := blockAt m + 50

/-- The time of the `(m + 1)`-th arrival on a group's output barrier: the first or second barrier
of slice `(m % 16) / 2` of the epilogue of tile `m / 16`. -/
def outBarTime (m : Nat) : Nat := blockAt (m / 16) + 4282 + 32 * (m % 16) + 2 * (m % 2)

/-- The arrival counts of a consumer's state after `T` successful accumulator-full polls: the
relation `ThreadFacts.cons_bars` gives for the CLC barrier (`clc`) or the output barrier. -/
def BarFact (clc : Bool) (c : Consumer.D) (T n : Nat) : Prop :=
  if clc then n + c.clcHold + Consumer.holds c = T + Consumer.tileOpen c
  else n + 16 * (Consumer.holds c + c.inEpi) = 16 * T + c.outPhase

/-- The time of the `(m + 1)`-th arrival on a barrier of the kind. -/
def barTime (clc : Bool) (m : Nat) : Nat := if clc then clcBarTime m else outBarTime m

theorem outPhase_le (c : Consumer.D) : c.outPhase ≤ 16 * c.inEpi := by
  unfold Consumer.D.outPhase Consumer.D.inEpi
  cases hs : c.site <;> simp <;> omega

/-- A consumer outside its exit stage that has made at most `m` arrivals on a barrier has its next
event at or before the barrier's `(m + 1)`-th arrival. -/
theorem bar_vtime_le {clc : Bool} {c : Consumer.D} {T n m : Nat}
    (hx : Consumer.exitOff c = none) (hT : c.started + Consumer.holds c ≤ T)
    (hn : BarFact clc c T n) (hm : n ≤ m) : Consumer.vtime T c ≤ barTime clc m := by
  unfold BarFact barTime at *
  unfold Consumer.D.clcHold Consumer.holds Consumer.tileOpen Consumer.D.started Consumer.D.inEpi
    Consumer.D.outPhase Consumer.vtime Consumer.exitOff clcBarTime outBarTime blockAt blockSpan at *
  cases hs : c.site <;> cases clc <;> simp [hs] at * <;> omega

/-- A consumer outside its exit stage that has made more than `m` arrivals on a barrier has its
next event after the barrier's `(m + 1)`-th arrival. -/
theorem bar_vtime_lt {clc : Bool} {c : Consumer.D} {T n m : Nat}
    (hx : Consumer.exitOff c = none) (hs0 : c.site ≠ .setMaxReg)
      (hT : c.started + Consumer.holds c ≤ T)
    (hn : BarFact clc c T n) (hm : m + 1 ≤ n) : barTime clc m < Consumer.vtime T c := by
  unfold BarFact barTime at *
  unfold Consumer.D.clcHold Consumer.holds Consumer.tileOpen Consumer.D.started Consumer.D.inEpi
    Consumer.D.outPhase Consumer.vtime Consumer.exitOff clcBarTime outBarTime blockAt blockSpan at *
  cases hs : c.site <;> cases clc <;> simp [hs] at * <;> omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
