-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.Slots
public import Kernels.InklingRelDecode.Proof.Lib.BarOne

@[expose] public section

/-! # The clocks of the generations of the whole-CTA barrier

Barrier 1 has four generations in a launch: the publication of the roles (281), the setup of
the loop (289), the end of the loop (`finish + 276`) and the second dispatch round
(`finish + 288`). Every role's state at a rendezvous of the barrier is at the clock of its
generation, and its other states with `n` earlier rendezvous are earlier than generation `n`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib

/-- The half-CTA rendezvous of the Softmax loop. -/
def loopBarPcs : List Nat := [999, 1012, 2241, 2251, 2326]

/-- The clock of generation `n` of barrier 1. -/
def barCap (n : Nat) : Nat :=
  if n = 0 then Slots.publish else if n = 1 then Slots.reuse
  else if n = 2 then Slots.finish + 276 else Slots.finish + 288

theorem barCap_lt {a b : Nat} (h : a < b) (hb : b ≤ 3) : barCap a < barCap b := by
  unfold barCap Slots.publish Slots.reuse Slots.finish Slots.frame Slots.stride
  split_ifs <;> omega

theorem barCap_le {a b : Nat} (h : a ≤ b) (hb : b ≤ 3) : barCap a ≤ barCap b := by
  rcases Nat.lt_or_ge a b with h | h'
  · exact (barCap_lt h hb).le
  · rw [Nat.le_antisymm h h']

/-- **What a role says about its states' clocks against barrier 1**: a state with `n ≤ 3`
earlier rendezvous is at or before generation `n`, strictly unless it stands at a rendezvous,
where it is exactly at it. -/
def BarCapAt (time pc phase : Nat) : Prop :=
  (pc ∈ barOneSites → phase ≤ 3) ∧ (phase ≤ 3 → time ≤ barCap phase ∧
    (pc ∈ barOneSites → time = barCap phase) ∧ (pc ∉ barOneSites → time < barCap phase))

/-- **The lower clock of a state after `phase` rendezvous of barrier 1**: it is later than the
generation it has passed. -/
def BarLow (time phase : Nat) : Prop := 1 ≤ phase → phase ≤ 4 → barCap (phase - 1) < time

end PTX.Kernels.InklingRelDecode.Proof.Lib
