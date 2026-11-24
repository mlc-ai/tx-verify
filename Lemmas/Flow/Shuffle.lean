-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.ShapeExecution

@[expose] public section

/-! # The value of a warp-uniform shuffle

A proof tool. When every thread's `n`-th shuffle has an operand that is the same across each
warp, a full-warp `shfl.sync.idx` from lane 0 receives that operand (`nth_shfl_value`), provided
no thread exits before its `n`-th shuffle. A sequence of such shuffles (e.g. of a shared base,
a warp index and a cluster rank) is handled one index at a time; a thread whose first event is
the shuffle is the case `n = 0` (`first_shfl_value`). A thread machine can then follow each
thread with the received values fixed. -/

namespace PTX.Flow
open PTX

noncomputable section

theorem laneZero_sameWarp {L : Launch} (hpos : 0 < L.block) {g : Nat} (hg : g < L.threads) :
    SameWarp L g (g - laneOf L g) ∧ laneOf L (g - laneOf L g) = 0 := by
  have hl : laneOf L g ≤ g % L.block := by unfold laneOf; omega
  have hb : g - laneOf L g = g / L.block * L.block + (g % L.block - laneOf L g) := by
    have := Nat.div_add_mod g L.block
    rw [Nat.mul_comm] at this
    omega
  have hlt : g % L.block - laneOf L g < L.block := by
    have := Nat.mod_lt g hpos
    omega
  have hdiv : (g - laneOf L g) / L.block = g / L.block := by
    rw [hb, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
  have hmod : (g - laneOf L g) % L.block = g % L.block - laneOf L g := by
    rw [hb, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  refine ⟨⟨⟨hg, lt_of_le_of_lt (Nat.sub_le _ _) hg, hdiv.symm⟩, ?_⟩, ?_⟩
  · rw [hmod]; unfold laneOf; omega
  · show (g - laneOf L g) % L.block % 32 = 0
    rw [hmod]; unfold laneOf; omega

/-- **The `n`-th shuffle of a warp-uniform operand.** Every thread's `n`-th shuffle has the
operand `v h`, which is the same across each warp, and no thread exits before its `n`-th
shuffle: a full-warp `shfl.sync.idx` from lane 0 as a thread's `n`-th shuffle receives its own
operand. -/
theorem nth_shfl_value {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) (hpos : 0 < L.block) {n : Nat}
    {v : Nat → Value}
    (hnth : ∀ h < L.threads, ∀ i pc m a b c r o, X.ShflK (h, i) n →
      X.get (h, i) = some ⟨pc, .shfl m a b c r o⟩ → a = v h)
    (hv : ∀ g h, SameWarp L g h → v h = v g)
    (hexit : ∀ h < L.threads, ¬ ShflExited X h n)
    {g i pc : Nat} (hg : g < L.threads) {a : Value} {recv : Value} {ok : Bool}
    (he : X.get (g, i) = some ⟨pc, .shfl .idx a 0 31 recv ok⟩) (hk : X.ShflK (g, i) n) :
    recv = v g ∧ ok = true := by
  obtain ⟨hok, hsource⟩ := hX.shfl g i n pc .idx a 0 31 recv ok he hk
  have hsrc : shflSource .idx (laneOf L g) 0 31 = (0, true) := by simp [shflSource]
  rw [hsrc] at hok hsource
  simp only [Nat.add_zero] at hok hsource
  obtain ⟨hw, -⟩ := laneZero_sameWarp hpos hg
  have hq : g - laneOf L g < L.threads := hw.1.2.1
  rcases hsource with ⟨j, pc', b', c', r', o', hpeer, hepeer⟩ | hx
  · exact ⟨(hnth _ hq j pc' .idx recv b' c' r' o' hpeer hepeer).trans (hv g _ hw), hok⟩
  · exact absurd hx (hexit _ hq)

/-- Every thread's first event is a full-warp shuffle from lane 0 of the operand `v`, which
is the same across each warp: each thread receives its own operand. -/
theorem first_shfl_value {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) (hpos : 0 < L.block) {pc : Nat}
    {v : Nat → Value}
    (hfirst : ∀ h < L.threads, ∀ ev, X.get (h, 0) = some ev →
      ∃ recv ok, ev = ⟨pc, .shfl .idx (v h) 0 31 recv ok⟩)
    (hv : ∀ g h, SameWarp L g h → v h = v g)
    {g : Nat} (hg : g < L.threads) {recv : Value} {ok : Bool}
    (he : X.get (g, 0) = some ⟨pc, .shfl .idx (v g) 0 31 recv ok⟩) :
    recv = v g ∧ ok = true := by
  -- a thread whose first event is a shuffle has it as its shuffle number 0 and has not exited
  have head : ∀ h < L.threads, ∀ k ev, X.get (h, k) = some ev →
      ∃ f, X.get (h, 0) = some f ∧ X.ShflK (h, 0) 0 ∧
        ∃ recv ok, f = ⟨pc, .shfl .idx (v h) 0 31 recv ok⟩ := by
    intro h hh k ev hk
    have hne : X.tr h ≠ [] := by
      intro hn
      simp only [Execution.get, hn, List.getElem?_nil] at hk
      cases hk
    obtain ⟨f, rest, htr⟩ := List.exists_cons_of_ne_nil hne
    have hf : X.get (h, 0) = some f := by simp only [Execution.get, htr, List.getElem?_cons_zero]
    obtain ⟨recv, ok, rfl⟩ := hfirst h hh f hf
    exact ⟨_, hf, ⟨⟨_, _, _, _, _, _, _, hf⟩, rfl⟩, recv, ok, rfl⟩
  refine nth_shfl_value hX hpos (n := 0) ?_ hv ?_ hg he ⟨⟨_, _, _, _, _, _, _, he⟩, rfl⟩
  · intro h hh i pc' m a b c r o hk hget
    obtain ⟨f, hf, hk0, recv', ok', rfl⟩ := head h hh i _ hget
    obtain rfl : i = 0 := Proof.shfl_index_unique hk hk0
    rw [hf] at hget
    simp only [Option.some.injEq, Event.mk.injEq, Kind.shfl.injEq] at hget
    exact hget.2.2.1.symm
  · rintro h hh ⟨k, pc', hex, hcnt⟩
    obtain ⟨f, hf, -, recv', ok', rfl⟩ := head h hh k _ hex
    cases k with
    | zero => rw [hf] at hex; cases hex
    | succ k =>
      obtain ⟨f', rest, htr⟩ : ∃ f' rest, X.tr h = f' :: rest := by
        cases htr : X.tr h with
        | nil => simp [Execution.get, htr] at hf
        | cons f' rest => exact ⟨f', rest, rfl⟩
      have : f' = ⟨pc, .shfl .idx (v h) 0 31 recv' ok'⟩ := by
        simpa [Execution.get, htr] using hf
      subst this
      rw [htr] at hcnt
      simp [List.take_succ_cons, List.countP_cons, Execution.isShfl] at hcnt

end
end PTX.Flow
