-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Flow

/-- Shuffle-up with clamp zero selects the lane at the requested offset when it exists. -/
theorem shflSource_up {lane offset : Nat} (hoff : offset < 32) :
    shflSource .up lane offset 0 =
      if offset ≤ lane then (lane - offset, true) else (lane, false) := by
  simp [shflSource, Nat.mod_eq_of_lt hoff]

/-- Shuffle-down with clamp 31 selects the next lane, or keeps the last lane's value. -/
theorem shflSource_down_one (lane : Nat) :
    shflSource .down lane 1 31 =
      if lane + 1 < 32 then (lane + 1, true) else (lane, false) := by
  simp [shflSource, Nat.lt_succ_iff]

/-- The full-warp indexed shuffle can read any lane of the warp. -/
theorem shflSource_idx {offset : Nat} (lane : Nat) (hoff : offset < 32) :
    shflSource .idx lane offset 31 = (offset, true) := by
  have hb : offset &&& 31 = offset := by
    have hb := Nat.and_two_pow_sub_one_eq_mod (x := offset) 5
    simpa [Nat.mod_eq_of_lt hoff] using hb
  simp [shflSource, Nat.mod_eq_of_lt hoff, hb, show offset ≤ 31 by omega]

/-- If the source has reached the same shuffle instance, its operand is the received value. -/
theorem shfl_source_value {K : Kernel} {A : List Assumption} {L : Launch} {m : Mem0}
    {X : Execution} (hX : Consistent L K A m X)
    {g i n pc b c j pc' b' c' : Nat} {mode : ShflMode}
    {a recv src r' : Value} {ok o' : Bool}
    (he : X.get (g, i) = some ⟨pc, .shfl mode a b c recv ok⟩)
    (hk : X.ShflK (g, i) n)
    (hp : X.get (g - laneOf L g + (shflSource mode (laneOf L g) b c).1, j) =
      some ⟨pc', .shfl mode src b' c' r' o'⟩)
    (hj : X.ShflK (g - laneOf L g + (shflSource mode (laneOf L g) b c).1, j) n)
    (hx : ¬ ShflExited X (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) n) :
    recv = src ∧ ok = (shflSource mode (laneOf L g) b c).2 := by
  obtain ⟨hok, ⟨k, p, d, f, r, o, hn, hv⟩ | hExit⟩ :=
    hX.shfl g i n pc mode a b c recv ok he hk
  · have heq : k = j :=
      eq_of_count_eq Execution.isShfl _ hv rfl hp rfl (hn.2.trans hj.2.symm)
    subst k
    rw [hp] at hv
    cases hv
    exact ⟨rfl, hok⟩
  · exact False.elim (hx hExit)

/-- Counting a ballot's initial set bits returns the number of lanes in that prefix. -/
theorem ballot_popc_prefix {word : BitVec 32} {n : Nat} (hn : n ≤ 32)
    (hBit : ∀ lane < 32, word.getLsbD lane = decide (lane < n)) :
    ((List.range 32).filter word.toNat.testBit).length = n := by
  have hFilter : (List.range 32).filter word.toNat.testBit =
      (List.range 32).filter (fun lane => decide (lane < n)) := by
    apply List.filter_congr
    intro lane hl
    exact hBit lane (List.mem_range.mp hl)
  rw [hFilter]
  have h (bound : Nat) :
      ((List.range bound).filter (fun lane => decide (lane < n))).length = min n bound := by
    induction bound with
    | zero => simp
    | succ bound ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih]
      by_cases hb : bound < n
      · simp [hb, Nat.min_eq_right (show bound ≤ n by omega)]
      · simp [hb, Nat.min_eq_left (show n ≤ bound by omega),
          Nat.min_eq_left (show n ≤ bound + 1 by omega)]
  rw [h, Nat.min_eq_left hn]

end PTX.Flow
