-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnOrigin
import Lemmas.Protocol.ClusterTrace

@[expose] public section

/-! # Concrete softmax return ordinals increase along each lane -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private theorem publication_between_returns {i j : Nat} {e f : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (he : X.get (g, i) = some e) (hf : X.get (g, j) = some f)
    (hie : e.pc = Wg0.Site.validFree.pc) (hjf : f.pc = Wg0.Site.validFree.pc) (hij : i < j) :
    ∃ k, i < k ∧ k < j ∧ ∃ a, X.get (g, k) = some a ∧ isProbabilityPublication a = true := by
  let xs := X.tr g
  let between := (xs.drop (i + 1)).take (j - (i + 1))
  have hi := PTX.len_of_get he
  have hj := PTX.len_of_get hf
  have hFirst : xs.drop i = e :: xs.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, ← List.getElem?_eq_some_iff.mp he |>.2]
  have hSecond : xs.drop j = f :: xs.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hj, ← List.getElem?_eq_some_iff.mp hf |>.2]
  have hSplit : xs = xs.take i ++ e :: (between ++ f :: xs.drop (j + 1)) := by
    nth_rewrite 1 [← List.take_append_drop i xs]
    rw [hFirst]
    congr 2
    nth_rewrite 1 [← List.take_append_drop (j - (i + 1)) (xs.drop (i + 1))]
    rw [List.drop_drop, Nat.add_sub_of_le (show i + 1 ≤ j by omega), hSecond]
  by_contra! hNone
  have hNo : ∀ a ∈ between, a.pc ≠ Wg0.Site.soReady.pc := by
    intro a ha hTag
    obtain ⟨k, hk, hGet⟩ := List.mem_iff_getElem.mp ha
    have hkl : k < j - (i + 1) := lt_of_lt_of_le hk (List.length_take_le ..)
    have hAt : X.get (g, i + 1 + k) = some a := by
      change xs[i + 1 + k]? = _
      rw [← List.getElem?_drop]
      have h : between[k]? = some a := List.getElem?_eq_some_iff.mpr ⟨hk, hGet⟩
      simpa only [between, List.getElem?_take, ite_eq_left hkl] using h
    exact hNone (i + 1 + k) (by omega) (by omega) a hAt (by simp [isProbabilityPublication, hTag])
  obtain ⟨o, hRun⟩ := hX.thr g (Frame.lt_of_get hX he)
  change Run kernel Assumptions.all L g {} xs o at hRun
  rw [hSplit] at hRun
  exact no_second_return_before_publication hie hjf hNo hRun

/-- From a common first mask acquire, two returns on one lane have strictly ordered blocks. -/
theorem actual_softmax_return_count_lt {start i j : Nat} {e f : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (he : X.get (g, i) = some e) (hf : X.get (g, j) = some f)
    (hie : e.pc = Wg0.Site.validFree.pc) (hjf : f.pc = Wg0.Site.validFree.pc)
    (hStart : start ≤ i) (hij : i < j) :
    (((X.tr g).drop start).take (i - start)).countP isProbabilityPublication <
      (((X.tr g).drop start).take (j - start)).countP isProbabilityPublication := by
  obtain ⟨k, hik, hkj, a, ha, hPub⟩ := publication_between_returns hX he hf hie hjf hij
  let xs := (X.tr g).drop start
  have hAt : xs[k - start]? = some a := by
    rw [List.getElem?_drop, Nat.add_sub_of_le (show start ≤ k by omega)]
    exact ha
  have hLe := PTX.ClusterTrace.countP_take_mono (p := isProbabilityPublication) (xs := xs)
    (show i - start ≤ k - start by omega)
  have hLt := PTX.ClusterTrace.countP_take_lt (m := j - start)
    (show k - start < j - start by omega) hAt hPub
  change (xs.take (i - start)).countP _ < (xs.take (j - start)).countP _
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
