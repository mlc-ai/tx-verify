-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FinLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.EpiRd

@[expose] public section

/-! # The finished blocks of a trace

The finished blocks `(w0Fin l).1` of a prefix of a lane of warpgroup 0 are the blocks cut at the
arrivals at pc 1122 (no block closes before the arrival at pc 200: `w0_noEarly`), so a later
prefix extends them, and the block closed by the event at index `K0` is the entry of index
`(w0Fin (take K0)).1.length` of every later prefix's finished blocks (`w0Fin_block_of_close`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem w0Scan_length (l : List Event) : (w0Scan l).1.length = w0Closed l := by
  induction l using List.reverseRecOn with
  | nil => simp [w0Scan, w0Closed]
  | append_singleton l e ih =>
    unfold w0Closed at ih ⊢
    rw [w0Scan_snoc, List.countP_append]
    by_cases h1 : e.pc = w0ArrSPc <;> simp [h1, ih]

/-- Under no early close the finished blocks are the scan's. -/
theorem w0Fin_eq_scan {l : List Event} (h : W0NoEarlyClose l) : w0Fin l = w0Scan l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    have ih := ih h.init
    have hne : ¬ (w0ArrLPc = w0ArrSPc) := by unfold w0ArrLPc w0ArrSPc; decide
    rw [w0Fin_snoc, w0Scan_snoc, ih]
    by_cases h1 : e.pc = w0ArrSPc
    · simp [h1]
    · by_cases h2 : e.pc = w0ArrLPc
      · have h0 := h l.length (by simp) (by simp [h2])
        simp only [List.take_left'] at h0
        have hl : (w0Scan l).1.length = 0 := by rw [w0Scan_length]; exact h0
        have hl' := List.length_eq_zero_iff.mp hl
        simp [h2, hl']
      · simp [h1, h2]

theorem w0Scan_prefix (l ex : List Event) : (w0Scan l).1 <+: (w0Scan (l ++ ex)).1 := by
  induction ex using List.reverseRecOn with
  | nil => simp
  | append_singleton ex e ih =>
    rw [← List.append_assoc, w0Scan_snoc]
    by_cases h1 : e.pc = w0ArrSPc
    · simp only [h1, ite_true]
      exact ih.trans (List.prefix_append _ _)
    · simp only [h1, ite_false]
      exact ih

/-- **A closed block is an entry of every later prefix's finished blocks**: the event at index
`K0` at pc 1122 closes the block in progress before it, the entry of index
`(w0Fin (take K0)).1.length` of the finished blocks of the prefix of length `k > K0`. -/
theorem w0Fin_block_of_close (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {K0 k : Nat} {c0 : Event}
    (hc0 : X.get (g, K0) = some c0) (hpc : c0.pc = 1122) (hk : K0 < k)
    (hal : LaneUbFree X g k) :
    (w0Fin ((X.tr g).take k)).1[(w0Fin ((X.tr g).take K0)).1.length]? =
      some (w0Fin ((X.tr g).take K0)).2 := by
  have hpre : (X.tr g).take (K0 + 1) = (X.tr g).take K0 ++ [c0] := by
    have : (X.tr g)[K0]? = some c0 := hc0
    rw [List.take_add_one, this]; rfl
  have htk : (X.tr g).take k = (X.tr g).take (K0 + 1) ++ ((X.tr g).take k).drop (K0 + 1) := by
    have h1 : ((X.tr g).take k).take (K0 + 1) = (X.tr g).take (K0 + 1) := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    conv_lhs => rw [← List.take_append_drop (K0 + 1) ((X.tr g).take k), h1]
  have hs : w0Scan ((X.tr g).take (K0 + 1)) =
      ((w0Scan ((X.tr g).take K0)).1 ++ [(w0Scan ((X.tr g).take K0)).2], []) := by
    rw [hpre, w0Scan_snoc]
    simp [hpc, w0ArrSPc]
  have h1 := w0Scan_prefix ((X.tr g).take (K0 + 1)) (((X.tr g).take k).drop (K0 + 1))
  rw [hs] at h1
  obtain ⟨t, ht⟩ := h1
  rw [w0Fin_eq_scan (w0_noEarly_pre hp hX hFw hw hal), htk,
    w0Fin_eq_scan (w0_noEarly_pre hp hX hFw hw (hal.mono hk.le))]
  simp only at ht
  rw [← ht]
  simp

/-- **The first closing event after an index**: a closing event (pc 1122) at `K` after `j` has a
first one `K0 ≤ K`, no event between `j` and `K0` at pc 1122. -/
theorem w0_first_close {X : Execution} {g j K : Nat} {c : Event} (hK : X.get (g, K) = some c)
    (hc : c.pc = 1122) (hjK : j < K) :
    ∃ K0, j < K0 ∧ K0 ≤ K ∧ (∃ c0, X.get (g, K0) = some c0 ∧ c0.pc = 1122) ∧
      ∀ q, j < q → q < K0 → ∀ ev, X.get (g, q) = some ev → ev.pc ≠ 1122 := by
  have hex : ∃ n, ∃ ev, X.get (g, j + 1 + n) = some ev ∧ ev.pc = 1122 :=
    ⟨K - (j + 1), c, by rw [show j + 1 + (K - (j + 1)) = K by omega]; exact hK, hc⟩
  classical
  obtain ⟨c0, hc0, hc0pc⟩ := Nat.find_spec hex
  have hmin : ∀ q < Nat.find hex, ∀ ev, X.get (g, j + 1 + q) = some ev → ev.pc ≠ 1122 :=
    fun q hq ev hev h => Nat.find_min hex hq ⟨ev, hev, h⟩
  have hn0 : Nat.find hex ≤ K - (j + 1) := Nat.find_min' hex ⟨c, by
    rw [show j + 1 + (K - (j + 1)) = K by omega]; exact hK, hc⟩
  refine ⟨j + 1 + Nat.find hex, by omega, by omega, ⟨c0, hc0, hc0pc⟩, fun q hq1 hq2 ev hev => ?_⟩
  exact hmin (q - (j + 1)) (by omega) ev
    (by rw [show j + 1 + (q - (j + 1)) = q by omega]; exact hev)

/-- **No closing event between two indices**: the closed blocks of the prefixes are the same. -/
theorem w0Closed_take_eq {X : Execution} {g k K0 : Nat} (hkK : k ≤ K0)
    (h : ∀ q, k ≤ q → q < K0 → ∀ ev, X.get (g, q) = some ev → ev.pc ≠ 1122) :
    w0Closed ((X.tr g).take K0) = w0Closed ((X.tr g).take k) := by
  have h0 : ((X.tr g).take K0).take k = (X.tr g).take k := by
    rw [List.take_take, Nat.min_eq_left hkK]
  have h1 : (X.tr g).take K0 = (X.tr g).take k ++ ((X.tr g).take K0).drop k := by
    conv_lhs => rw [← List.take_append_drop k ((X.tr g).take K0), h0]
  have h2 : (((X.tr g).take K0).drop k).countP (fun e => e.pc = w0ArrSPc) = 0 := by
    refine List.countP_eq_zero.mpr fun a ha => ?_
    obtain ⟨q, hq, hqa⟩ := List.mem_iff_getElem.mp ha
    have hq0 := hq
    simp only [List.length_drop, List.length_take] at hq
    have hget : X.get (g, k + q) = some a := by
      have h3 : (((X.tr g).take K0).drop k)[q]? = some a := by
        rw [List.getElem?_eq_getElem hq0, hqa]
      rw [List.getElem?_drop, List.getElem?_take] at h3
      have hqK : k + q < K0 := by omega
      have h4 : (X.tr g)[k + q]? = some a := by simpa [hqK, Nat.add_comm] using h3
      exact h4
    have := h (k + q) (by omega) (by omega) a hget
    unfold w0ArrSPc
    simpa using this
  unfold w0Closed
  rw [h1, List.countP_append, h2]
  simp

theorem w0Closed_mono {l : List Event} {a b : Nat} (h : a ≤ b) :
    w0Closed (l.take a) ≤ w0Closed (l.take b) := by
  have : l.take a = (l.take b).take a := by rw [List.take_take, Nat.min_eq_left h]
  unfold w0Closed
  rw [this]
  exact (List.take_sublist _ _).countP_le

/-- **No closing event between two indices with the same closed count.** -/
theorem w0_noClose_between {X : Execution} {g k K : Nat}
    (h : w0Closed ((X.tr g).take K) = w0Closed ((X.tr g).take k)) :
    ∀ q, k ≤ q → q < K → ∀ ev, X.get (g, q) = some ev → ev.pc ≠ 1122 := by
  intro q hkq hqK ev hev hpc
  have hpre : (X.tr g).take (q + 1) = (X.tr g).take q ++ [ev] := by
    have : (X.tr g)[q]? = some ev := hev
    rw [List.take_add_one, this]; rfl
  have h1 : w0Closed ((X.tr g).take (q + 1)) = w0Closed ((X.tr g).take q) + 1 := by
    unfold w0Closed
    rw [hpre, List.countP_append]
    simp [hpc, w0ArrSPc]
  have h2 := w0Closed_mono (l := X.tr g) hkq
  have h3 := w0Closed_mono (l := X.tr g) (show q + 1 ≤ K by omega)
  omega

/-- **The carried row sum is nonnegative.** -/
theorem w0Carry_nonneg (sc : ℝ) (bs : List (List Event)) : 0 ≤ (w0Carry sc bs).2 :=
  Wg0.Data.w0Carry_l_nonneg sc bs

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
