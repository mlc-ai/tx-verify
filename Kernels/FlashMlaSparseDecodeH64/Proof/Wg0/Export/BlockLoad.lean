-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockList
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Seen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PeerPlace
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.PcBound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime

@[expose] public section

/-! # Every closed block has its exchange load

The block closed by the event at pc 1122 at index `K` has an event at pc 572 before it
(`w0_boundSeen`), a read (`wg0_peerPlace`) after `2 r + 2` barrier-9 events, `r` the number of
blocks closed before (`w0_load_of_close`). The `t`-th closing event exists for every `t` below the
number of closed blocks (`w0_close_idx`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- An event of the block in progress is an entry of the list with no closing event after it. -/
theorem w0Scan_snd_idx {l : List Event} {f : Event} (h : f ∈ (w0Scan l).2) :
    ∃ i, l[i]? = some f ∧ w0Closed (l.take i) = w0Closed l := by
  induction l using List.reverseRecOn with
  | nil => simp [w0Scan] at h
  | append_singleton l e ih =>
    rw [w0Scan_snoc] at h
    by_cases h1 : e.pc = w0ArrSPc
    · simp [h1] at h
    · simp only [h1, ite_false, List.mem_append, List.mem_singleton] at h
      have hc : w0Closed (l ++ [e]) = w0Closed l := by
        unfold w0Closed; rw [List.countP_append]; simp [h1]
      rcases h with h | h
      · obtain ⟨i, hi, hc'⟩ := ih h
        have hil : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
        refine ⟨i, by rw [List.getElem?_append_left hil]; exact hi, ?_⟩
        rw [List.take_append_of_le_length hil.le, hc, hc']
      · refine ⟨l.length, by simp [h], ?_⟩
        rw [List.take_left, hc]

/-- **The `t`-th closing event** of a list exists for `t` below its number of closed blocks. -/
theorem w0_close_idx {l : List Event} {t : Nat} (ht : t < w0Closed l) :
    ∃ K c, l[K]? = some c ∧ c.pc = 1122 ∧ w0Closed (l.take K) = t := by
  induction l using List.reverseRecOn with
  | nil => simp [w0Closed] at ht
  | append_singleton l e ih =>
    have hc : w0Closed (l ++ [e]) = w0Closed l + if e.pc = w0ArrSPc then 1 else 0 := by
      unfold w0Closed; rw [List.countP_append]; simp
    by_cases h1 : e.pc = w0ArrSPc
    · simp only [h1, ↓reduceIte] at hc
      by_cases h2 : t < w0Closed l
      · obtain ⟨K, c, hK, hpc, hct⟩ := ih h2
        have hil : K < l.length := (List.getElem?_eq_some_iff.mp hK).1
        exact ⟨K, c, by rw [List.getElem?_append_left hil]; exact hK, hpc, by
          rw [List.take_append_of_le_length hil.le]; exact hct⟩
      · refine ⟨l.length, e, by simp, h1, ?_⟩
        rw [List.take_left]
        omega
    · simp only [h1, ↓reduceIte] at hc
      obtain ⟨K, c, hK, hpc, hct⟩ := ih (by omega)
      have hil : K < l.length := (List.getElem?_eq_some_iff.mp hK).1
      exact ⟨K, c, by rw [List.getElem?_append_left hil]; exact hK, hpc, by
        rw [List.take_append_of_le_length hil.le]; exact hct⟩

open Wg0 Wg0.Data in
/-- **A closed block has its exchange load**: the closing event at index `K` has an event at pc 572
before it, a read, in the same block, after `2 r + 2` barrier-9 events (`r` the blocks closed
before `K`). -/
theorem w0_load_of_close (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {K : Nat} (hal : LaneUbFree X g K)
    {c0 : Event} (hub0 : ∀ f, c0.kind ≠ .ub f) (hv : W0Valid P.scale ((X.tr g).take K))
    (hc0 : X.get (g, K) = some c0) (hpc : c0.pc = 1122) :
    ∃ k a bs, k < K ∧ X.get (g, k) = some ⟨572, .rd a bs⟩ ∧
      ((X.tr g).take k).countP (Execution.isBarId 9) =
        2 * (w0Fin ((X.tr g).take K)).1.length + 2 := by
  obtain ⟨-, hs, -⟩ := w0_boundSeen hp hX hFw hw hc0 hub0 (by omega)
    hv
  obtain ⟨f, hfm, hf572⟩ := hs (by omega) (by omega)
  have hfs : f ∈ (w0Scan ((X.tr g).take K)).2 := by rw [← w0Fin_snd]; exact hfm
  obtain ⟨i, hi, hci⟩ := w0Scan_snd_idx hfs
  have hiK : i < K := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_take] at this
    omega
  have hget : X.get (g, i) = some f := by
    rw [List.getElem?_take_of_lt hiK] at hi
    exact hi
  have hat : MbarRow.Wg0At L g f.pc := ⟨hw, by omega, by omega⟩
  obtain ⟨-, hrd⟩ := wg0_peerPlace hp hX hFw hget (NoUbBefore.ne hal hiK hget) hat (by omega)
  obtain ⟨a, bs, hk, -⟩ := hrd (by omega)
  obtain ⟨pcf, kd⟩ := f
  simp only at hf572 hk
  subst hf572 hk
  refine ⟨i, a, bs, hiK, hget, ?_⟩
  have h1 := w0_cnt_exch hp hX hFw hw hget (NoUbBefore.ne hal hiK hget) (Or.inl rfl)
  rw [h1, w0Fin_length (w0_noEarly_pre hp hX hFw hw (hal.mono hiK.le)),
    w0Fin_length (w0_noEarly_pre hp hX hFw hw hal)]
  rw [List.take_take, Nat.min_eq_left hiK.le] at hci
  rw [hci]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
