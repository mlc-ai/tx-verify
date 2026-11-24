-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmBlock
import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open Wg0

noncomputable section

private theorem halfMass_pairs (f : Nat → ℝ) :
    ((List.finRange 16).map fun i => f (2 * i.val)).sum +
      ((List.finRange 16).map fun i => f (2 * i.val + 1)).sum =
      ∑ i ∈ Finset.range 32, f i := by
  change (∑ i : Fin 16, f (2 * i.val)) + (∑ i : Fin 16, f (2 * i.val + 1)) = _
  rw [← Finset.sum_add_distrib]
  have he := (finProdFinEquiv (m := 16) (n := 2)).sum_comp (fun i => f i.val)
  simp only [Fintype.sum_prod_type] at he
  rw [← Fin.sum_univ_eq_sum_range f]
  simpa [Fin.sum_univ_two, finProdFinEquiv, Nat.add_comm] using he

/-- One softmax lane rescales its half mass and adds exactly its 32 block probabilities.
The same probabilities supply the lane's BF16 writes. -/
theorem block_probability_update {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
    (hpre : Pre P L mem0) (d : Wg0.D) (raw : Nat → Nat → Nat) (valid : Nat → Bool) (gain : ℝ)
    (hs : ∀ i : Fin 16, d.scoreSums i.val =
      .pair (peakVal (blockScore P L g (head L g) (32 * half L g + 2 * i.val) raw valid))
        (peakVal (blockScore P L g (head L g) (32 * half L g + 2 * i.val + 1) raw valid)))
    (hg : valFloat .f32 d.gainWord = .ok gain) :
    ∃ d', probabilityUpdate L g d = some d' ∧ d'.sumUpd = true ∧
      d'.lh = (if d.sumUpd then d.lh else 0) * gain +
        (∑ slot ∈ Finset.range 32,
          blockProbability P L g (head L g) (reference d) raw valid (32 * half L g + slot)) ∧
      ∀ slot, 32 * half L g ≤ slot → slot < 32 * half L g + 32 →
        d'.pw (head L g) slot = blockProbability P L g (head L g) (reference d) raw valid slot := by
  let first := 32 * half L g
  let lo (i : Fin 16) := blockScore P L g (head L g) (first + 2 * i.val) raw valid
  let hi (i : Fin 16) := blockScore P L g (head L g) (first + 2 * i.val + 1) raw valid
  let w := blockProbability P L g (head L g) (reference d) raw valid
  obtain ⟨d', hd', hs', hm, hp⟩ := probabilityUpdate_terms hpre d lo hi gain hs hg
  have hsum := halfMass_pairs (fun i => w (first + i))
  have hmass : d'.lh = (if d.sumUpd then d.lh else 0) * gain +
      (∑ slot ∈ Finset.range 32, w (first + slot)) := by
    rw [← hsum]
    simpa only [List.map_map, Function.comp_def, w, lo, hi, blockProbability, Nat.add_assoc]
      using hm
  refine ⟨d', hd', hs', hmass, ?_⟩
  intro slot hlo hhi
  let offset := slot - first
  let i : Fin 16 := ⟨offset / 2, by unfold offset first; omega⟩
  let ps := (List.finRange 16).map (fun i : Fin 16 => (w (first + 2 * i.val),
    w (first + 2 * i.val + 1)))
  have hps : ps.getD i.val (0, 0) =
      (w (first + 2 * i.val), w (first + 2 * i.val + 1)) := by
    have hn : i.val < (List.finRange 16).length := by simp
    dsimp only [ps]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hn, List.getElem_finRange]
    rfl
  have he := hp slot hlo hhi
  change d'.pw (head L g) slot =
    (if offset % 2 = 0 then (ps.getD i.val (0, 0)).1 else (ps.getD i.val (0, 0)).2) at he
  rw [hps] at he
  change d'.pw (head L g) slot = w slot
  rw [he]
  have hidx : first + 2 * i.val + offset % 2 = slot := by
    dsimp [i, offset, first]
    omega
  by_cases hb : offset % 2 = 0
  · rw [ite_eq_left hb]
    change w (first + 2 * i.val) = w slot
    apply congrArg w
    omega
  · rw [ite_eq_right hb]
    change w (first + 2 * i.val + 1) = w slot
    apply congrArg w
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
