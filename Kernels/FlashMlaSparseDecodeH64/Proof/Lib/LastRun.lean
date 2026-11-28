-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LastAt
public import Lemmas.Kit.CountAt
public import Lemmas.Protocol.ClusterTrace

@[expose] public section

/-! # The last four events at a pc are four consecutive counted events

If a thread's events at the pc `p` before its event `k` are all of a counted class `isR`, four of
them have the counts `c0, c0 + 1, c0 + 2, c0 + 3` of the class's prefix counts, and no event at `p`
has a count `c0 + 4` or more, then the thread's last four events at `p` are those four
(`lastAt_run`). It is the way a load of a vector of four words at one pc is read back. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.ClusterTrace PTX.Kit

variable {X : Execution} {g : Nat}

theorem lastAt_zero' (X : Execution) (g i p : Nat) : lastAt X g i p 0 = [] := by
  simp [lastAt, lastN]

/-- Events that are not at `p` leave the last events at `p` as they were. -/
theorem lastAt_const {k p n : Nat} (hk : k ≤ (X.tr g).length) {a : Nat}
    (hno : ∀ i f, a ≤ i → i < k → (X.tr g)[i]? = some f → f.pc ≠ p) (hak : a ≤ k) :
    lastAt X g k p n = lastAt X g a p n := by
  induction k, hak using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    obtain ⟨f, hf⟩ : ∃ f, (X.tr g)[b]? = some f :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [lastAt_succ_ne hf (hno b f hab (by omega) hf)]
    exact ih (by omega) (fun i f' h1 h2 h3 => hno i f' h1 (by omega) h3)

/-- **Four consecutive counted events at a pc are the last four there.** -/
theorem lastAt_run {k p c0 : Nat} {isR : Event → Bool} (hk : k ≤ (X.tr g).length)
    (hP : ∀ i f, i < k → (X.tr g)[i]? = some f → f.pc = p → isR f = true)
    (hex : ∀ j, j < 4 → ∃ kr f, kr < k ∧ (X.tr g)[kr]? = some f ∧ f.pc = p ∧ isR f = true ∧
      ((X.tr g).take kr).countP isR = c0 + j)
    (hend : ∀ i f, i < k → (X.tr g)[i]? = some f → f.pc = p →
      ((X.tr g).take i).countP isR < c0 + 4) :
    ∀ j, j < 4 → ∃ kr f, kr < k ∧ (X.tr g)[kr]? = some f ∧ f.pc = p ∧ isR f = true ∧
      ((X.tr g).take kr).countP isR = c0 + j ∧ (lastAt X g k p 4)[j]? = some f := by
  obtain ⟨k0, f0, hk0, hf0, hp0, hr0, hc0⟩ := hex 0 (by omega)
  obtain ⟨k1, f1, hk1, hf1, hp1, hr1, hc1⟩ := hex 1 (by omega)
  obtain ⟨k2, f2, hk2, hf2, hp2, hr2, hc2⟩ := hex 2 (by omega)
  obtain ⟨k3, f3, hk3, hf3, hp3, hr3, hc3⟩ := hex 3 (by omega)
  -- the positions are in order
  have o01 : k0 < k1 := lt_of_countP_take_lt (xs := X.tr g) (p := isR) (by omega)
  have o12 : k1 < k2 := lt_of_countP_take_lt (xs := X.tr g) (p := isR) (by omega)
  have o23 : k2 < k3 := lt_of_countP_take_lt (xs := X.tr g) (p := isR) (by omega)
  -- no event at `p` in the gaps
  have gap : ∀ (a b : Nat) (fa : Event), a < b → b < k → (X.tr g)[a]? = some fa → isR fa = true →
      ((X.tr g).take b).countP isR = ((X.tr g).take a).countP isR + 1 →
      ∀ i f, a + 1 ≤ i → i < b → (X.tr g)[i]? = some f → f.pc ≠ p := by
    intro a b fa hab hbk hfa hra hcb i f hi1 hi2 hf hpc
    have h1 := countP_take_succ_of hfa hra
    have h2 := countP_take_mono (xs := X.tr g) (p := isR) hi1
    have h3 := countP_take_succ_of hf (hP i f (by omega) hf hpc)
    have h4 := countP_take_mono (xs := X.tr g) (p := isR) (show i + 1 ≤ b by omega)
    omega
  have g01 := gap k0 k1 f0 o01 hk1 hf0 hr0 (by omega)
  have g12 := gap k1 k2 f1 o12 hk2 hf1 hr1 (by omega)
  have g23 := gap k2 k3 f2 o23 hk3 hf2 hr2 (by omega)
  have g3 : ∀ i f, k3 + 1 ≤ i → i < k → (X.tr g)[i]? = some f → f.pc ≠ p := by
    intro i f hi1 hi2 hf hpc
    have h1 := countP_take_succ_of hf3 hr3
    have h2 := countP_take_mono (xs := X.tr g) (p := isR) hi1
    have := hend i f hi2 hf hpc
    omega
  -- the last events at `p`, one more at each position
  have s0 : lastAt X g (k0 + 1) p 1 = [f0] := by
    rw [lastAt_succ_eq hf0 hp0, lastAt_zero']; rfl
  have s1 : lastAt X g (k1 + 1) p 2 = [f0, f1] := by
    rw [lastAt_succ_eq hf1 hp1, lastAt_const (by omega) (a := k0 + 1) (fun i f h1 h2 h3 =>
      g01 i f h1 h2 h3) (by omega), s0]; rfl
  have s2 : lastAt X g (k2 + 1) p 3 = [f0, f1, f2] := by
    rw [lastAt_succ_eq hf2 hp2, lastAt_const (by omega) (a := k1 + 1) (fun i f h1 h2 h3 =>
      g12 i f h1 h2 h3) (by omega), s1]; rfl
  have s3 : lastAt X g (k3 + 1) p 4 = [f0, f1, f2, f3] := by
    rw [lastAt_succ_eq hf3 hp3, lastAt_const (by omega) (a := k2 + 1) (fun i f h1 h2 h3 =>
      g23 i f h1 h2 h3) (by omega), s2]; rfl
  have sk : lastAt X g k p 4 = [f0, f1, f2, f3] := by
    rw [lastAt_const hk (a := k3 + 1) (fun i f h1 h2 h3 => g3 i f h1 h2 h3) (by omega), s3]
  intro j hj
  rw [sk]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · exact ⟨k0, f0, hk0, hf0, hp0, hr0, hc0, rfl⟩
  · exact ⟨k1, f1, hk1, hf1, hp1, hr1, hc1, rfl⟩
  · exact ⟨k2, f2, hk2, hf2, hp2, hr2, hc2, rfl⟩
  · exact ⟨k3, f3, hk3, hf3, hp3, hr3, hc3, rfl⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
