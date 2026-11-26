-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QkPrev

@[expose] public section

/-! # The MMA two before a PV MMA is the PV MMA with its D column

PV MMA `k ≥ 2` of block `d` (the `24 d + 16 + k`-th MMA issue of the lane, D at `128 (k % 2)`) is
preceded by PV MMA `k - 2` (`mma_pvPrev`), the same D column, `24 d + 16 + k - 2`-th issue; the
only MMA between them is PV MMA `k - 1`, which has the other D column. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

private theorem pvPc_inj' {k k' : Nat} (h : TmemRow.pvPc k = TmemRow.pvPc k') : k = k' := by
  simp only [TmemRow.pvPc] at h
  split_ifs at h <;> omega

private theorem pvPc_rng {k : Nat} (hk : k < 8) :
    1853 ≤ TmemRow.pvPc k ∧ TmemRow.pvPc k ≤ 2160 := by
  simp only [TmemRow.pvPc]
  split <;> omega

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The MMA before PV MMA `k ≥ 2`**: PV MMA `k - 2` of the same block at an event `j < i`, with
the same D column, and every MMA strictly between `j` and `i` has the other D column. -/
theorem mma_pvPrev {i k : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hx : X.get (g, i) = some ⟨TmemRow.pvPc k, .tc (.mma (128 * (k % 2)) s acc mask)⟩)
    (hk2 : 2 ≤ k) (hk : k < 8) :
    ∃ j < i, ∃ s' acc' mask', X.get (g, j) =
        some ⟨TmemRow.pvPc (k - 2), .tc (.mma (128 * (k % 2)) s' acc' mask')⟩ ∧
      (∃ r, mmaIssues ((X.tr g).take i) = 24 * r + 16 + k ∧
        mmaIssues ((X.tr g).take j) = 24 * r + 16 + (k - 2)) ∧
      ∀ j', j < j' → j' < i → ∀ pc dc s2 a2 m2,
        X.get (g, j') = some ⟨pc, .tc (.mma dc s2 a2 m2)⟩ →
        1853 ≤ pc → pc ≤ 2160 → dc ≠ 128 * (k % 2) := by
  have hrg := pvPc_rng hk
  obtain ⟨r, kk, hkk, hn, hcase⟩ := mma_slot_pc hp hX hFw hx ⟨by omega, by omega⟩
  have hkk' : kk = 16 + k := by
    rcases hcase with ⟨hq16, h2, -⟩ | ⟨-, hlt, h2, -⟩
    · simp only [TmemRow.qkPc, TmemRow.pvPc] at h2
      split_ifs at h2 <;> omega
    · have := pvPc_inj' h2
      omega
  subst hkk'
  obtain ⟨j, hji, pc', dc', s', acc', mask', hget, hin1, hin2, hcnt⟩ :=
    mma_with_count (g := g) (X := X) (i := i) (c := 24 * r + 16 + k - 2) (by omega)
  obtain ⟨r', k'', hk'', hnj, hcase'⟩ := mma_slot_pc hp hX hFw hget ⟨by omega, by omega⟩
  have hr' : r' = r ∧ k'' = 16 + k - 2 := by omega
  obtain ⟨rfl, rfl⟩ := hr'
  rcases hcase' with ⟨hlt, -⟩ | ⟨-, hlt, h2, h3⟩
  · omega
  have hpc2 : pc' = TmemRow.pvPc (k - 2) := by
    rw [← h2]
    congr 1
    omega
  have hdc : dc' = 128 * (k % 2) := by omega
  refine ⟨j, hji, s', acc', mask', ?_, ⟨r', by omega, hnj.trans (by omega)⟩, ?_⟩
  · rw [hget, hpc2, hdc]
  · intro j' hj1 hj2 pc dc s2 a2 m2 he hl hh hdc2
    have h1 := mmaIssues_lt hget ⟨hin1, hin2⟩ hj1
    have h2' := mmaIssues_lt he ⟨hl, hh⟩ hj2
    obtain ⟨r2, k3, hk3, hn3, hcase3⟩ := mma_slot_pc hp hX hFw he ⟨by omega, by omega⟩
    have hr3 : r2 = r' ∧ k3 = 16 + k - 1 := by omega
    obtain ⟨rfl, rfl⟩ := hr3
    rcases hcase3 with ⟨hlt3, -⟩ | ⟨-, -, -, h4⟩
    · omega
    · omega

end
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
