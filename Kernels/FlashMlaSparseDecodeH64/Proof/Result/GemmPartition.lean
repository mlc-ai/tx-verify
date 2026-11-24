-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX

noncomputable section

/-- A QK dot product is split into two datapath halves, sixteen issues, and sixteen products
per issue. Each issue covers sixteen adjacent entries in one 128-element group. -/
def qkDepth : Fin 2 × Fin 16 × Fin 16 ≃ Fin 512 where
  toFun x := ⟨128 * (x.2.1.val / 4) + 64 * x.1.val + 16 * (x.2.1.val % 4) + x.2.2.val, by
    have := x.1.isLt
    have := x.2.1.isLt
    have := x.2.2.isLt
    omega⟩
  invFun n := (⟨n.val / 64 % 2, by omega⟩,
    ⟨4 * (n.val / 128) + n.val % 64 / 16, by omega⟩, ⟨n.val % 16, by omega⟩)
  left_inv x := by
    rcases x with ⟨h, i, k⟩
    have hh := h.isLt
    have hi := i.isLt
    have hk := k.isLt
    apply Prod.ext
    · apply Fin.ext
      change (128 * (i.val / 4) + 64 * h.val + 16 * (i.val % 4) + k.val) / 64 % 2 = h.val
      omega
    · apply Prod.ext
      · apply Fin.ext
        change 4 * ((128 * (i.val / 4) + 64 * h.val + 16 * (i.val % 4) + k.val) / 128) +
          (128 * (i.val / 4) + 64 * h.val + 16 * (i.val % 4) + k.val) % 64 / 16 = i.val
        omega
      · apply Fin.ext
        change (128 * (i.val / 4) + 64 * h.val + 16 * (i.val % 4) + k.val) % 16 = k.val
        omega
  right_inv n := by
    apply Fin.ext
    have hn := n.isLt
    change 128 * ((4 * (n.val / 128) + n.val % 64 / 16) / 4) +
      64 * (n.val / 64 % 2) + 16 * ((4 * (n.val / 128) + n.val % 64 / 16) % 4) + n.val % 16 = _
    omega

/-- Combining the QK datapath halves and slices includes each feature exactly once. -/
theorem qk_sum (f : Fin 512 → ℝ) :
    (∑ h : Fin 2, ∑ i : Fin 16, ∑ k : Fin 16, f (qkDepth (h, i, k))) = ∑ a, f a := by
  simpa [Fintype.sum_prod_type] using qkDepth.sum_comp f

/-- Each PV output column accumulates the four slices of the same 64 probability slots. -/
theorem pv_sum (f : Fin 64 → ℝ) :
    (∑ i : Fin 4, ∑ k : Fin 16, f (finProdFinEquiv (i, k))) = ∑ a, f a := by
  simpa [Fintype.sum_prod_type] using (finProdFinEquiv (m := 4) (n := 16)).sum_comp f

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
