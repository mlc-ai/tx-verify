-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Startup.Tmem

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Startup.Export

/-- A lane of warp zero that has made no paired Tensor Memory operation is at the allocation. -/
public theorem site_no_ops {b : Nat} {s} (hb : b < 32) (h : resourceCount b s = 0) :
    s = .alloc := by
  have : ¬ 32 ≤ b := by omega
  cases s <;> simp_all [resourceCount]

/-- A lane of warp zero that has made one is between the allocation and the shuffle. -/
public theorem site_one_op {b : Nat} {s} (hb : b < 32) (h : resourceCount b s = 1) :
    s ≠ .alloc ∧ s ≠ .shfl ∧ ∀ r, s ≠ .enter r := by
  have : ¬ 32 ≤ b := by omega
  cases s <;> simp [resourceCount, this] at h ⊢

end PTX.Kernels.InklingRelDecode.Proof.Startup.Export
