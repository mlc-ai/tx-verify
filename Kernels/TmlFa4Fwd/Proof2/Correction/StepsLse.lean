-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Correction.StepsLsePP
public import Kernels.TmlFa4Fwd.Gen.StepCorrection
public import Kernels.TmlFa4Fwd.Proof2.Correction.StepsLsePZ
public import Kernels.TmlFa4Fwd.Proof2.Correction.StepsLseZP
public import Kernels.TmlFa4Fwd.Proof2.Correction.StepsLseZZ
public import Kernels.TmlFa4Fwd.Proof2.Correction.StepsLseL0

@[expose] public section

/-! # The LSE stores

The last arrival of the final stage leads to the two LSE stores. Their segments take the base-2
logarithm of the two row sums: the kernel's `lg2` assumption gives the exact value on a positive
operand, Core's table gives `-inf` on `+0` (a padding row's sum can be zero), and the code's `selp`
on the sum being nonzero then picks the LSE or `-inf`. The machine continues on nonnegative sums (`0
≤ rs0 ∧ 0 ≤ rs1`) and stops otherwise. The last final arrival's four sign cases are one file each
(`StepsLsePP` … `StepsLseZZ`), the first store's in `StepsLseL0`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The last arrival of the final stage: on nonnegative row sums, its successors by the four
cases of their signs; otherwise a stop. -/
theorem stepAt_fd (hp : Pre p L m) {s : Site} (hs : s = .fdone 1 1) (v : V) :
    (code p L g).StepAt ⟨s, v, 0⟩ := by
  by_cases hpos : 0 ≤ v.rs0 ∧ 0 ≤ v.rs1
  · obtain ⟨h0, h1⟩ := hpos
    rcases h0.lt_or_eq with h0 | h0 <;> rcases h1.lt_or_eq with h1 | h1
    · exact stepAt_fdPP hp hs v h0 h1
    · exact stepAt_fdPZ hp hs v h0 h1
    · exact stepAt_fdZP hp hs v h0 h1
    · exact stepAt_fdZZ hp hs v h0 h1
  · subst hs
    exact PTX.Flow.Code.StepAt.of (by site_event (trivial))
      (stop_ok fun e => by simp [succ, hpos])

/-- The second LSE store. -/
theorem stepAt_l1 (hp : Pre p L m) {s : Site} (hs : s = .lse 1) (v : V) :
    (code p L g).StepAt ⟨s, v, 0⟩ := by
  have hparams := params hp
  have hsc := scale_read hp
  corr_sites s

theorem stepAt_lse (hp : Pre p L m) (_hg : g < L.threads) (d : D) (hk : d.k = 0)
    (hs : d.site = .fdone 1 1 ∨ ∃ h, d.site = .lse h) :
    (code p L g).StepAt d := by
  obtain ⟨s, v, k⟩ := d
  simp only at hk hs
  subst hk
  rcases hs with rfl | ⟨h, rfl⟩
  · exact stepAt_fd hp rfl v
  · fin_cases h
    · exact stepAt_l0 hp rfl v
    · exact stepAt_l1 hp rfl v

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Correction
