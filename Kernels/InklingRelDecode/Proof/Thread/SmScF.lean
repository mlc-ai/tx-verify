-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmScW
public import Lemmas.Flow.FmaPairCore

@[expose] public section

/-! # The scores `fma(bias, inv_scale, s)` (pcs 1431-1462)

The 32 packed fused multiply-adds `fma.rn.f32x2 %rd(499 + q), %rd(358 - q), %rd12, %rd(499 + q)`
turn the S pairs into the scored pairs. The register `%rd(499 + q)` holds two things in turn: the
pair of the S words `2 q`, `2 q + 1` and then the pair of their scores. The state's S words are
the current contents of the pair registers (the table's pair registers are packs of them, and
`%r415 …` are dead from pc 1298 on), so the scored state `d.scored m`, whose first `m` pairs are
scored, is the state at pc `1431 + m`. The facts at the checkpoints are the live registers valued
by the overlay `wex d 32` of the widened pairs in front of the table of `d.scored m`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat}

/-! ### The code and the liveness of the packed fused multiply-adds -/

/-- The instruction at `pc` is `fma.rn.f32x2 d, a, b, c`. -/
def fma2At (pc d a b c : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .float f⟩ => f == { fma2I with dsts := [some d], srcs := [.reg a, .reg b, .reg c] }
  | _ => false

theorem fma2At_spec {pc d a b c : Nat} (h : fma2At pc d a b c = true) :
    kernel.code[pc]? = some ⟨none, fma2Op d a b c⟩ := by
  unfold fma2At at h
  split at h
  · rename_i f hc
    rw [hc, fma2Op_eq, beq_iff_eq.mp h]
  · cases h

theorem fma_code : ∀ m < 32, fma2At (1431 + m) (2447 + m) (2306 - m) 1960 (2447 + m) = true := by
  decide +kernel

theorem emu_fma : ∀ m < 32, Assumptions.emuSites.contains (1431 + m) = false := by decide +kernel

theorem live_f1 : ∀ m < 32, (2306 - m) ∈ Flow.live (1431 + m) ∧ 1960 ∈ Flow.live (1431 + m) ∧
    (2447 + m) ∈ Flow.live (1431 + m) := by decide +kernel

theorem live_f2 : ∀ m < 32, subX (Flow.live (1431 + m + 1)) (Flow.live (1431 + m))
    [2447 + m] = true := by decide +kernel

theorem live_f3 : ∀ m < 32, ∀ r ∈ Flow.live (1431 + m + 1), ¬ (876 ≤ r ∧ r < 876 + 64) := by
  decide +kernel

/-! ### The table of the scored state -/

theorem valueOf_p1961 (d : D) : valueOf L g d 1960 =
    joinValue (.float .f32 (1 / d.e.sc)) (.float .f32 (1 / d.e.sc)) := by
  sm_vals

/-! ### One fused multiply-add -/

theorem live_wex_dead : ∀ r ∈ Flow.live 1463, ¬ (2275 ≤ r ∧ r < 2275 + 32) := by decide +kernel

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
