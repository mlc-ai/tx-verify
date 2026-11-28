-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Tma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The TMA lane's named barrier

The only named-barrier event of the TMA code is the CTA barrier `barrier.sync 12` at pc 2330,
after the block loop, without a thread count (the count operand is the CTA's 384 threads, which
the template records as none): `tma_bar`, and the row `barRow_tma`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A barrier event at a TMA pc is `barrier.sync 12` at pc 2330.** -/
theorem tma_bar (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc b : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar b cnt mode⟩) (hr : 2162 ≤ pc ∧ pc < 2332) :
    pc = 2330 ∧ b = 12 ∧ cnt = none ∧ mode = .sync := by
  obtain ⟨d, -, -, ⟨hpc, hk⟩, hl, -⟩ := tma_at hp hX hFw he (fun _ h => by cases h) hr
  tma_state d
  cases s <;> simp [Tma.EvK, Tma.Poll, RdAt] at hk
  case outBar => exact ⟨hpc, hk⟩
  case leave i => exact absurd rfl (hl i)

/-- **Row `BarRow.Tma`**: a barrier event of a lane of the role is `everyone_sync` at 2330. -/
theorem barRow_tma (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : BarRow.Tma P L X := by
  intro g k e _ he hat hb
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | bar b cnt mode =>
    obtain ⟨-, hr⟩ := hat
    obtain ⟨rfl, rfl, rfl, rfl⟩ := tma_bar hp hX hFw he hr
    exact ⟨rfl, rfl⟩
  | _ => simp [Execution.isBar] at hb

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
