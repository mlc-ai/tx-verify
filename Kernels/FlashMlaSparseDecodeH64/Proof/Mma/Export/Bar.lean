-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The MMA lane's named barrier

The only named-barrier event of the MMA code is the CTA barrier `barrier.sync 12` at pc 2160,
after the block loop, without a thread count (`mma_bar`); `barRow_mma` is the row `BarRow.Mma`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A barrier event at an MMA pc is `barrier.sync 12` at pc 2160.** -/
theorem mma_bar (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc b : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar b cnt mode⟩) (hr : 1850 ≤ pc ∧ pc < 2162) :
    pc = 2160 ∧ b = 12 ∧ cnt = none ∧ mode = .sync := by
  obtain ⟨d, -, ⟨hpc, hk⟩, hl, -⟩ := mma_at hp hX hFw he (fun _ h => by cases h) hr
  obtain ⟨site, l0, l1, neg, cnt', pha, par⟩ := d
  cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hk
  case outBar => exact ⟨hpc, hk⟩
  case leave i => exact absurd rfl (hl i)

/-- **Row `BarRow.Mma`**: a barrier event of the MMA lane is `everyone_sync` at 2160. -/
theorem barRow_mma (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : BarRow.Mma P L X := by
  intro g k e _ he hat hb
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | bar id cnt md =>
    obtain ⟨-, hlo, hhi⟩ := hat
    obtain ⟨hpc, rfl, rfl, rfl⟩ := mma_bar hp hX hFw he ⟨hlo, hhi⟩
    exact ⟨hpc, rfl⟩
  | _ => simp [Execution.isBar] at hb

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
