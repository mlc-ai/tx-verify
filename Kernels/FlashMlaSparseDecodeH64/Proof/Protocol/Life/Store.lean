-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Exit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.TensorOrigin
import Lemmas.Kernel.StoreDrain

@[expose] public section

/-! # An output store's source reads finish before its lane exits

The assumption `storeDrain` (`Assumptions.lean`) selects the four output-store sites
(`tensor_store_origin`: a tensor store is at pc 1358, 1516, 1673 or 1831) and requires the
read completion of each selected store at its lane's exit (`TensorStore.ReadsDrainedBeforeExit`,
a constraint of every consistent execution). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
open PTX

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A tensor store's source reads finish before its CTA exits.** -/
theorem life_store (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) : StoreFinished L kernel Assumptions.all X := by
  intro i a s hi hx
  obtain ⟨g, k⟩ := i
  obtain ⟨-, -, c, hc, hget, -⟩ := tensor_store_origin hp hX hFw hnu hi
  obtain ⟨finish, hfin, hb⟩ := exit_after hX hget (by simp) hx
  have hsel : TensorStore.Selected Assumptions.storeDrain.storeReadsBeforeExit X (g, k) := by
    refine ⟨_, a, s, hget, ?_⟩
    simp only [Assumptions.storeDrain]
    interval_cases c <;> decide
  have hmem : Assumptions.storeDrain ∈ Assumptions.all := by simp [Assumptions.all]
  have hd : TensorStore.ReadsDrainedBeforeExit Assumptions.storeDrain.storeReadsBeforeExit X :=
    hX.asm _ hmem
  exact SharedFinished.of_storeReadsDrained (A := Assumptions.all) (a := Assumptions.storeDrain)
    hmem hb hsel hfin hd

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
