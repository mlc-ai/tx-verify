-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.RingRecords
public import Lemmas.Order.ElectOrdinal

@[expose] public section

/-! # The elected lane of a warp

An election of the kernel has an elected lane in its warp: the lane its leader names, whose
election of the same instance is a need of the returned election (DEP-ORDER). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A lane with an election event has an elected lane in its warp: the lane named by the
instance's leader, whose election of the instance is a need of the returned election (DEP-ORDER)
and returns the same leader (`ElectOk`). -/
theorem elected_of_elect {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {h j pc mask inst leader : Nat}
    (hel : X.Elect (h, j) pc mask inst leader) :
    ∃ h' j', h' < L.threads ∧ SameWarp L h h' ∧ X.Elect (h', j') pc mask inst (laneOf L h') := by
  obtain ⟨hh, -, hmem⟩ := hX.elect.1 _ _ _ _ _ hel
  obtain ⟨x, -, k, pc', ld', rfl, hget⟩ := elect_ready hX hel _ (elect_need_mem hel hmem)
  have hE' : X.Elect (warpLane L h leader, k) pc' mask inst ld' := hget
  obtain ⟨hh', -, -⟩ := hX.elect.1 _ _ _ _ _ hE'
  have hb := hpre.block
  have hl := hmem.1
  have hsw : SameWarp L h (warpLane L h leader) := by
    simp only [warpLane, laneOf] at hh' ⊢
    refine ⟨⟨hh, hh', ?_⟩, ?_⟩ <;> rw [hb] <;> omega
  have hlane : laneOf L (warpLane L h leader) = leader := by
    simp only [warpLane, laneOf]
    rw [hb]
    omega
  obtain ⟨rfl, -, rfl, -⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ hel hE' hsw
  exact ⟨_, k, hh', hsw, by rw [hlane]; exact hE'⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof
