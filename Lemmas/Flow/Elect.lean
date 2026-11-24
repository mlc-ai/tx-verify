-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Order.JointWaits

@[expose] public section

namespace PTX
noncomputable section

/-- Equal masks in one warp have equal results, across dynamic instances and source
positions. -/
theorem ElectOk.deterministic {L : Launch} {X : Execution} (h : ElectOk L X)
    {e f : EvId} {pc pc' mask inst inst' leader leader' : Nat}
    (he : X.Elect e pc mask inst leader) (hf : X.Elect f pc' mask inst' leader')
    (hw : SameWarp L e.1 f.1) :
    leader = leader' := h.2.2 e f pc pc' mask inst inst' leader leader' he hf hw

/-- A label cannot alias two calls by the same lane, even in a loop. -/
theorem ElectOk.instance_unique {L : Launch} {X : Execution} (h : ElectOk L X)
    {e f : EvId} {pc pc' mask mask' inst leader leader' : Nat}
    (he : X.Elect e pc mask inst leader) (hf : X.Elect f pc' mask' inst leader')
    (hw : SameWarp L e.1 f.1) (ht : e.1 = f.1) : e = f :=
  (h.2.1 e f pc pc' mask mask' inst leader leader' he hf hw).2.2.2 ht

/-- Every lane of the member mask of an election has its own event of the instance. `ElectOk` does
not state the participation of the mask's lanes; their events are the needs of the election
(`KindNeeds`), so this follows from the readiness of its return (`DependencyOk.ready`). -/
theorem DependencyOk.electParticipant {K : Kernel} {L : Launch} {X : Execution}
    (h : DependencyOk L K X) {e : EvId} {pc mask inst leader l : Nat}
    (he : X.Elect e pc mask inst leader) (hl : l < 32) (hm : mask.testBit l = true) :
    ∃ j pc' leader', X.get (warpLane L e.1 l, j) = some ⟨pc', .elect mask inst leader'⟩ := by
  have hneed : Need.node (fun x => ∃ j pc leader, x = .thread (warpLane L e.1 l, j) ∧
      X.get (warpLane L e.1 l, j) = some ⟨pc, .elect mask inst leader⟩) ∈ Needs L X e := by
    simp only [Needs, Execution.Elect] at he ⊢
    rw [he]
    simp only [KindNeeds, List.mem_map, List.mem_filter, List.mem_range]
    exact ⟨l, ⟨hl, hm⟩, rfl⟩
  have hret : Returned X e := by
    simp only [Returned, Execution.Elect] at he ⊢
    rw [he]
    simp [Kind.resume]
  obtain ⟨-, -, j, pc', leader', -, hget⟩ := h.ready e hret _ hneed
  exact ⟨j, pc', leader', hget⟩

end
end PTX
