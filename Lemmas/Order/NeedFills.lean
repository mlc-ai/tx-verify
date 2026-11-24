-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Dependency

@[expose] public section

/-! # What fills a need

Every node need of `KindNeeds` (DEP-ORDER) is filled by a thread node, by the record of an object
history (the counter updates a successful poll observed), or by a stage of an operation that a
group wait of the needing event covers (`needs_node_fills`). -/

namespace PTX
open AsyncCopy
noncomputable section

/-- A node need is filled by a thread node, by the record of an object history, or by a stage of
an operation that a group wait of the needing event covers. -/
theorem needs_node_fills {L : Launch} {X : Execution} {e : EvId} {fills : Ref → Prop} {x : Ref}
    (hn : Need.node fills ∈ Needs L X e) (hf : fills x) :
    (∃ t, x = .thread t) ∨ (∃ m, ∃ r ∈ X.objects m, x = r.id) ∨
      ∃ k i p, GroupWaitsFor X k i e ∧ x = .async i p := by
  unfold Needs at hn
  split at hn
  · simp at hn
  rename_i ev _
  cases hk : ev.kind <;> rw [hk] at hn
  all_goals try cases ‹TcKind›
  all_goals try simp only [KindNeeds] at hn
  all_goals try (simp at hn; done)
  all_goals try simp only [ctaBarNeeds, ctaBarWarpNeeds, clusterNeeds, clusterWarpNeeds, maskNeeds,
    groupNeeds, pollNeeds, tcNeeds, resourceNeeds, warpLanes, needsIf] at hn
  all_goals try
    (rcases List.mem_append.mp hn with old | result
     · left; aesop
     · cases Tmem.Pair.allocResultNeeds_node L result
       obtain ⟨store, _, _, _, rfl, _⟩ := Tmem.Pair.AllocResultFill.written L hf
       exact .inl ⟨store, rfl⟩)
  all_goals try (left; aesop; done)
  all_goals first
    | (split at hn
       · simp only [List.mem_flatMap] at hn
         obtain ⟨r, hr, h⟩ := hn
         split at h
         · simp only [List.mem_singleton, Need.node.injEq] at h
           subst h
           exact .inr (.inl ⟨_, r, hr, hf⟩)
         · cases h
       · cases hn)
    | (simp only [List.mem_flatMap, List.mem_range] at hn
       obtain ⟨j, -, h⟩ := hn
       split at h
       · simp only [List.mem_map, Need.node.injEq] at h
         obtain ⟨p, -, rfl⟩ := h
         exact .inr (.inr ⟨_, _, p, ‹_›, hf⟩)
       · simp at h)

end
end PTX
