-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpLanes

@[expose] public section

/-! # A warp barrier passed by a whole warp

A proof tool. When every thread of `g`'s warp can perform a warp barrier with member mask
`mask` (each one a member, every member lane a thread; source positions may differ), the warp
performs one rendezvous with a fresh instance label: a counted extension
(`warpBar_counted_extension`). -/

namespace PTX.Step
open PTX AsyncCopy Classical
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **A whole warp passes a warp barrier**: a counted extension. -/
theorem warpBar_counted_extension (hX : Consistent L K A mem0 X) {g mask : Nat}
    (pcs : Nat → Nat) (hg : g < L.threads)
    (hfull : ∀ lane, electMember mask lane → ∃ h, SameWarp L g h ∧ laneOf L h = lane)
    (hmem : ∀ h, SameWarp L g h → electMember mask (laneOf L h))
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Launched L X h)
    (hrel : ∀ h, SameWarp L g h → Released L X h)
    (hrun : ∀ h, SameWarp L g h → ∀ inst, ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧ EStep K A L h t1 ⟨pcs h, .warpBar mask inst⟩ o)
    (hasm : ∀ inst, ∀ a ∈ A, a.wf L mem0
      (X.appendLanes (warpThreads L g) fun h => ⟨pcs h, .warpBar mask inst⟩)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨inst, hfr⟩ := exists_fresh_label hX
  let ev : Nat → Event := fun h => ⟨pcs h, .warpBar mask inst⟩
  have hmw {h : Nat} : h ∈ warpThreads L g ↔ SameWarp L g h := mem_warpThreads
  have hcases {e : EvId} {m i : Nat} (he : (X.appendLanes (warpThreads L g) ev).WarpBar e m i) :
      (e.2 < (X.tr e.1).length ∧ X.WarpBar e m i) ∨
        (SameWarp L g e.1 ∧ e.2 = (X.tr e.1).length ∧ m = mask ∧ i = inst) := by
    obtain ⟨p, hp⟩ := he
    rcases appendLanes_get_cases hp with ⟨h1, h2⟩ | ⟨hh, h2, hq⟩
    · exact .inl ⟨h1, p, h2⟩
    · simp only [ev, Event.mk.injEq, Kind.warpBar.injEq] at hq
      obtain ⟨-, rfl, rfl⟩ := hq
      exact .inr ⟨hmw.mp hh, h2, rfl, rfl⟩
  have hnew {h : Nat} (hs : SameWarp L g h) :
      (X.appendLanes (warpThreads L g) ev).WarpBar (h, (X.tr h).length) mask inst :=
    ⟨pcs h, appendLanes_get_new (hmw.mpr hs)⟩
  -- no old warp barrier has the new label
  have hfresh {e : EvId} {m : Nat} (he : X.WarpBar e m inst) : False := by
    obtain ⟨p, hp⟩ := he
    exact hfr e _ hp rfl
  have hwarp : WarpBarOk L (X.appendLanes (warpThreads L g) ev) := by
    refine ⟨?_, ?_⟩
    · intro e m i he
      rcases hcases he with ⟨-, hx⟩ | ⟨hs, -, rfl, rfl⟩
      · exact hX.warpBar.1 e m i hx
      · exact ⟨hs.1.2.1, hmem _ hs⟩
    · intro e f m m' i he hf hs
      rcases hcases he with ⟨-, hx⟩ | ⟨hse, he2, rfl, rfl⟩ <;>
        rcases hcases hf with ⟨-, hy⟩ | ⟨hsf, hf2, rfl, hi⟩
      · exact hX.warpBar.2 e f m m' i hx hy hs
      · subst hi
        exact (hfresh hx).elim
      · exact (hfresh hy).elim
      · exact ⟨rfl, fun h1 => Prod.ext h1 (by rw [he2, hf2, h1])⟩
  -- every lane of the mask has its event of the new instance (DEP-ORDER)
  have hready : ∀ h ∈ warpThreads L g,
      Ready L (X.appendLanes (warpThreads L g) ev) (h, (X.tr h).length) := by
    intro h hh n hn
    simp only [Needs, appendLanes_get_new hh, ev, KindNeeds, List.mem_map, List.mem_filter,
      List.mem_range] at hn
    obtain ⟨l, ⟨hl, hb⟩, rfl⟩ := hn
    obtain ⟨h', hw, rfl⟩ := hfull l ⟨hl, hb⟩
    have hl' : warpLane L h (laneOf L h') = h' :=
      warpLane_of_sameWarp (sameWarp_trans (sameWarp_symm (hmw.mp hh)) hw)
    refine ⟨.thread (h', (X.tr h').length), ⟨_, appendLanes_get_new (hmw.mpr hw)⟩, ?_⟩
    exact ⟨(X.tr h').length, by rw [hl'], by rw [hl']; exact hnew hw⟩
  have hnot : ∀ h ∈ warpThreads L g, ∀ m a b c recv ok, (ev h).kind ≠ .shfl m a b c recv ok :=
    fun _ _ _ _ _ _ _ _ h => by cases h
  apply appendLanes_counted_extension (ev := ev) hX (warpThreads_nodup g) (warpThreads_ne_nil hg)
    (fun h hh => (hmw.mp hh).1.2.1) (fun _ _ => trivial) (fun h hh => hst h (hmw.mp hh))
    (fun h hh => hrel h (hmw.mp hh)) (fun h hh => hrun h (hmw.mp hh) inst)
  · intro h hh j hj hm
    rcases hm with ⟨p, p', m, i, l, l', hi, -⟩ | ⟨m, i, hi, hjx⟩ | ⟨-, n, hk, -⟩ | hv
    · rw [appendLanes_get_new hh] at hi
      simp [ev] at hi
    · rcases hcases hi with ⟨h1, -⟩ | ⟨-, -, -, rfl⟩
      · simp at h1
      · rcases hcases hjx with ⟨-, hy⟩ | ⟨-, hj2, -⟩
        · exact hfresh hy
        · omega
    · exact appendLanes_not_shflK_new hh (hnot h hh) hk
    · exact appendLanes_not_voteWait hh rfl (by simp [ev]) hv
  · exact hready
  · exact appendLanes_shflOk_of_not_shfl hX hnot
  · exact appendLanes_electOk_of_not_elect hX (fun _ _ _ _ _ h => by cases h)
  · exact hwarp
  · exact hasm inst

end
end PTX.Step
