-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpLanes

@[expose] public section

/-! # An election performed by a whole warp

A proof tool. When every thread of `g`'s warp can perform the election at `pc` with member mask
`mask` (each one a member, every member lane a thread), the warp performs one instance of it:
a fresh instance label and one leader, the leader of every earlier election of the warp with
this mask if there is one (`exists_leader`), a member otherwise. This is a counted extension
(`elect_counted_extension`). -/

namespace PTX.Step
open PTX AsyncCopy Classical
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- A leader for `mask` in `g`'s warp: a member lane, and the leader of every election of the
warp with this mask. -/
theorem exists_leader (hX : Consistent L K A mem0 X) {g mask lane : Nat}
    (hm : electMember mask lane) :
    ∃ leader, electMember mask leader ∧
      ∀ e pc inst l, SameWarp L g e.1 → X.Elect e pc mask inst l → l = leader := by
  by_cases hex : ∃ e pc inst l, SameWarp L g e.1 ∧ X.Elect e pc mask inst l
  · obtain ⟨e, pc, inst, l, hw, he⟩ := hex
    exact ⟨l, (hX.elect.1 e pc mask inst l he).2.2,
      fun e' pc' inst' l' hw' he' => hX.elect.2.2 e' e pc' pc mask inst' inst l' l he' he
        (sameWarp_trans (sameWarp_symm hw') hw)⟩
  · exact ⟨lane, hm, fun e pc inst l hw he => (hex ⟨e, pc, inst, l, hw, he⟩).elim⟩

/-- **A whole warp performs an election**: a counted extension. -/
theorem elect_counted_extension (hX : Consistent L K A mem0 X) {g pc mask leader : Nat}
    (hg : g < L.threads)
    (hfull : ∀ lane, electMember mask lane → ∃ h, SameWarp L g h ∧ laneOf L h = lane)
    (hmem : ∀ h, SameWarp L g h → electMember mask (laneOf L h))
    (hlead : electMember mask leader)
    (hdet : ∀ e pc' inst l, SameWarp L g e.1 → X.Elect e pc' mask inst l → l = leader)
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Launched L X h)
    (hrel : ∀ h, SameWarp L g h → Released L X h)
    (hrun : ∀ h, SameWarp L g h → ∀ inst, ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧ EStep K A L h t1 ⟨pc, .elect mask inst leader⟩ o)
    (hasm : ∀ inst, ∀ a ∈ A, a.wf L mem0
      (X.appendLanes (warpThreads L g) fun _ => ⟨pc, .elect mask inst leader⟩)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨inst, hfr⟩ := exists_fresh_label hX
  let E : Event := ⟨pc, .elect mask inst leader⟩
  have hmw {h : Nat} : h ∈ warpThreads L g ↔ SameWarp L g h := mem_warpThreads
  -- the elections of the extension: the old ones and the new instance
  have hcases {e : EvId} {p m i l : Nat}
      (he : (X.appendLanes (warpThreads L g) fun _ => E).Elect e p m i l) :
      (e.2 < (X.tr e.1).length ∧ X.Elect e p m i l) ∨
        (SameWarp L g e.1 ∧ e.2 = (X.tr e.1).length ∧ p = pc ∧ m = mask ∧ i = inst ∧
          l = leader) := by
    rcases appendLanes_get_cases he with h | ⟨hh, h2, hq⟩
    · exact .inl h
    · simp only [E, Event.mk.injEq, Kind.elect.injEq] at hq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hq
      exact .inr ⟨hmw.mp hh, h2, rfl, rfl, rfl, rfl⟩
  have hnew {h : Nat} (hs : SameWarp L g h) :
      (X.appendLanes (warpThreads L g) fun _ => E).Elect (h, (X.tr h).length) pc mask inst leader :=
    appendLanes_get_new (hmw.mpr hs)
  -- no old election has the new label
  have hfresh {e : EvId} {p m l : Nat} (he : X.Elect e p m inst l) : False := hfr e _ he rfl
  have helect : ElectOk L (X.appendLanes (warpThreads L g) fun _ => E) := by
    refine ⟨?_, ?_, ?_⟩
    · intro e p m i l he
      rcases hcases he with ⟨-, hx⟩ | ⟨hs, -, rfl, rfl, rfl, rfl⟩
      · exact hX.elect.1 e p m i l hx
      · exact ⟨hs.1.2.1, hmem _ hs, hlead⟩
    · intro e f p p' m m' i l l' he hf hs
      rcases hcases he with ⟨-, hx⟩ | ⟨hse, he2, rfl, rfl, rfl, rfl⟩ <;>
        rcases hcases hf with ⟨-, hy⟩ | ⟨hsf, hf2, rfl, rfl, hi, rfl⟩
      · exact hX.elect.2.1 e f p p' m m' i l l' hx hy hs
      · subst hi
        exact (hfresh hx).elim
      · exact (hfresh hy).elim
      · refine ⟨rfl, rfl, rfl, fun h1 => ?_⟩
        exact Prod.ext h1 (by rw [he2, hf2, h1])
    · intro e f p p' m i i' l l' he hf hs
      rcases hcases he with ⟨-, hx⟩ | ⟨hse, -, rfl, rfl, rfl, rfl⟩ <;>
        rcases hcases hf with ⟨-, hy⟩ | ⟨hsf, -, rfl, hm, rfl, rfl⟩
      · exact hX.elect.2.2 e f p p' m i i' l l' hx hy hs
      · subst hm; exact hdet e p i l (sameWarp_trans hsf (sameWarp_symm hs)) hx
      · exact (hdet f p' i' l' (sameWarp_trans hse hs) hy).symm
      · rfl
  -- every lane of the mask has its election of the new instance (DEP-ORDER)
  have hready : ∀ h ∈ warpThreads L g,
      Ready L (X.appendLanes (warpThreads L g) fun _ => E) (h, (X.tr h).length) := by
    intro h hh n hn
    simp only [Needs, appendLanes_get_new hh, E, KindNeeds, List.mem_map, List.mem_filter,
      List.mem_range] at hn
    obtain ⟨l, ⟨hl, hb⟩, rfl⟩ := hn
    obtain ⟨h', hw, rfl⟩ := hfull l ⟨hl, hb⟩
    have hl' : warpLane L h (laneOf L h') = h' :=
      warpLane_of_sameWarp (sameWarp_trans (sameWarp_symm (hmw.mp hh)) hw)
    refine ⟨.thread (h', (X.tr h').length), ⟨_, appendLanes_get_new (hmw.mpr hw)⟩, ?_⟩
    exact ⟨(X.tr h').length, pc, leader, by rw [hl'], by rw [hl']; exact hnew hw⟩
  have hnot : ∀ h ∈ warpThreads L g, ∀ m a b c recv ok, E.kind ≠ .shfl m a b c recv ok :=
    fun _ _ _ _ _ _ _ _ h => by cases h
  apply appendLanes_counted_extension (ev := fun _ =>
    E) hX (warpThreads_nodup g) (warpThreads_ne_nil hg)
    (fun h hh => (hmw.mp hh).1.2.1) (fun _ _ => trivial) (fun h hh => hst h (hmw.mp hh))
    (fun h hh => hrel h (hmw.mp hh)) (fun h hh => hrun h (hmw.mp hh) inst)
  · intro h hh j hj hm
    rcases hm with ⟨p, p', m, i, l, l', hi, hjx⟩ | ⟨m, i, ⟨p, hp⟩, -⟩ | ⟨-, n, hk, -⟩ | hv
    · rcases hcases hi with ⟨h1, -⟩ | ⟨-, -, -, -, rfl, -⟩
      · simp at h1
      · rcases hcases hjx with ⟨-, hy⟩ | ⟨-, hj2, -⟩
        · exact hfresh hy
        · omega
    · rw [appendLanes_get_new hh] at hp
      simp [E] at hp
    · exact appendLanes_not_shflK_new hh (hnot h hh) hk
    · exact appendLanes_not_voteWait hh rfl (by simp [E]) hv
  · exact hready
  · exact appendLanes_shflOk_of_not_shfl hX hnot
  · exact helect
  · exact appendLanes_warpBarOk_of_not_warpBar hX (fun _ _ _ _ h => by cases h)
  · exact hasm inst

end
end PTX.Step
