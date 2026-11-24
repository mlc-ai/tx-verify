-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpVote

@[expose] public section

/-! # A predicate vote performed by a whole warp -/

namespace PTX.Step

open PTX AsyncCopy Classical

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- When every named lane can perform the same mode vote, its warp can perform that
instance with the reduction of the participating predicates. -/
theorem vote_mode_counted_extension (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0)
    {g pc mask : Nat} (mode : VoteMode) (a : Nat → Bool) (hg : g < L.threads)
    (hmem : ∀ h, SameWarp L g h → mask.testBit (laneOf L h) = true)
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Launched L X h)
    (hrel : ∀ h, SameWarp L g h → Released L X h)
    (hrun : ∀ h, SameWarp L g h → ∀ result, ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧
      EStep K A L h t1 ⟨pc, .voteMode mode mask (a h) result⟩ o)
    (hasm : ∀ result, ∀ am ∈ A, am.wf L mem0 (X.appendLanes (warpThreads L g)
      (fun h => ⟨pc, .voteMode mode mask (a h) result⟩))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  let partFor := fun lane => some (a (warpLane L g lane))
  let result := voteResult mode partFor
  let ev : Nat → Event := fun h => ⟨pc, .voteMode mode mask (a h) result⟩
  let cnt := maskCount voteClass X g mask
  have hmw {h : Nat} : h ∈ warpThreads L g ↔ SameWarp L g h := mem_warpThreads
  have le : X.le (X.appendLanes (warpThreads L g) ev) := le_appendLanes
  have ha := appendLanes_threadAppend (X := X) (ds := warpThreads L g) (ev := ev)
  have hlive : ∀ x, SameWarp L g x → ∀ k pc, X.get (x, k) ≠ some ⟨pc, .exit⟩ := by
    intro x hx k pce hex
    obtain ⟨t, -, -, hr, -⟩ := hrun x hx false
    exact hr.no_exit hex
  have hcnt {h : Nat} (hs : SameWarp L g h) : maskCount voteClass X h mask = cnt :=
    (vote_count_eq hX hs hlive hmem).symm
  have hlane (h : Nat) : laneOf L h < 32 := Nat.mod_lt _ (by decide)
  have hthr {v : EvId} {q : Event} (hv : X.get v = some q) : v.1 < L.threads := by
    by_contra hn
    have := len_of_get hv
    rw [hX.outside v.1 (by omega)] at this
    simp at this
  -- The new votes are the instance of ordinal `cnt` of the member mask `mask`
  have hnewK {h m n' : Nat} (hs : SameWarp L g h)
      (hk : (X.appendLanes (warpThreads L g) ev).MaskK voteClass (h, (X.tr h).length) m n') :
      m = mask ∧ n' = cnt := by
    obtain ⟨⟨q, p, hq, hc, hm⟩, hc'⟩ := hk
    rw [appendLanes_get_new (hmw.mpr hs)] at hq
    cases hq
    simp only [ev, voteClass, Option.some.injEq] at hc
    subst hc
    subst hm
    refine ⟨rfl, ?_⟩
    rw [appendLanes_take (i := (h, (X.tr h).length)) le_rfl, List.take_length] at hc'
    exact hc'.symm.trans (hcnt hs)
  have hatNew {h : Nat} (hs : SameWarp L g h) :
      (X.appendLanes (warpThreads L g) ev).MaskAt voteClass (h, (X.tr h).length) mask cnt
        mode := by
    refine ⟨⟨⟨_, _, appendLanes_get_new (hmw.mpr hs), rfl, rfl⟩, ?_⟩, _, _,
      appendLanes_get_new (hmw.mpr hs), rfl, rfl⟩
    rw [appendLanes_take (i := (h, (X.tr h).length)) le_rfl, List.take_length]
    exact hcnt hs
  -- an old vote of a lane of the warp with member mask `mask` has an ordinal below `cnt`
  have hold {v : EvId} (hs : SameWarp L g v.1) (hv : v.2 < (X.tr v.1).length)
      (hk : (X.appendLanes (warpThreads L g) ev).MaskK voteClass v mask cnt) : False := by
    have hk' := ha.maskK (ha.not_new hv) hk
    have := MaskK.lt_count hk'
    rw [hcnt hs] at this
    exact Nat.lt_irrefl _ this
  have hexit : ∀ v pc', (X.appendLanes (warpThreads L g) ev).get v = some ⟨pc', .exit⟩ →
      X.get v = some ⟨pc', .exit⟩ := fun v pc' h =>
    (appendLanes_get_kind (fun j _ h => by simp [ev] at h)).mp h
  -- an instance of an old vote is one of `X`: the new ballots have the ordinal `cnt`
  have hinstX {g' i' m n : Nat} {q : VoteMode} {part : Nat → Option Bool}
      (hio : i' < (X.tr g').length) (hk : X.MaskK voteClass (g', i') m n)
      (hi : MaskInstance L voteClass (X.appendLanes (warpThreads L g) ev) g' m n q part) :
      MaskInstance L voteClass X g' m n q part := by
    have hg' : g' < L.threads := hthr hk.1.choose_spec.choose_spec.1
    intro lane hl
    obtain ⟨h1, h2⟩ := hi lane hl
    refine ⟨fun hbit => ?_, h2⟩
    rcases h1 hbit with ⟨j, pc', k, v, hj, hc, hkk, hp⟩ | ⟨hx, hp⟩
    · rcases appendLanes_get_cases hj with ⟨hjo, hjX⟩ | ⟨hxd, hjl, -⟩
      · exact .inl ⟨j, pc', k, v, hjX, hc, ha.maskK (ha.not_new hjo) hkk, hp⟩
      · exfalso
        simp only at hxd hjl
        subst hjl
        have hsx := hmw.mp hxd
        obtain ⟨rfl, rfl⟩ := hnewK hsx hkk
        have hsg : SameWarp L g g' :=
          sameWarp_trans hsx (sameWarp_symm (sameWarp_lane hb hg' hl).1)
        have := MaskK.lt_count hk
        rw [hcnt hsg] at this
        exact Nat.lt_irrefl _ this
    · exact .inr ⟨Execution.maskExited_of_le le hexit hx, hp⟩
  have hnotKind {k : Kind} (hk : ∀ p m b r, k ≠ .voteMode p m b r) {v : EvId}
      {pc' : Nat} : (X.appendLanes (warpThreads L g) ev).get v = some ⟨pc', k⟩ →
      X.get v = some ⟨pc', k⟩ :=
    (appendLanes_get_kind (fun _ _ h => hk _ _ _ _ h.symm)).mp
  have hvote : VoteOk L (X.appendLanes (warpThreads L g) ev) := by
    intro g' i n' pc' m' a' bal hget hk part hp
    have he := hnotKind (fun _ _ _ _ h => by cases h) hget
    have hOld := Execution.maskK_of_le le he hk
    exact hX.vote _ _ _ _ _ _ _ he hOld part (hinstX (len_of_get he) hOld hp)
  have hvalue : WarpValueOk L (X.appendLanes (warpThreads L g) ev) := by
    obtain ⟨hv, hr, hm, ham⟩ := hX.warpValue
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g' i pc' mode' m' a' r n hget hk part hp
      rcases appendLanes_get_cases hget with ⟨hio, hx⟩ | ⟨hh, hi, hq⟩
      · have hkx := Execution.maskK_of_le le hx hk
        exact hv _ _ _ _ _ _ _ _ hx hkx part (hinstX hio hkx hp)
      · simp only [ev, Event.mk.injEq, Kind.voteMode.injEq] at hq
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hq
        have hs := hmw.mp hh
        simp only at hi
        subst hi
        obtain ⟨-, rfl⟩ := hnewK hs hk
        have hParts : ∀ lane ∈ List.range 32, partFor lane = part lane := by
          intro lane hl
          have hl32 := List.mem_range.mp hl
          obtain ⟨hsx, hlx⟩ := sameWarp_lane hb hs.1.2.1 hl32
          have hsx' := sameWarp_trans hs hsx
          have hLane := (warpLane_of_sameWarp hsx').symm
          rw [hlx] at hLane
          have hbit := hmem _ hsx'
          rw [hlx] at hbit
          rcases (hp lane hl32).1 hbit with ⟨j, pc'', k, v, hj, hc, hkk, hpv⟩ | ⟨hEx, _⟩
          · rcases appendLanes_get_cases hj with ⟨hjo, -⟩ | ⟨-, -, hq⟩
            · exact (hold (v := (_, j)) hsx' hjo hkk).elim
            · have hk := congrArg Event.kind hq
              change k = _ at hk
              rw [hk] at hc
              simp only [ev, voteClass, Option.some.injEq, WarpPart.mk.injEq] at hc
              obtain ⟨-, -, rfl⟩ := hc
              rw [hpv]
              simp only [partFor, hLane]
          · obtain ⟨j, exitSite, hx, _⟩ := hEx
            exact (hlive _ hsx' j exitSite (hexit _ _ hx)).elim
        unfold result voteResult
        rw [List.filterMap_congr hParts]
    · intro g' i pc' op signed m a' r n hget hk part hp
      have hx := hnotKind (fun _ _ _ _ h => by cases h) hget
      refine hr g' i pc' op signed m a' r n hx (Execution.maskK_of_le le hx hk) part
        (Execution.maskInstance_of_le le (fun v pc'' k w hj hc => ?_) hexit hp)
      exact hnotKind (fun _ _ _ _ h => by rw [h] at hc; cases hc) hj
    · intro g' i pc' all wide m a' r p n hget hk part hp
      have hx := hnotKind (fun _ _ _ _ h => by cases h) hget
      refine hm g' i pc' all wide m a' r p n hx (Execution.maskK_of_le le hx hk) part
        (Execution.maskInstance_of_le le (fun v pc'' k w hj hc => ?_) hexit hp)
      exact hnotKind (fun _ _ _ _ h => by rw [h] at hc; cases hc) hj
    · intro g' i pc' r hget
      exact ham g' i pc' r (hnotKind (fun _ _ _ _ h => by cases h) hget)
  -- Every lane of the member mask has its vote of the new instance (DEP-ORDER)
  have hready : ∀ h ∈ warpThreads L g,
      Ready L (X.appendLanes (warpThreads L g) ev) (h, (X.tr h).length) := by
    intro h hh nd hn
    simp only [Needs, appendLanes_get_new hh, KindNeeds, maskNeeds, Option.bind_some, ev,
      voteClass, List.mem_map, List.mem_filter, List.mem_range] at hn
    obtain ⟨l, ⟨hl, -⟩, rfl⟩ := hn
    have hs := hmw.mp hh
    obtain ⟨hw, -⟩ := sameWarp_lane hb hs.1.2.1 hl
    have hs' : SameWarp L g (warpLane L h l) := sameWarp_trans hs hw
    refine ⟨.thread (warpLane L h l, (X.tr (warpLane L h l)).length),
      ⟨_, appendLanes_get_new (hmw.mpr hs')⟩, _, rfl, ?_⟩
    exact ⟨sameWarp_symm hw, _, cnt, mode, hatNew hs, .inl (hatNew hs')⟩
  have hnot : ∀ h ∈ warpThreads L g, ∀ m a b c recv ok, (ev h).kind ≠ .shfl m a b c recv ok :=
    fun _ _ _ _ _ _ _ _ h => by cases h
  apply appendLanes_counted_extension_lane (ev := ev) hX (warpThreads_nodup g)
    (warpThreads_ne_nil hg) (fun h hh => (hmw.mp hh).1.2.1) (fun _ _ => trivial)
    (fun h hh => hst h (hmw.mp hh)) (fun h hh => hrel h (hmw.mp hh))
    (fun h hh => hrun h (hmw.mp hh) _)
  · intro h hh j hj hm
    rcases hm with ⟨p, p', m, i, l, l', hi, -⟩ | ⟨m, i, ⟨p, hi⟩, -⟩ | ⟨-, n, hk, -⟩ |
      ⟨hs, m, n', q, hatj, hx | ⟨-, ⟨pce, he⟩, -⟩⟩
    · rw [appendLanes_get_new hh] at hi
      simp [ev] at hi
    · rw [appendLanes_get_new hh] at hi
      simp [ev] at hi
    · exact appendLanes_not_shflK_new hh (hnot h hh) hk
    · obtain ⟨rfl, rfl⟩ := hnewK (hmw.mp hh) hx.1
      exact hold (sameWarp_trans (hmw.mp hh) hs) hj hatj.1
    · rw [appendLanes_get_new hh] at he
      simp [ev] at he
  · exact hready
  · exact appendLanes_shflOk_of_not_shfl hX hnot
  · exact appendLanes_electOk_of_not_elect hX (fun _ _ _ _ _ h => by cases h)
  · exact appendLanes_warpBarOk_of_not_warpBar hX (fun _ _ _ _ h => by cases h)
  · exact hvote
  · exact hvalue
  · exact hasm result

end
end PTX.Step
