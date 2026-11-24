-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpLanes
public import Lemmas.Protocol.CountNth
public import Lemmas.Step.ExitLast

@[expose] public section

/-! # A shuffle performed by a whole warp

A proof tool. The lanes of a warp have made equally many shuffles (`shfl_count_eq`, from
DEP-WARP-SHUFFLE). When every thread of `g`'s warp can perform the shuffle at `pc` with mode `m` and
its operands `a h`, `b h`, `c h`, in a CTA whose size is a multiple of 32, the warp performs one
instance: each lane receives the operand of the source lane that the `shfl.sync` pseudo-code
selects (`shflSource`). This is a counted extension (`shfl_counted_extension`). -/

namespace PTX.Step
open PTX AsyncCopy Classical
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- The source lane of a lane of a warp is a lane of the warp. -/
theorem shflSource_lt (mode : ShflMode) {lane : Nat} (hl : lane < 32) (b c : Nat) :
    (shflSource mode lane b c).1 < 32 := by
  have hc : c % 32 < 2 ^ 5 := Nat.mod_lt _ (by decide)
  have hl' : lane < 2 ^ 5 := hl
  have hmax : (lane &&& c / 256 % 32) ||| (c % 32 &&& (31 - c / 256 % 32)) < 2 ^ 5 :=
    Nat.or_lt_two_pow (lt_of_le_of_lt Nat.and_le_left hl') (lt_of_le_of_lt Nat.and_le_left hc)
  unfold shflSource
  cases mode <;> simp only <;> split_ifs <;> omega

/-- A shuffle ordinal is below the thread's number of shuffles. -/
theorem ShflK.lt_count {e : EvId} {n : Nat} (h : X.ShflK e n) :
    n < (X.tr e.1).countP Execution.isShfl := by
  obtain ⟨⟨pc, m, a, b, c, r, o, hs⟩, hk⟩ := h
  have hlt := len_of_get hs
  have hsplit := List.take_append_drop e.2 (X.tr e.1)
  have hd : ((X.tr e.1).drop e.2).countP Execution.isShfl ≥ 1 := by
    have hx : (X.tr e.1)[e.2]? = some ⟨pc, .shfl m a b c r o⟩ := hs
    rw [List.getElem?_eq_getElem hlt] at hx
    rw [List.drop_eq_getElem_cons hlt, List.countP_cons, Option.some.inj hx]
    simp [Execution.isShfl]
  rw [← hsplit, List.countP_append, hk]
  omega

/-- A thread with more than `c` shuffles has its shuffle number `c`. -/
theorem exists_shflK {g c : Nat} (h : c + 1 ≤ (X.tr g).countP Execution.isShfl) : ∃ j,
    X.ShflK (g, j) c := by
  obtain ⟨j, x, hx, hp, hc⟩ := MbarRing.Slot.exists_nth_countP Execution.isShfl h
  obtain ⟨pc, k⟩ := x
  cases k <;> simp only [Execution.isShfl, Bool.false_eq_true] at hp
  exact ⟨j, ⟨_, _, _, _, _, _, _, hx⟩, hc⟩

/-- A shuffle of `X` has, in every lane of its warp, the shuffle of the same ordinal, or that lane
exited before it: a shuffle event has returned, so its needs are filled (DEP-ORDER,
DEP-WARP-INSTANCE). -/
theorem shfl_lane_of_ready (hX : Consistent L K A mem0 X) {g i n pc : Nat} {m : ShflMode}
    {a : Value} {b c : Nat} {r : Value} {o : Bool}
    (hget : X.get (g, i) = some ⟨pc, .shfl m a b c r o⟩) (hk : X.ShflK (g, i) n) {h : Nat}
    (hs : SameWarp L g h) : (∃ j, X.ShflK (h, j) n) ∨ ShflExited X h n := by
  have hr : Ready L X (g, i) := hX.dependency.ready _ (by simp [Returned, hget, Kind.resume])
  have hl : laneOf L h < 32 := Nat.mod_lt _ (by decide)
  have hmem := maskNeeds_mem L shflClass X (g, i) hget rfl hl
    (Nat.testBit_two_pow_sub_one 32 _ ▸ decide_eq_true hl)
  have hn := hr _ (by simpa only [Needs, hget, KindNeeds] using hmem)
  obtain ⟨-, -, j, rfl, -, m', n', q, hat, hx⟩ := hn
  rw [warpLane_of_sameWarp hs] at hx
  obtain ⟨hm', hk'⟩ := (maskK_shflClass _ _ _ _).mp hat.1
  have hn' : n' = n := hk'.2.symm.trans hk.2
  subst hn' hm'
  rcases hx with hx | ⟨-, hx⟩
  · exact .inl ⟨j, ((maskK_shflClass _ _ _ _).mp hx.1).2⟩
  · obtain ⟨pc', he, hc⟩ := (maskExitK_shflClass _ _ _ _).mp hx
    exact .inr ⟨j, pc', he, hc⟩

/-- **The lanes of a warp have made equally many shuffles.** -/
theorem shfl_count_eq (hX : Consistent L K A mem0 X) {g h : Nat} (hs : SameWarp L g h)
    (hlive : ∀ x, SameWarp L g x → ∀ n, ¬ ShflExited X x n) :
    (X.tr g).countP Execution.isShfl = (X.tr h).countP Execution.isShfl := by
  have le_of {g h : Nat} (hs : SameWarp L g h) (hh : ∀ n, ¬ ShflExited X h n) :
      (X.tr g).countP Execution.isShfl ≤ (X.tr h).countP Execution.isShfl := by
    by_contra hlt
    obtain ⟨j, hj⟩ := exists_shflK (X := X) (g := g) (c :=
      (X.tr h).countP Execution.isShfl) (by omega)
    obtain ⟨⟨pc, m, a, b, c, r, o, hget⟩, hk⟩ := id hj
    obtain ⟨j', hk'⟩ := (shfl_lane_of_ready hX hget hj hs).resolve_right (hh _)
    exact Nat.lt_irrefl _ (ShflK.lt_count hk')
  exact Nat.le_antisymm (le_of hs (hlive h hs))
    (le_of (sameWarp_symm hs) (hlive g (sameWarp_trans hs (sameWarp_symm hs))))

/-- A full-warp shuffle extends the execution when its batch preserves the assumptions. -/
theorem shfl_counted_extension_with_assumptions (hX : Consistent L K A mem0 X)
    (hb : L.block % 32 = 0)
    {g pc : Nat} {m : ShflMode} (a : Nat → Value) (b c : Nat → Nat) (hg : g < L.threads)
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Launched L X h)
    (hrel : ∀ h, SameWarp L g h → Released L X h)
    (hrun : ∀ h, SameWarp L g h → ∀ recv ok, ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧
      EStep K A L h t1 ⟨pc, .shfl m (a h) (b h) (c h) recv ok⟩ o)
    (hasm : ∀ asm ∈ A, asm.wf L mem0 (X.appendLanes (warpThreads L g) (fun h =>
      let source := shflSource m (laneOf L h) (b h) (c h)
      ⟨pc, .shfl m (a h) (b h) (c h) (a (h - laneOf L h + source.1)) source.2⟩))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  let src : Nat → Nat := fun h => h - laneOf L h + (shflSource m (laneOf L h) (b h) (c h)).1
  let ev : Nat → Event := fun h =>
    ⟨pc, .shfl m (a h) (b h) (c h) (a (src h)) (shflSource m (laneOf L h) (b h) (c h)).2⟩
  let n := (X.tr g).countP Execution.isShfl
  have hmw {h : Nat} : h ∈ warpThreads L g ↔ SameWarp L g h := mem_warpThreads
  have hlive : ∀ x, SameWarp L g x → ∀ n, ¬ ShflExited X x n := by
    rintro x hx n ⟨k, pce, hex, -⟩
    obtain ⟨t, -, -, hr, -⟩ := hrun x hx (a x) false
    exact hr.no_exit hex
  have hcnt {h : Nat} (hs : SameWarp L g h) : (X.tr h).countP Execution.isShfl = n :=
    (shfl_count_eq hX hs hlive).symm
  have hlane (h : Nat) : laneOf L h < 32 := Nat.mod_lt _ (by decide)
  have hsrc {h : Nat} (hs : SameWarp L g h) : SameWarp L g (src h) :=
    sameWarp_trans hs (sameWarp_lane hb hs.1.2.1 (shflSource_lt m (hlane h) _ _)).1
  -- the shuffles of the extension: the old ones and one new instance, number `n`
  have hnewK {h n' : Nat} (hs : SameWarp L g h) :
      (X.appendLanes (warpThreads L g) ev).ShflK (h, (X.tr h).length) n' ↔ n' = n := by
    have hk : ((X.appendLanes (warpThreads L g) ev).tr h).take (X.tr h).length = X.tr h := by
      rw [appendLanes_take (i := (h, (X.tr h).length)) le_rfl, List.take_length]
    constructor
    · rintro ⟨-, hc⟩
      simp only at hc
      rw [hk, hcnt hs] at hc
      exact hc.symm
    · rintro rfl
      exact ⟨⟨_, _, _, _, _, _, _, appendLanes_get_new (hmw.mpr hs)⟩, by
        simp only; rw [hk, hcnt hs]⟩
  have hshfl : ShflOk L (X.appendLanes (warpThreads L g) ev) := by
    intro h i n' pc' m' a' b' c' recv ok hget hk
    rcases appendLanes_get_cases hget with ⟨hio, hx⟩ | ⟨hh, hi, hq⟩
    · obtain ⟨h2, hsrc'⟩ :=
        hX.shfl h i n' pc' m' a' b' c' recv ok hx ((appendLanes_shflK_old hio).mp hk)
      refine ⟨h2, ?_⟩
      rcases hsrc' with ⟨j, p', b'', c'', r', o', h3, h4⟩ | hx'
      · exact .inl ⟨j, p', b'', c'', r', o',
          (appendLanes_shflK_old (len_of_get h4)).mpr h3,
          Execution.le_get le_appendLanes h4⟩
      · exact .inr (Execution.shflExited_mono le_appendLanes hx')
    · simp only [ev, Event.mk.injEq, Kind.shfl.injEq] at hq
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hq
      have hs := hmw.mp hh
      simp only at hi
      subst hi
      have hn' : n' = n := (hnewK hs).mp hk
      subst hn'
      exact ⟨rfl, .inl ⟨(X.tr (src h)).length, _, b (src h), c (src h), _, _,
        (hnewK (hsrc hs)).mpr rfl, appendLanes_get_new (hmw.mpr (hsrc hs))⟩⟩
  -- every lane of the warp has its shuffle of the new instance (DEP-ORDER)
  have hready : ∀ h ∈ warpThreads L g,
      Ready L (X.appendLanes (warpThreads L g) ev) (h, (X.tr h).length) := by
    intro h hh nd hn
    simp only [Needs, appendLanes_get_new hh, KindNeeds, maskNeeds, Option.bind_some, ev,
      shflClass, List.mem_map, List.mem_filter, List.mem_range] at hn
    obtain ⟨l, ⟨hl, -⟩, rfl⟩ := hn
    have hs := hmw.mp hh
    obtain ⟨hw, -⟩ := sameWarp_lane hb hs.1.2.1 hl
    have hs' : SameWarp L g (warpLane L h l) := sameWarp_trans hs hw
    have hat {x : Nat} (hx : SameWarp L g x) :
        (X.appendLanes (warpThreads L g) ev).MaskAt shflClass (x, (X.tr x).length) (2 ^ 32 - 1)
          n m :=
      ⟨(maskK_shflClass _ _ _ _).mpr ⟨rfl, (hnewK hx).mpr rfl⟩, _, _,
        appendLanes_get_new (hmw.mpr hx), rfl, rfl⟩
    refine ⟨.thread (warpLane L h l, (X.tr (warpLane L h l)).length),
      ⟨_, appendLanes_get_new (hmw.mpr hs')⟩, _, rfl, ?_⟩
    exact ⟨sameWarp_symm hw, _, n, m, hat hs, .inl (hat hs')⟩
  apply appendLanes_counted_extension (ev := ev) hX (warpThreads_nodup g) (warpThreads_ne_nil hg)
    (fun h hh => (hmw.mp hh).1.2.1) (fun _ _ => trivial) (fun h hh => hst h (hmw.mp hh))
    (fun h hh => hrel h (hmw.mp hh)) (fun h hh => hrun h (hmw.mp hh) _ _)
  · intro h hh j hj hm
    rcases hm with ⟨p, p', m1, i, l, l', hi, -⟩ | ⟨m1, i, ⟨p, hi⟩, -⟩ |
      ⟨hs, n', hk, hkj⟩ | hv
    · rw [appendLanes_get_new hh] at hi
      simp [ev] at hi
    · rw [appendLanes_get_new hh] at hi
      simp [ev] at hi
    · have hn' := (hnewK (hmw.mp hh)).mp hk
      subst hn'
      have hx := (appendLanes_shflK_old hj).mp hkj
      have := ShflK.lt_count hx
      rw [hcnt (sameWarp_trans (hmw.mp hh) hs)] at this
      exact Nat.lt_irrefl _ this
    · exact appendLanes_not_voteWait hh rfl (by simp [ev]) hv
  · exact hready
  · exact hshfl
  · exact appendLanes_electOk_of_not_elect hX (fun _ _ _ _ _ h => by cases h)
  · exact appendLanes_warpBarOk_of_not_warpBar hX (fun _ _ _ _ h => by cases h)
  · exact hasm

/-- **A whole warp performs a shuffle**: a counted extension. -/
theorem shfl_counted_extension (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0)
    {g pc : Nat} {m : ShflMode} (a : Nat → Value) (b c : Nat → Nat) (hg : g < L.threads)
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Launched L X h)
    (hrel : ∀ h, SameWarp L g h → Released L X h)
    (hrun : ∀ h, SameWarp L g h → ∀ recv ok, ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧
      EStep K A L h t1 ⟨pc, .shfl m (a h) (b h) (c h) recv ok⟩ o)
    (hasm : ∀ ev, (∀ h, (ev h).kind.readsMem = false) →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes (warpThreads L g) ev)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  shfl_counted_extension_with_assumptions hX hb a b c hg hst hrel hrun (hasm _ fun _ => rfl)

end
end PTX.Step
