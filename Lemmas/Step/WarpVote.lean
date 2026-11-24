-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpBatch
public import Lemmas.Step.WarpLanes
public import Lemmas.Protocol.CountNth
public import Lemmas.Flow.ElectActor
public import Lemmas.Step.ExitLast

@[expose] public section

/-! # A ballot performed by a whole warp

A proof tool. The lanes of a warp that have not exited have made equally many votes with a member
mask naming all of them (`vote_count_eq`): every vote has returned, so each lane of its mask has its
vote of the same instance (DEP-ORDER, DEP-WARP-INSTANCE). When every thread of `g`'s warp can
perform the ballot at `pc` with member mask `mask` (naming every lane) and its own predicate `a h`,
in a CTA whose size is a multiple of 32, the warp performs one instance: every lane receives the
ballot whose bit of each lane is that lane's predicate (`warpBallot`, THREAD-VOTE, DEP-WARP-VOTE).
This is a counted extension (`vote_counted_extension`). -/

namespace PTX.Step
open PTX AsyncCopy Classical
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- The ballot of `g`'s warp when each thread `h` contributes `a h`: bit `lane` is the
predicate of lane `lane` of the warp. -/
def warpBallot (L : Launch) (g : Nat) (a : Nat → Bool) : BitVec 32 :=
  (BitVec.ofBoolListLE ((List.range 32).map fun lane => a (g - laneOf L g + lane))).setWidth 32

/-- The bit of a lane of the warp in the warp's ballot is that lane's predicate. -/
theorem warpBallot_getLsbD (hb : L.block % 32 = 0) {g h : Nat} (hg : g < L.threads)
    (hs : SameWarp L g h) (a : Nat → Bool) : (warpBallot L g a).getLsbD (laneOf L h) = a h := by
  have hl : laneOf L h < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨hw, hla⟩ := sameWarp_lane hb hg hl
  have heq : g - laneOf L g + laneOf L h = h :=
    sameWarp_eq_of_lane_eq (sameWarp_trans (sameWarp_symm hw) hs) (by rw [hla])
  rw [warpBallot, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]
  simp [hl, heq]

/-- The number of events of class `c` with member mask `m` of thread `h`. -/
def maskCount {Q V : Type} (c : Kind → Option (WarpPart Q V)) (X : Execution) (h m : Nat) : Nat :=
  (X.tr h).countP fun ev => (c ev.kind).any (·.mask == m)

/-- An ordinal of a masked collective is below the thread's number of such events. -/
theorem MaskK.lt_count {Q V : Type} {c : Kind → Option (WarpPart Q V)} {e : EvId} {m n : Nat}
    (h : X.MaskK c e m n) : n < maskCount c X e.1 m := by
  obtain ⟨⟨ev, p, hs, hc, hm⟩, hk⟩ := h
  have hlt := len_of_get hs
  have hsplit := List.take_append_drop e.2 (X.tr e.1)
  have hd : ((X.tr e.1).drop e.2).countP (fun ev => (c ev.kind).any (·.mask == m)) ≥ 1 := by
    have hx : (X.tr e.1)[e.2]? = some ev := hs
    rw [List.getElem?_eq_getElem hlt] at hx
    rw [List.drop_eq_getElem_cons hlt, List.countP_cons, Option.some.inj hx]
    simp [hc, hm]
  unfold maskCount
  rw [← hsplit, List.countP_append, hk]
  omega

/-- A thread with more than `n` events of class `c` with member mask `m` has its `n`-th one. -/
theorem exists_maskK {Q V : Type} {c : Kind → Option (WarpPart Q V)} {g m n : Nat}
    (h : n + 1 ≤ maskCount c X g m) : ∃ j, X.MaskK c (g, j) m n := by
  obtain ⟨j, x, hx, hp, hc⟩ := MbarRing.Slot.exists_nth_countP _ h
  cases hcx : c x.kind with
  | none => simp [hcx] at hp
  | some p => exact ⟨j, ⟨x, p, hx, hcx, by simpa [hcx] using hp⟩, hc⟩

/-- A vote of `X` has, in every lane of its warp that its member mask names, the vote of the same
instance, or that lane has exited: a vote has returned, so its needs are filled (DEP-ORDER,
DEP-WARP-INSTANCE). -/
theorem vote_lane_of_ready (hX : Consistent L K A mem0 X) {g i m n : Nat}
    (hk : X.MaskK voteClass (g, i) m n) {h : Nat} (hs : SameWarp L g h)
    (hbit : m.testBit (laneOf L h) = true) :
    (∃ j, X.MaskK voteClass (h, j) m n) ∨ ∃ k pc, X.get (h, k) = some ⟨pc, .exit⟩ := by
  obtain ⟨⟨⟨pc, k⟩, p, hget, hc, rfl⟩, hcnt⟩ := hk
  have hneeds : Needs L X (g, i) = maskNeeds L voteClass X (g, i) := by
    simp only [Needs, hget]
    cases k <;> simp_all [voteClass, KindNeeds]
  have hr : Ready L X (g, i) := hX.dependency.ready _ (by
    simp only [Returned, hget]
    cases k <;> simp_all [voteClass, Kind.resume])
  have hl : laneOf L h < 32 := Nat.mod_lt _ (by decide)
  have hn := hr _ (hneeds ▸ maskNeeds_mem L voteClass X (g, i) hget hc hl hbit)
  obtain ⟨-, -, j, rfl, -, m', n', q, hat, hx⟩ := hn
  rw [warpLane_of_sameWarp hs] at hx
  obtain ⟨⟨ev', p', hg', hc', hm'⟩, hk'⟩ := hat.1
  rw [hget] at hg'
  cases hg'
  rw [hc] at hc'
  cases hc'
  subst hm'
  have hn' : n' = n := hk'.symm.trans hcnt
  subst hn'
  rcases hx with hx | ⟨-, ⟨pc', he⟩, -⟩
  · exact .inl ⟨j, hx.1⟩
  · exact .inr ⟨j, pc', he⟩

/-- **The lanes of a warp have made equally many votes with a member mask that names all of
them**, when no lane of the warp has exited. -/
theorem vote_count_eq (hX : Consistent L K A mem0 X) {g h mask : Nat} (hs : SameWarp L g h)
    (hlive : ∀ x, SameWarp L g x → ∀ k pc, X.get (x, k) ≠ some ⟨pc, .exit⟩)
    (hmask : ∀ x, SameWarp L g x → mask.testBit (laneOf L x) = true) :
    maskCount voteClass X g mask = maskCount voteClass X h mask := by
  have le_of {g h : Nat} (hs : SameWarp L g h) (hh : ∀ k pc, X.get (h, k) ≠ some ⟨pc, .exit⟩)
      (hm : mask.testBit (laneOf L h) = true) :
      maskCount voteClass X g mask ≤ maskCount voteClass X h mask := by
    by_contra hlt
    obtain ⟨j, hj⟩ := exists_maskK (X := X) (c := voteClass) (g := g) (m := mask)
      (n := maskCount voteClass X h mask) (by omega)
    rcases vote_lane_of_ready hX hj hs hm with ⟨j', hk'⟩ | ⟨k, pc, he⟩
    · exact Nat.lt_irrefl _ (MaskK.lt_count hk')
    · exact hh k pc he
  have hgg : SameWarp L g g := sameWarp_trans hs (sameWarp_symm hs)
  exact Nat.le_antisymm (le_of hs (hlive h hs) (hmask h hs))
    (le_of (sameWarp_symm hs) (hlive g hgg) (hmask g hgg))

/-- **A whole warp performs a ballot**: a counted extension. -/
theorem vote_counted_extension (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0)
    {g pc mask : Nat} (a : Nat → Bool) (hg : g < L.threads)
    (hmem : ∀ h, SameWarp L g h → mask.testBit (laneOf L h) = true)
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Launched L X h)
    (hrel : ∀ h, SameWarp L g h → Released L X h)
    (hrun : ∀ h, SameWarp L g h → ∀ ballot, ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧ EStep K A L h t1 ⟨pc, .vote mask (a h) ballot⟩ o)
    (hasm : ∀ ev, (∀ h, (ev h).kind.readsMem = false) →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes (warpThreads L g) ev)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  let ev : Nat → Event := fun h => ⟨pc, .vote mask (a h) (warpBallot L g a)⟩
  let cnt := maskCount voteClass X g mask
  have hmw {h : Nat} : h ∈ warpThreads L g ↔ SameWarp L g h := mem_warpThreads
  have le : X.le (X.appendLanes (warpThreads L g) ev) := le_appendLanes
  have ha := appendLanes_threadAppend (X := X) (ds := warpThreads L g) (ev := ev)
  have hlive : ∀ x, SameWarp L g x → ∀ k pc, X.get (x, k) ≠ some ⟨pc, .exit⟩ := by
    intro x hx k pce hex
    obtain ⟨t, -, -, hr, -⟩ := hrun x hx 0
    exact hr.no_exit hex
  have hcnt {h : Nat} (hs : SameWarp L g h) : maskCount voteClass X h mask = cnt :=
    (vote_count_eq hX hs hlive hmem).symm
  have hlane (h : Nat) : laneOf L h < 32 := Nat.mod_lt _ (by decide)
  have hthr {v : EvId} {q : Event} (hv : X.get v = some q) : v.1 < L.threads := by
    by_contra hn
    have := len_of_get hv
    rw [hX.outside v.1 (by omega)] at this
    simp at this
  -- the new ballots are the instance of ordinal `cnt` of the member mask `mask`
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
        .ballot := by
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
  have hvote : VoteOk L (X.appendLanes (warpThreads L g) ev) := by
    intro g' i n' pc' m' a' bal hget hk part hp lane hl
    rcases appendLanes_get_cases hget with ⟨hio, hx⟩ | ⟨hh, hi, hq⟩
    · exact hX.vote g' i n' pc' m' a' bal hx (Execution.maskK_of_le le hx hk) part
        (hinstX hio (Execution.maskK_of_le le hx hk) hp) lane hl
    · simp only [ev, Event.mk.injEq, Kind.vote.injEq] at hq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hq
      have hs := hmw.mp hh
      simp only at hi
      subst hi
      obtain ⟨-, rfl⟩ := hnewK hs hk
      obtain ⟨hsx, hlx⟩ := sameWarp_lane hb hs.1.2.1 hl
      have hsx' := sameWarp_trans hs hsx
      have hbit := hmem _ hsx'
      rw [hlx] at hbit
      refine ⟨fun b hpb => ?_, fun hf => by rw [hbit] at hf; cases hf⟩
      rcases (hp lane hl).1 hbit with ⟨j, pc'', k, v, hj, hc, hkk, hpv⟩ | ⟨-, hpn⟩
      · rcases appendLanes_get_cases hj with ⟨hjo, -⟩ | ⟨-, hjl, hq⟩
        · exact (hold (v := (_, j)) hsx' hjo hkk).elim
        · simp only [ev, Event.mk.injEq] at hq
          obtain ⟨-, rfl⟩ := hq
          simp only [voteClass, Option.some.injEq, WarpPart.mk.injEq] at hc
          obtain ⟨-, -, rfl⟩ := hc
          rw [hpv] at hpb
          cases hpb
          simpa only [hlx] using warpBallot_getLsbD hb hg hsx' a
      · rw [hpn] at hpb
        cases hpb
  have hvalue : WarpValueOk L (X.appendLanes (warpThreads L g) ev) := by
    have hnot {k : Kind} (hk : ∀ m a b, k ≠ .vote m a b) {v : EvId} {pc' : Nat} :
        (X.appendLanes (warpThreads L g) ev).get v = some ⟨pc', k⟩ → X.get v = some ⟨pc', k⟩ :=
      (appendLanes_get_kind (fun j _ h => hk _ _ _ h.symm)).mp
    obtain ⟨hv, hr, hm, ham⟩ := hX.warpValue
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g' i pc' mode m a' r n hget hk part hp
      have hx := hnot (fun _ _ _ h => by cases h) hget
      have hkx := Execution.maskK_of_le le hx hk
      exact hv g' i pc' mode m a' r n hx hkx part (hinstX (len_of_get hx) hkx hp)
    · intro g' i pc' op signed m a' r n hget hk part hp
      have hx := hnot (fun _ _ _ h => by cases h) hget
      refine hr g' i pc' op signed m a' r n hx (Execution.maskK_of_le le hx hk) part
        (Execution.maskInstance_of_le le (fun v pc'' k w hj hc => ?_) hexit hp)
      exact hnot (fun _ _ _ h => by rw [h] at hc; cases hc) hj
    · intro g' i pc' all wide m a' r p n hget hk part hp
      have hx := hnot (fun _ _ _ h => by cases h) hget
      refine hm g' i pc' all wide m a' r p n hx (Execution.maskK_of_le le hx hk) part
        (Execution.maskInstance_of_le le (fun v pc'' k w hj hc => ?_) hexit hp)
      exact hnot (fun _ _ _ h => by rw [h] at hc; cases hc) hj
    · intro g' i pc' r hget
      exact ham g' i pc' r (hnot (fun _ _ _ h => by cases h) hget)
  -- every lane of the member mask has its ballot of the new instance (DEP-ORDER)
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
    exact ⟨sameWarp_symm hw, _, cnt, .ballot, hatNew hs, .inl (hatNew hs')⟩
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
  · exact hasm ev fun _ => rfl

end
end PTX.Step
