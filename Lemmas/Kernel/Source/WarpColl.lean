-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Followed
public import Lemmas.Kernel.FullVote
public import Lemmas.Kernel.Source.Warp
public import Lemmas.Step.WarpLanes
public import Lemmas.Step.WarpShfl
public import Lemmas.Step.WarpVote

@[expose] public section

/-! # The source of a warp collective, for a lane of any warp of any machine family

A proof tool, generic over the kernel (promoted from the tml-fa4 thread frame,
`Proof2/Common/Frame.lean` and `Proof2/Common/Coll.lean`). What a shuffle or a full-mask ballot
of a lane returns comes from the lanes of its warp at the same instance (DEP-WARP-SHFL,
DEP-WARP-VOTE). The instance is fixed by the count of the lane's earlier collectives of its kind.

* **Order.** The warp collectives are the shuffles and the full-mask ballots (`isColl`); the order
  of the never-dropped induction is by the collectives up to and including an event (`collUpTo`,
  with `Frame.lexOrder`). The source lanes of a collective are followed up to it, at every
  position with at most the collectives before the event (`GoodUpTo`, from `upTo_of_lt` or
  `upTo_of_prev`): their earlier positions have fewer collectives.
* **Sources.** A role gives three position facts about the lanes of its warp in the CTA, each as
  "this cannot happen" at a followed position: a ballot past at most the shuffles and exactly the
  ballots of the current state (at a shuffle), a shuffle past at most the ballots and exactly the
  shuffles (at a ballot), and a return past at most both counts. From them `shfl_src` finds the
  source lane's shuffle of the instance and `vote_src` every lane's ballot of the instance, each
  at a followed position with the counts of the instance. Which site the source lane is at, and
  what it sends, is the role's (its reference invariant there).

The machine family `C` is any family of sound site machines, the warp is the Core warp index
`g % L.block / 32` (`InWarp`), and the only launch fact used is that a block is whole warps
(`L.block % 32 = 0`). -/

namespace PTX.Frame
open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {C : (g : Nat) → Flow.Code K A L g} {g : Nat}

/-! ### The order by the warp collectives -/

/-- The warp collectives: shuffles and full-mask ballots. -/
def isColl (e : Event) : Bool := Execution.isShfl e || voteWith (2 ^ 32 - 1) e

/-- The warp collectives up to and including an event: the measure of the induction. -/
def collUpTo (X : Execution) (i : EvId) : Nat := ((X.tr i.1).take (i.2 + 1)).countP isColl

theorem isShfl_not_vote {e : Event} (h : Execution.isShfl e = true) :
    voteWith (2 ^ 32 - 1) e = false := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [Execution.isShfl, voteWith, voteClass]

/-- A ballot with the full mask is a collective. -/
theorem isColl_vote {pc : Nat} {a : Bool} {b : BitVec 32} :
    isColl ⟨pc, .vote (2 ^ 32 - 1) a b⟩ = true := by
  simp [isColl]

theorem countColl (es : List Event) :
    es.countP isColl = es.countP Execution.isShfl + es.countP (voteWith (2 ^ 32 - 1)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hx := @isShfl_not_vote e
    simp only [List.countP_cons, ih, isColl]
    by_cases hs : Execution.isShfl e = true
    · simp only [hs, hx hs, Bool.or_false, ↓reduceIte, Bool.false_eq_true]
      omega
    · simp only [Bool.not_eq_true] at hs
      by_cases hv : voteWith (2 ^ 32 - 1) e = true
      · simp only [hs, hv, Bool.false_or, ↓reduceIte, Bool.false_eq_true]
        omega
      · simp only [Bool.not_eq_true] at hv
        simp only [hs, hv, Bool.false_or, ↓reduceIte, Bool.false_eq_true]
        omega

/-- The lanes of warp `w`: launched threads whose Core warp index in the CTA is `w`. -/
def InWarp (L : Launch) (w g : Nat) : Prop := g < L.threads ∧ g % L.block / 32 = w

/-- **The lanes of the warp of a lane of warp `w`**: lane `i` of the warp is launched, of warp
`w`, in the same CTA, has lane index `i`, and is in the same warp. -/
theorem lane_facts {w : Nat} (hb : L.block % 32 = 0) (hg : g < L.threads)
    (hw : g % L.block / 32 = w) {i : Nat} (hi : i < 32) :
    let h := g - laneOf L g + i
    h < L.threads ∧ h % L.block / 32 = w ∧ h / L.block = g / L.block ∧
      laneOf L h = i ∧ SameWarp L g h := by
  intro h
  obtain ⟨hs, hl⟩ := Step.sameWarp_lane hb hg hi
  obtain ⟨⟨-, hh, hc⟩, hwarp⟩ := hs
  exact ⟨hh, hwarp ▸ hw, hc.symm, hl, ⟨⟨hg, hh, hc⟩, hwarp⟩⟩

variable (C) in
/-- The lanes of warp `w` are followed with `J` at the positions with at most `n` collectives
before them. -/
def GoodUpTo (J : ∀ g, (C g).D → Prop) (X : Execution) (w n : Nat) : Prop :=
  ∀ h j, InWarp L w h → ((X.tr h).take j).countP isColl ≤ n → FollowedAt C J X h j

/-- **The source lanes of a collective are followed up to it**: with the order by the
collectives, every position of a lane of warp `w` with at most the collectives before the event
is followed. Only the lanes' events with fewer collectives up to them than the event are used. -/
theorem upTo_of_lt {J : ∀ g, (C g).D → Prop} {w k : Nat} {e : Event}
    (hinit : ∀ g, J g (C g).init) (he : X.get (g, k) = some e) (hc : isColl e = true)
    (hprev : ∀ j, collUpTo X j < collUpTo X (g, k) → InWarp L w j.1 → ¬ Bad C J X j) :
    GoodUpTo C J X w (((X.tr g).take k).countP isColl) := by
  intro h j hh hj
  refine followedAt_of_noBad (hinit h) j fun i hi => hprev (h, i) ?_ hh
  have h1 := countP_take_mono isColl (X.tr h) (show i + 1 ≤ j by omega)
  have h2 : ((X.tr g).take (k + 1)).countP isColl = ((X.tr g).take k).countP isColl + 1 := by
    rw [List.take_add_one, show (X.tr g)[k]? = some e from he]
    simp [List.countP_append, hc]
  simp only [collUpTo]
  omega

/-- `upTo_of_lt` with the lexicographic order of `Frame.inductive_lex`. -/
theorem upTo_of_prev {J : ∀ g, (C g).D → Prop} {w k : Nat} {e : Event}
    (hinit : ∀ g, J g (C g).init) (he : X.get (g, k) = some e) (hc : isColl e = true)
    (hprev : ∀ j, lexOrder (collUpTo X) j (g, k) → InWarp L w j.1 → ¬ Bad C J X j) :
    GoodUpTo C J X w (((X.tr g).take k).countP isColl) :=
  upTo_of_lt hinit he hc fun j hj => hprev j (.inl hj)

/-- A followed position before an event that is no undefined behaviour is a state that holds the
invariant. -/
theorem good_state {J : ∀ g, (C g).D → Prop} (hC : ∀ g < L.threads, (C g).Sound)
    (hX : Consistent L K A mem0 X) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩)
    (hG : FollowedAt C J X g j) : ∃ d, stateAt C X g j = some (some d) ∧ J g d := by
  rcases fired hC hX he with ⟨σ, o, hσ, -⟩ | ⟨-, pc, f, rfl⟩
  · cases σ with
    | none => exact absurd hσ hG.1
    | some σ => exact ⟨σ, hσ, hG.2 σ hσ⟩
  · exact absurd rfl (hub pc f)

/-! ### The sources -/

/-- **The source of a shuffle of a lane of warp `w`**: the source lane made the shuffle of the
same instance, sending the received value, from a followed position with the instance's shuffle
count and at most the current ballot count. -/
theorem shfl_src {J : ∀ g, (C g).D → Prop} {w : Nat}
    (hb : L.block % 32 = 0) (hX : Consistent L K A mem0 X)
    (hg : g < L.threads) (hw : g % L.block / 32 = w) {k pc ns nv : Nat} {mode : ShflMode}
    {a recv : Value} {b c : Nat} {ok : Bool}
    (he : X.get (g, k) = some ⟨pc, .shfl mode a b c recv ok⟩)
    (hcs : ((X.tr g).take k).countP Execution.isShfl = ns) (IH : GoodUpTo C J X w (ns + nv))
    (hV : ∀ h j e, InWarp L w h → h / L.block = g / L.block → X.get (h, j) = some e →
      voteWith (2 ^ 32 - 1) e = true → FollowedAt C J X h j →
      cnt X Execution.isShfl h j ≤ ns → cnt X (voteWith (2 ^ 32 - 1)) h j = nv → False)
    (hE : ∀ h j pc, InWarp L w h → h / L.block = g / L.block → X.get (h, j) = some ⟨pc, .exit⟩ →
      FollowedAt C J X h j →
      cnt X Execution.isShfl h j ≤ ns → cnt X (voteWith (2 ^ 32 - 1)) h j ≤ nv → False) :
    ∃ j pc' b' c' r' o',
      X.get (g - laneOf L g + (shflSource mode (laneOf L g) b c).1, j) =
        some ⟨pc', .shfl mode recv b' c' r' o'⟩ ∧
      FollowedAt C J X (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) j ∧
      cnt X Execution.isShfl (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) j = ns ∧
      cnt X (voteWith (2 ^ 32 - 1)) (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) j ≤
        nv := by
  have hK : X.ShflK (g, k) ns := ⟨⟨pc, mode, a, b, c, recv, ok, he⟩, hcs⟩
  obtain ⟨-, hsrc⟩ := hX.shfl g k ns pc mode a b c recv ok he hK
  have hsl := Step.shflSource_lt mode (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) b c
  obtain ⟨hsT, hsW, hsC, -, -⟩ := lane_facts hb hg hw hsl
  have votes : ∀ i, cnt X Execution.isShfl
      (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) i ≤ ns →
      cnt X (voteWith (2 ^ 32 - 1)) (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) i ≤
        nv :=
    fun i hi => coll_le (S := Execution.isShfl)
      (fun j _ hn => IH _ j ⟨hsT, hsW⟩ (by simp only [cnt] at hn; rw [countColl]; omega))
      (fun j0 e0 he0 hv0 hG hc0 => by
        by_contra hle
        exact hV _ j0 e0 ⟨hsT, hsW⟩ hsC he0 hv0 hG (by omega) hc0) hi
  rcases hsrc with ⟨j, pc', b', c', r', o', hK', hj⟩ | ⟨kx, pcx, hx, hcx⟩
  · have hvj := votes j (by simp only [cnt]; rw [hK'.2])
    simp only [cnt] at hvj
    exact ⟨j, pc', b', c', r', o', hj, IH _ j ⟨hsT, hsW⟩ (by rw [countColl, hK'.2]; omega),
      hK'.2, hvj⟩
  · exfalso
    have hvx := votes kx hcx
    simp only [cnt] at hvx
    exact hE _ kx pcx ⟨hsT, hsW⟩ hsC hx (IH _ kx ⟨hsT, hsW⟩ (by rw [countColl]; omega)) hcx hvx

set_option maxHeartbeats 1000000 in
/-- **The sources of a ballot of a lane of warp `w`**: the bit of every lane is its predicate at
the ballot of the same instance, where the role's fact `P` holds (`hB`: a full-mask vote of a
lane of the warp at a followed position with the instance's ballot count and at most the current
shuffle count is a ballot whose predicate satisfies `P`). -/
theorem vote_src {J : ∀ g, (C g).D → Prop} {w : Nat} {P : Nat → Bool → Prop}
    (hb : L.block % 32 = 0) (hX : Consistent L K A mem0 X)
    (hg : g < L.threads) (hw : g % L.block / 32 = w) {k pc ns nv : Nat} {a : Bool}
    {bv : BitVec 32} (he : X.get (g, k) = some ⟨pc, .vote (2 ^ 32 - 1) a bv⟩)
    (hcv : ((X.tr g).take k).countP (voteWith (2 ^ 32 - 1)) = nv)
    (IH : GoodUpTo C J X w (ns + nv))
    (hS : ∀ h j e, InWarp L w h → h / L.block = g / L.block → X.get (h, j) = some e →
      Execution.isShfl e = true → FollowedAt C J X h j →
      cnt X (voteWith (2 ^ 32 - 1)) h j ≤ nv → cnt X Execution.isShfl h j = ns → False)
    (hE : ∀ h j pc, InWarp L w h → h / L.block = g / L.block → X.get (h, j) = some ⟨pc, .exit⟩ →
      FollowedAt C J X h j →
      cnt X Execution.isShfl h j ≤ ns → cnt X (voteWith (2 ^ 32 - 1)) h j ≤ nv → False)
    (hB : ∀ h j e, InWarp L w h → h / L.block = g / L.block → X.get (h, j) = some e →
      voteWith (2 ^ 32 - 1) e = true → FollowedAt C J X h j →
      cnt X Execution.isShfl h j ≤ ns → cnt X (voteWith (2 ^ 32 - 1)) h j = nv →
      ∃ pc' a' b', e = ⟨pc', .vote (2 ^ 32 - 1) a' b'⟩ ∧ P h a') :
    ∀ i < 32, P (g - laneOf L g + i) (bv.getLsbD i) := by
  have hK : X.MaskK voteClass (g, k) (2 ^ 32 - 1) nv :=
    ⟨⟨_, ⟨2 ^ 32 - 1, .ballot, a⟩, he, rfl, rfl⟩, hcv⟩
  have lane : ∀ i < 32, ∃ j pc' a' b', X.get (g - laneOf L g + i, j) =
        some ⟨pc', .vote (2 ^ 32 - 1) a' b'⟩ ∧
      X.MaskK voteClass (g - laneOf L g + i, j) (2 ^ 32 - 1) nv ∧ P (g - laneOf L g + i) a' := by
    intro i hi
    obtain ⟨hiT, hiW, hiC, hiL, hiS⟩ := lane_facts hb hg hw hi
    have hbit : (2 ^ 32 - 1 : Nat).testBit (laneOf L (g - laneOf L g + i)) = true := by
      rw [hiL, Nat.testBit_two_pow_sub_one]; simpa using hi
    have shfls : ∀ j, cnt X (voteWith (2 ^ 32 - 1)) (g - laneOf L g + i) j ≤ nv →
        cnt X Execution.isShfl (g - laneOf L g + i) j ≤ ns := fun j hj =>
      coll_le (S := voteWith (2 ^ 32 - 1))
        (fun j _ hn => IH _ j ⟨hiT, hiW⟩ (by simp only [cnt] at hn; rw [countColl]; omega))
        (fun j1 e1 he1 hs1 hG hc1 => by
          by_contra hle
          exact hS _ j1 e1 ⟨hiT, hiW⟩ hiC he1 hs1 hG (by omega) hc1) hj
    by_cases hA : ∃ j, X.MaskK voteClass (g - laneOf L g + i, j) (2 ^ 32 - 1) nv
    · obtain ⟨j, ⟨ej, pj, hej, hcj, hmj⟩, hcnt⟩ := hA
      have hcnt' : cnt X (voteWith (2 ^ 32 - 1)) (g - laneOf L g + i) j = nv := hcnt
      have hfv : voteWith (2 ^ 32 - 1) ej = true := by simp [voteWith, hcj, hmj]
      have hsj := shfls j hcnt'.le
      have hG := IH _ j ⟨hiT, hiW⟩ (by
        simp only [cnt] at hsj hcnt'; rw [countColl]; omega)
      obtain ⟨pc', a', b', rfl, hP⟩ := hB _ j ej ⟨hiT, hiW⟩ hiC hej hfv hG hsj hcnt'
      exact ⟨j, pc', a', b', hej, ⟨⟨_, _, hej, hcj, hmj⟩, hcnt⟩, hP⟩
    · exfalso
      obtain ⟨kx, pcx, hx⟩ := (Step.vote_lane_of_ready hX hK hiS hbit).resolve_left hA
      have hvx : ((X.tr (g - laneOf L g + i)).take kx).countP (voteWith (2 ^ 32 - 1)) ≤ nv := by
        by_contra hgt
        obtain ⟨j0, e0, hj0, he0', hv0, hc0⟩ := exists_nthEv (X := X)
          (p := voteWith (2 ^ 32 - 1)) (g := g - laneOf L g + i) (k := kx) (n := nv) (by omega)
        apply hA
        refine ⟨j0, ?_, hc0⟩
        simp only [voteWith, Option.any_eq_true, beq_iff_eq] at hv0
        obtain ⟨q, hq, hqm⟩ := hv0
        exact ⟨e0, q, he0', hq, hqm⟩
      have hsx := shfls kx hvx
      exact hE _ kx pcx ⟨hiT, hiW⟩ hiC hx (IH _ kx ⟨hiT, hiW⟩ (by
        simp only [cnt] at hsx; rw [countColl]; omega)) hsx hvx
  choose j pc' a' b' hget hmk hP using lane
  let part : Nat → Option Bool := fun i => if hi : i < 32 then some (a' i hi) else none
  have hMI : MaskInstance L voteClass X g (2 ^ 32 - 1) nv .ballot part := by
    intro i hi
    refine ⟨fun _ => .inl ⟨j i hi, pc' i hi, _, a' i hi, hget i hi, rfl, hmk i hi, by
      simp [part, hi]⟩, fun hb => ?_⟩
    rw [Nat.testBit_two_pow_sub_one] at hb
    simp at hb; omega
  intro i hi
  rw [(hX.vote g k nv pc _ _ bv he hK part hMI i hi).1 (a' i hi) (by simp [part, hi])]
  exact hP i hi

end
end PTX.Frame
