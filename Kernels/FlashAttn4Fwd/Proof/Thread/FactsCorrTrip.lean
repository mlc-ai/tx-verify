-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrRescale
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin
public import Lemmas.Flow.VoteMask

@[expose] public section

/-! # The correction warps' rescale of a trip (`CorrValues.trip`)

Past loop trip `t` of item `j` of stage `st` (more than `n j + t + 1` P-ready arrivals of the
stage), the thread made the trip's O-free arrival (the arrival with `n j + t + 1` earlier ones,
`exists_nthEv`; by its credit it is the trip's, `trip_credit_inj`). There the run invariant names
the read of `α` after the trip's sync (`Counts.rsSt`) and the trip's vote, whose predicate is
`α < 1` (`Counts.rsVote`); when the ballot was not zero, every chunk's store of the trip
(`Counts.rsWrote` through `Counts.rsVote`). The thread's own bit of the ballot is its predicate
(`VoteOk`, with the full member mask, `fires_vote_mask`, and the thread not exited before its
later events). On a canonical word reading as `α` the predicate is `α < 1` (`ltOne_fin`), so
`α < 1` makes the ballot nonzero and every column of the row is stored; when the thread's earlier
loads returned single-precision floats and its earlier reads canonical words, each stored value
is a single-precision product (`rst_operands`, `rs_f32`). With the rescale and final values this
is the correction part of `ValueFacts` (`ValueFacts_corr`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A lane of the member mask of a ballot in the warp of thread `g`: it takes part in the
`n`-th ballot instance of mask `m` with input `v`. -/
def BallotPart (L : Launch) (X : Execution) (g m n l : Nat) (v : Bool) : Prop :=
  ∃ j pc k, X.get (g - laneOf L g + l, j) = some ⟨pc, k⟩ ∧
    voteClass k = some ⟨m, .ballot, v⟩ ∧ X.MaskK voteClass (g - laneOf L g + l, j) m n

/-- Every lane of the member mask of a ballot takes part in its instance or exited before it: a
ballot has returned, so its needs are filled (DEP-ORDER, DEP-WARP-INSTANCE). -/
theorem ballot_lane {K : Kernel} {A : List Assumption} (hX : Consistent L K A mem0 X)
    {g v pc m n : Nat} {a : Bool} {b : BitVec 32} (he : X.get (g, v) = some ⟨pc, .vote m a b⟩)
    (hK : X.MaskK voteClass (g, v) m n) {l : Nat} (hl : l < 32) (hm : m.testBit l = true) :
    (∃ v', BallotPart L X g m n l v') ∨ MaskExited voteClass X (g - laneOf L g + l) m n := by
  have hneeds : Needs L X (g, v) = maskNeeds L voteClass X (g, v) := by
    simp only [Needs, he, KindNeeds]
  have hr : Ready L X (g, v) := hX.dependency.ready _ (by simp [Returned, he, Kind.resume])
  have hn := hr _ (hneeds ▸ maskNeeds_mem L voteClass X (g, v) he rfl hl hm)
  obtain ⟨-, -, j, rfl, -, m', n', q, ⟨⟨⟨ev, p, hg, hc, hpm⟩, hk⟩, ev', p', hg', hc', hq⟩, hx⟩ := hn
  rw [he] at hg hg'
  cases hg
  cases hg'
  simp only [voteClass, Option.some.injEq] at hc hc'
  subst hc hc'
  simp only at hpm hq
  subst hpm hq
  have hn' : n' = n := hk.symm.trans hK.2
  subst hn'
  rcases hx with ⟨hk2, ev2, p2, hg2, hc2, hq2⟩ | ⟨-, hx⟩
  · left
    obtain ⟨ev3, p3, hg3, hc3, hm3⟩ := hk2.1
    rw [hg2] at hg3
    cases hg3
    rw [hc2] at hc3
    cases hc3
    obtain ⟨pc2, k2⟩ := ev2
    obtain ⟨m2, q2, v2⟩ := p2
    simp only at hm3 hq2
    subst hm3 hq2
    exact ⟨v2, j, pc2, k2, hg2, hc2, hk2⟩
  · exact .inr ((maskExited_iff voteClass X _ m n').mpr ⟨j, hx⟩)

/-- **A ballot's instance**: every lane of the member mask takes part with an input or exited
before it (`ballot_lane`), so the instance has its inputs. -/
theorem ballot_instance {K : Kernel} {A : List Assumption} (hX : Consistent L K A mem0 X)
    {g v pc m n : Nat} {a : Bool} {b : BitVec 32} (he : X.get (g, v) = some ⟨pc, .vote m a b⟩)
    (hK : X.MaskK voteClass (g, v) m n) :
    ∃ part, MaskInstance L voteClass X g m n .ballot part := by
  classical
  refine ⟨fun l => if h : m.testBit l = true ∧ ∃ v', BallotPart L X g m n l v' then
    some (Classical.choose h.2) else none, fun l hl => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · by_cases hp : ∃ v', BallotPart L X g m n l v'
    · have hc : m.testBit l = true ∧ ∃ v', BallotPart L X g m n l v' := ⟨hm, hp⟩
      obtain ⟨j, pc', k, hg', hc', hk'⟩ := Classical.choose_spec hc.2
      exact .inl ⟨j, pc', k, _, hg', hc', hk', dite_eq_left hc⟩
    · rcases ballot_lane hX he hK hl hm with h | h
      · exact absurd h hp
      · exact .inr ⟨h, dite_eq_right fun hc => hp hc.2⟩
  · exact dite_eq_right fun hc => by rw [hm] at hc; exact Bool.false_ne_true hc.1

/-- **A thread's own bit of its ballot is its predicate**, when its member mask names it. -/
theorem ballot_own {K : Kernel} {A : List Assumption} (hX : Consistent L K A mem0 X)
    {g v pc m : Nat} {a : Bool} {b : BitVec 32} (he : X.get (g, v) = some ⟨pc, .vote m a b⟩)
    (hbit : m.testBit (laneOf L g) = true) : b.getLsbD (laneOf L g) = a := by
  classical
  have hK : X.MaskK voteClass (g, v) m
      (((X.tr g).take v).countP fun ev => (voteClass ev.kind).any (·.mask == m)) :=
    ⟨⟨_, ⟨m, .ballot, a⟩, he, rfl, rfl⟩, rfl⟩
  set n := ((X.tr g).take v).countP fun ev => (voteClass ev.kind).any (·.mask == m)
  have hl32 : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hgl : g - laneOf L g + laneOf L g = g := by
    have : laneOf L g ≤ g := (Nat.mod_le _ _).trans (Nat.mod_le _ _)
    omega
  let part : Nat → Option Bool := fun l =>
    if l = laneOf L g then some a
    else if h : m.testBit l = true ∧ ∃ v', BallotPart L X g m n l v' then
      some (Classical.choose h.2)
    else none
  have hpart : MaskInstance L voteClass X g m n .ballot part := by
    intro l hl
    by_cases hlo : l = laneOf L g
    · subst hlo
      refine ⟨fun _ => .inl ⟨v, pc, _, a, by rw [hgl]; exact he, rfl, by rw [hgl]; exact hK,
        by simp [part]⟩, fun h => by rw [hbit] at h; cases h⟩
    refine ⟨fun hm => ?_, fun hm => by simp [part, hlo, hm]⟩
    by_cases hp : ∃ v', BallotPart L X g m n l v'
    · have hc : m.testBit l = true ∧ ∃ v', BallotPart L X g m n l v' := ⟨hm, hp⟩
      obtain ⟨j, pc', k, hg', hc', hk'⟩ := Classical.choose_spec hc.2
      exact .inl ⟨j, pc', k, _, hg', hc', hk',
        by simp only [part, hlo, ↓reduceIte, dite_eq_left hc]⟩
    · rcases ballot_lane hX he hK hl hm with h | h
      · exact absurd h hp
      · exact .inr ⟨h, by
          simp only [part, hlo, ↓reduceIte]
          exact dite_eq_right fun hc => hp hc.2⟩
  exact (hX.vote g v n pc m a b he hK part hpart _ hl32).1 a (by simp [part])

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- A correction thread's ballot event has the full member mask. -/
theorem corr_vote_mask {g v pc m : Nat} {a : Bool} {b : BitVec 32} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (he : X.get (g, v) = some ⟨pc, .vote m a b⟩) : m = 2 ^ 32 - 1 := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, -, -, -, -, hcode, hf, hev⟩
  · cases hk
  obtain ⟨-, hk⟩ := hev (by simp)
  obtain ⟨site, i, tt, aw, aa, o'⟩ := d
  cases site
  case vote st =>
    fin_cases st
    · obtain rfl := Option.some.inj (hcode.symm.trans Flow.code_vote_0)
      exact fires_vote_mask hf rfl
    · obtain rfl := Option.some.inj (hcode.symm.trans Flow.code_vote_1)
      exact fires_vote_mask hf rfl
  all_goals exfalso
  all_goals simp at hk

/-- **A thread's own bit of its ballot is its predicate.** -/
theorem corr_vote_own {g v pc m : Nat} {a : Bool} {b : BitVec 32} (_hg : g < L.threads)
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (he : X.get (g, v) = some ⟨pc, .vote m a b⟩) :
    b.getLsbD (laneOf L g) = a := by
  have hm := corr_vote_mask hpre hX ht hw hw' he
  have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  exact ballot_own hX he (by rw [hm, Nat.testBit_two_pow_sub_one]; simp [hlane])

/-- **`CorrValues.trip`**: past loop trip `t` of item `j`, the thread read the trip's factor; when
it is below one, the thread rescaled every column of its row. -/
theorem CorrValues_trip {g st j t e : Nat} (hg : g < L.threads) (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (hst : st < 2) (ht1 : t + 1 < kvBlocks P)
    (hge : kvBlocks P * j + t + 2 ≤ pArr L X g st e) :
    ∃ r, ∃ bs : List (Option Byte), r < e ∧
      StatRead L X g st ((kvBlocks P + 1) * j + 1 + t) r bs ∧
      ∀ α : ℝ, F32Read bs α → α < 1 →
        (∀ k < e, ∀ pc a' (vals' : List Value),
          X.get (g, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') →
        (∀ k < e, ∀ pc (ac : Acc) (bs' : List (Option Byte)),
          X.get (g, k) = some ⟨pc, .rd ac bs'⟩ → ∃ x, F32Read bs' x) →
        ∀ d < 128, ∃ y, CorrStored L X g st (kvBlocks P * j + t + 1) d y := by
  have hkv := corr_trips_eq hpre
  rw [← hkv] at ht1 hge ⊢
  -- the trip's O-free arrival
  set m := pReadyBar L (leadCta (ctaOf L g)) st
  obtain ⟨x, ev, hxe, hgx, hpx, hcx⟩ := exists_nthEv (X := X) (g := g) (p := arrivesOn m)
    (n := Correction.trips L * j + t + 1) (k := e) (by unfold pArr at hge; exact hge)
  obtain ⟨epc, ek⟩ := ev
  have hk : ∃ tx cnt rel sc, ek = .arrive m tx cnt rel sc := by
    cases ek <;> simp only [arrivesOn, sourceArrive, Bool.false_eq_true, decide_eq_true_eq] at hpx
    subst hpx
    exact ⟨_, _, _, _, rfl⟩
  obtain ⟨tx, cnt, rel, sc, rfl⟩ := hk
  obtain ⟨-, -, d, -, hc, hi, -, hs⟩ := corr_arrive hpre hX ht hw hw' hgx
  have hpa : arrivals m ((X.tr g).take x) = Correction.trips L * d.i +
      Correction.freePos L st d := by
    rw [show m = Correction.leadLoc L g (144 + 8 * st) from pReadyBar_lead L g st]
    exact hc.free st hst
  have hcx' : arrivals m ((X.tr g).take x) = Correction.trips L * j + t + 1 := hcx
  rcases hs with ⟨a0, -, hm⟩ | ⟨st', -, hm⟩ | ⟨st', hsd, hm⟩
  · simp only [m, Correction.ownLoc, pReadyBar, leadCta, Correction.sb, Loc.mk.injEq] at hm
    omega
  · simp only [m, Correction.ownLoc, pReadyBar, leadCta, Correction.sb, Loc.mk.injEq] at hm
    omega
  have hm' : pReadyBar L (leadCta (ctaOf L g)) st = Correction.leadLoc L g (144 + 8 * st'.val) :=
    hm
  rw [pReadyBar_lead] at hm'
  simp only [Correction.leadLoc, Loc.mk.injEq] at hm'
  obtain rfl : st = st'.val := by omega
  have htr := hi.trip
  have hst0 := hi.start
  obtain ⟨site, I, t', aw, aa, o⟩ := d
  simp only at hsd htr hst0 hpa
  rcases hsd with rfl | ⟨b0, rfl⟩
  · obtain rfl := hst0 (.inr (.inr ⟨st', rfl⟩))
    rw [hpa] at hcx'
    fin_cases st' <;> simp [Correction.freePos] at hcx'
  cases b0
  rotate_left
  · rw [hpa] at hcx'
    have hf : Correction.freePos L st'.val ⟨.oFree st' true, I, t', aw, aa, o⟩ =
        Correction.trips L := by fin_cases st' <;> simp [Correction.freePos]
    rw [hf] at hcx'
    exact absurd (by omega : Correction.trips L * I + Correction.trips L =
      Correction.trips L * j + (1 + t)) (trip_credit_ne ht1)
  have ht' := htr (by fin_cases st' <;> rfl)
  have hf : Correction.freePos L st'.val ⟨.oFree st' false, I, t', aw, aa, o⟩ = 1 + t' := by
    fin_cases st' <;> simp [Correction.freePos]
  rw [hpa, hf] at hcx'
  obtain ⟨rfl, rfl⟩ := trip_credit_inj (a := I) (b := j) ht' ht1 (by omega)
  -- the read of `α`
  obtain ⟨r, hr, pcr, ac, bs, hgr, hlr, hvr, hcr⟩ :=
    hc.rsSt st' (by unfold Correction.rsSite; exact .inr (.inr (.inr (.inr rfl))))
  rw [List.length_take] at hr
  have hrx : r < x := by omega
  rw [take_get hrx] at hgr
  rw [take_take_le hrx.le] at hcr
  obtain ⟨_, str, -, -, -, -, hcl'⟩ := corr_rd hpre hX ht hw hw' hgr
  have hstr : str = st' := by
    obtain ⟨-, hl2, -⟩ := hcl'
    rw [hlr] at hl2
    simp only [Correction.ownLoc, statsWord, Correction.sb, Loc.mk.injEq, Correction.rowOf,
      Correction.tidOf, rowOf] at hl2
    exact Fin.ext (by omega)
  subst hstr
  refine ⟨r, bs, by omega, ⟨pcr, ac, hgr, hcl', ?_⟩, ?_⟩
  · have hkw := corr_kOf hw hw'
    rw [corr_barOrd hpre hX ht hw hw' r (by omega),
      show warpOf L g - 5 + 4 * str.val = Correction.kOf L g + 3 + 4 * str.val by omega, hcr]
    ring
  intro α hbs hα hL hR dd hdd
  -- the vote of the trip
  obtain ⟨-, v, hv, mk, a, b, hgv, hpa', -, himp⟩ :=
    hc.rsVote str (by unfold Correction.rsAfterVote; exact .inr (.inr (.inr (.inr rfl))))
  obtain ⟨v0, hv1, hv2⟩ := hbs
  rw [hv1] at hvr
  injection hvr with hvr
  rw [← hvr, Correction.ltOne_fin hv2.2] at hpa'
  rw [List.length_take] at hv
  have hvx : v < x := by omega
  rw [take_get hvx] at hgv
  have hown := corr_vote_own hpre hX ht hg hw hw' hgv
  have hb : b ≠ 0 := by
    intro h0
    rw [h0, hpa'] at hown
    simp [hα] at hown
  obtain ⟨r', hr', pc', vals, hgs, hcs⟩ := himp rfl hb ⟨dd / 16, by omega⟩
  rw [List.length_take] at hr'
  have hrx' : r' < x := by omega
  rw [take_get hrx'] at hgs
  rw [take_take_le hrx'.le] at hcs
  obtain ⟨d', _, _, hc', -, hsd', -, hl, hvals⟩ := corr_tst_vals hpre hX ht hw hw' hgs
  obtain ⟨hF', hlo', α', ha'⟩ := rst_operands hpre hX ht hw hw' hc' hsd'
    (fun k hk => hL k (by omega)) (fun k hk => hR k (by omega))
  obtain ⟨y, hy⟩ := rs_f32 d' ((dd % 16) / 2) ((dd % 16) % 2) (by omega) hF' hlo' ha'
  refine ⟨y, r', _, dd % 16, vals, ⟨pc', hgs⟩, ?_, by omega, ?_, ?_⟩
  · rw [pArr, pReadyBar_lead, hcs]; ring
  · rw [tmem_column L g g _ _ (by omega)]
    simp only
    omega
  · rw [hvals _ (by omega), hy]

/-- **`ValueFacts.corr`**: every correction thread computes on the values it loaded. -/
theorem ValueFacts_corr {g : Nat} (hg : g < L.threads) (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) : CorrValues P L X g where
  rescale hs hst hq hp hin := CorrValues_rescale hpre hX ht hw hw' hs hst hq hp hin
  trip hst ht1 hge := CorrValues_trip hpre hX ht hg hw hw' hst ht1 hge
  final hW hst hhh hx hy hk hcov := CorrValues_final hpre hX ht hw hw' hW hst hhh hx hy hk hcov

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
