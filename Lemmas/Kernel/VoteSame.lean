-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpVote
public import Lemmas.Flow.NthEv

@[expose] public section

/-! # Two lanes of a warp receive the same mode vote

The `n`-th mode votes with one member mask of two lanes of a warp are one instance
(DEP-WARP-VOTE): every lane of the mask has its `n`-th vote or has exited before it
(`Step.vote_lane_of_ready`), so the instance's inputs exist, and both lanes receive their
reduction (`VoteModeOk`). The lanes' votes with that mask must share the mode (`hq`). -/

namespace PTX.Step
open PTX PTX.Flow

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **Two lanes of a warp receive the same result from their `n`-th mode votes with mask `m`**,
when every vote with mask `m` of a lane of the warp has mode `q`. -/
theorem voteMode_same (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0) {g h i j n m : Nat}
    {q : VoteMode} {pc pc' : Nat} {a a' r r' : Bool} (hg : g < L.threads)
    (hq : ∀ y k e p, SameWarp L g y → X.get (y, k) = some e → voteClass e.kind = some p →
      p.mask = m → p.qual = q)
    (hs : SameWarp L g h) (he : X.get (g, i) = some ⟨pc, .voteMode q m a r⟩)
    (he' : X.get (h, j) = some ⟨pc', .voteMode q m a' r'⟩)
    (hk : X.MaskK voteClass (g, i) m n) (hk' : X.MaskK voteClass (h, j) m n) : r = r' := by
  classical
  let part : Nat → Option Bool := fun l =>
    if hA : l < 32 ∧ m.testBit l = true ∧ ∃ j, X.MaskK voteClass (g - laneOf L g + l, j) m n then
      some (Classical.choose (Classical.choose_spec (Classical.choose_spec hA.2.2).1)).input
    else none
  have hMI : MaskInstance L voteClass X g m n q part := by
    intro l hl
    obtain ⟨hsw, -⟩ := sameWarp_lane hb hg hl
    refine ⟨fun hbit => ?_, fun hbit => by simp [part, hbit]⟩
    by_cases hA : ∃ j, X.MaskK voteClass (g - laneOf L g + l, j) m n
    · left
      have hA' : l < 32 ∧ m.testBit l = true ∧ ∃ j, X.MaskK voteClass (g - laneOf L g + l, j) m n :=
        ⟨hl, hbit, hA⟩
      have hcnt := (Classical.choose_spec hA'.2.2).2
      obtain ⟨hget, hp, hpm⟩ := Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec hA'.2.2).1)
      set ev := Classical.choose (Classical.choose_spec hA'.2.2).1
      set p := Classical.choose (Classical.choose_spec (Classical.choose_spec hA'.2.2).1)
      refine ⟨_, ev.pc, ev.kind, p.input, hget, ?_, ⟨⟨ev, p, hget, hp, hpm⟩, hcnt⟩, ?_⟩
      · rw [hp, ← hq _ _ _ p hsw hget hp hpm, ← hpm]
      · show (if hA : _ then _ else _) = _
        rw [dite_eq_left_of_eq_true (eq_true hA')]
    · right
      obtain ⟨k, pck, hx⟩ := (vote_lane_of_ready hX hk hsw (by
        rw [(sameWarp_lane hb hg hl).2]; exact hbit)).resolve_left hA
      refine ⟨⟨k, pck, hx, ?_⟩, by simp [part, hA]⟩
      by_contra hgt
      obtain ⟨j0, e0, -, he0, hv0, hc0⟩ := exists_nthEv (X := X)
        (p := fun ev => (voteClass ev.kind).any (·.mask == m)) (g := g - laneOf L g + l)
        (k := k) (n := n) (by omega)
      simp only [Option.any_eq_true, beq_iff_eq] at hv0
      obtain ⟨p0, hp0, hpm0⟩ := hv0
      exact hA ⟨j0, ⟨e0, p0, he0, hp0, hpm0⟩, hc0⟩
  have hMI' : MaskInstance L voteClass X h m n q part := by
    have hl : h - laneOf L h = g - laneOf L g := by
      have := warpLane_of_sameWarp hs
      unfold warpLane at this
      have : laneOf L h ≤ h := Nat.le_trans (Nat.mod_le _ _) (Nat.mod_le _ _)
      omega
    intro l hl'
    rw [hl]
    exact hMI l hl'
  rw [hX.warpValue.1 g i pc q m a r n he hk part hMI,
    hX.warpValue.1 h j pc' q m a' r' n he' hk' part hMI']

end PTX.Step
