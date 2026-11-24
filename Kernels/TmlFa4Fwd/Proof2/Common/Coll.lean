-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Common.Frame
public import Lemmas.Kernel.FullVote
public import Lemmas.Kernel.Source.WarpColl

@[expose] public section

/-! # The source of a warp collective, for a lane of any warp

What a shuffle or a full-mask ballot of a lane of warp `w` returns comes from the lanes of the
warp at the same instance (`ShflOk`, `VoteOk`). The instance is fixed by the count of the lane's
earlier collectives of its kind; the source lanes are followed up to it because their earlier
positions have fewer collectives (`GoodUpTo`, the induction hypothesis of the order `μ`).

A role gives three position facts about the lanes of its warp in the CTA, each as "this cannot
happen" at a followed position: a ballot past at most the shuffles and exactly the ballots of the
current state (when the current state is a shuffle); a shuffle past at most the ballots and exactly
the shuffles (when it is a ballot); and a return past at most both counts. From them,
`shfl_src` finds the source lane's shuffle of the instance and `vote_src` every lane's ballot of
the instance, each at a followed position with the counts of the instance. Which site the source
lane is at, and what it sends, is the role's (its `Fits` at that position). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A full-mask ballot as lane L's vote class. -/
theorem isFullVote_eq : isFullVote = voteWith (2 ^ 32 - 1) := rfl

/-- A ballot is a collective; the mask is matched, not evaluated. -/
theorem isColl_vote {pc : Nat} {a : Bool} {b : BitVec 32} :
    isColl ⟨pc, .vote (2 ^ 32 - 1) a b⟩ = true := by
  simp [isColl, isFullVote_eq, voteWith_vote]

/-- **The source of a shuffle of a lane of warp `w`**: the source lane made the shuffle of the same
instance, sending the received value, from a followed position with the instance's shuffle count
and at most the current ballot count. -/
theorem shfl_src {J : (g : Nat) → (thread p L g).D → Prop} {w : Nat}
    (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k pc ns nv : Nat} {mode : ShflMode}
    {a recv : Value} {b c : Nat} {ok : Bool}
    (he : X.get (g, k) = some ⟨pc, .shfl mode a b c recv ok⟩)
    (hcs : ((X.tr g).take k).countP Execution.isShfl = ns) (IH : GoodUpTo J X w (ns + nv))
    (hV : ∀ h j e, InWarp L w h → h / L.block = g / L.block → X.get (h, j) = some e →
      isFullVote e = true → Frame.FollowedAt (thread p L) J X h j →
      Frame.cnt X Execution.isShfl h j ≤ ns → Frame.cnt X isFullVote h j = nv → False)
    (hE : ∀ h j pc, InWarp L w h → h / L.block = g / L.block → X.get (h, j) = some ⟨pc, .exit⟩ →
      Frame.FollowedAt (thread p L) J X h j →
      Frame.cnt X Execution.isShfl h j ≤ ns → Frame.cnt X isFullVote h j ≤ nv → False) :
    ∃ j pc' b' c' r' o',
      X.get (g - laneOf L g + (shflSource mode (laneOf L g) b c).1, j) =
        some ⟨pc', .shfl mode recv b' c' r' o'⟩ ∧
      Frame.FollowedAt (thread p L) J X (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) j ∧
      Frame.cnt X Execution.isShfl (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) j = ns ∧
      Frame.cnt X isFullVote (g - laneOf L g + (shflSource mode (laneOf L g) b c).1) j ≤ nv :=
  Frame.shfl_src (C := thread p L) (by rw [hp.block]) hX hg hw he hcs IH hV hE

/-- **The sources of a ballot of a lane of warp `w`**: the bit of every lane is its predicate at
the ballot of the same instance, where the role's fact `P` holds (`hB`: a full-mask vote of a
lane of the warp at a followed position with the instance's ballot count and at most the current
shuffle count is a ballot whose predicate satisfies `P`). -/
theorem vote_src {J : (g : Nat) → (thread p L g).D → Prop} {w : Nat} {P : Nat → Bool → Prop}
    (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k pc ns nv : Nat} {a : Bool}
    {bv : BitVec 32} (he : X.get (g, k) = some ⟨pc, .vote (2 ^ 32 - 1) a bv⟩)
    (hcv : ((X.tr g).take k).countP isFullVote = nv) (IH : GoodUpTo J X w (ns + nv))
    (hS : ∀ h j e, InWarp L w h → h / L.block = g / L.block → X.get (h, j) = some e →
      Execution.isShfl e = true → Frame.FollowedAt (thread p L) J X h j →
      Frame.cnt X isFullVote h j ≤ nv → Frame.cnt X Execution.isShfl h j = ns → False)
    (hE : ∀ h j pc, InWarp L w h → h / L.block = g / L.block → X.get (h, j) = some ⟨pc, .exit⟩ →
      Frame.FollowedAt (thread p L) J X h j →
      Frame.cnt X Execution.isShfl h j ≤ ns → Frame.cnt X isFullVote h j ≤ nv → False)
    (hB : ∀ h j e, InWarp L w h → h / L.block = g / L.block → X.get (h, j) = some e →
      isFullVote e = true → Frame.FollowedAt (thread p L) J X h j →
      Frame.cnt X Execution.isShfl h j ≤ ns → Frame.cnt X isFullVote h j = nv →
      ∃ pc' a' b', e = ⟨pc', .vote (2 ^ 32 - 1) a' b'⟩ ∧ P h a') :
    ∀ i < 32, P (g - laneOf L g + i) (bv.getLsbD i) :=
  Frame.vote_src (C := thread p L) (by rw [hp.block]) hX hg hw he hcv IH hS hE hB

end
end PTX.Kernels.TmlFa4Fwd.Proof2
