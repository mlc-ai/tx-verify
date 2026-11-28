-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexEv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIxFacts
public import Lemmas.Kernel.Source.WarpColl
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView

@[expose] public section

/-! # The source of an index warp's shuffle

`ix_shflSrc`: an index lane's shuffle receives the operand of the shuffle of the lane it sources
from, the same instance of its warp. The lanes of the warp make no ballot, and none exits before
the instance (`ix_exitCount`: an exit's count of shuffles is `3 + 2 ×` the CTA's blocks, above
the shuffle's own count). So the sender made the shuffle, with the receiver's word as its
operand. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **An exit of an index lane has made `3 + 2 ×` blocks shuffles.** -/
theorem ix_exitCount (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {h j pc : Nat} (hh : h < L.threads) (hw : warpOf L h = 7)
    (he : X.get (h, j) = some ⟨pc, .exit⟩) :
    ((X.tr h).take j).countP Execution.isShfl = 3 + 2 * blocksOf P L (h / L.block) := by
  have hub : ∀ f, (⟨pc, .exit⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  obtain ⟨σ, hσ, -, -, hev, -⟩ := ev_at hp hX hFw he hub
  rcases ix_cls hFw hh hw hσ with ⟨d, n, rfl, hW, hx⟩ | ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl⟩
  · have hev' : Startup.Ev L h d ⟨pc, .exit⟩ := hev
    exact absurd rfl (Startup.ev_quiet hev' hx).2.1
  · rcases hs with rfl | rfl
    · obtain ⟨inst, hk⟩ := (show Wg1.Ev L h .smr ⟨pc, .exit⟩ from hev)
      cases hk
    · obtain ⟨r, ok, hk⟩ := (show Wg1.Ev L h .hsh ⟨pc, .exit⟩ from hev)
      cases hk
  · have hev' : Index.Ev P L h d ⟨pc, .exit⟩ := hev
    obtain ⟨b, hsh, -, -, -, -, h3⟩ := ix_facts hp hX hFw (noUbBefore_of_get hX he) hσ hh hw
    obtain ⟨-, hK⟩ := hev'
    have hs : d.site = .exit := by
      obtain ⟨site, el, ac, c⟩ := d
      cases site <;> simp [Index.EvK, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv,
        Index.StoreEv] at hK ⊢
    have hb := h3 (.inr hs)
    have hc : n .shfl = ((X.tr h).take j).countP Execution.isShfl := state_count hσ .shfl
    rw [← hc, hsh, hb, hs]
    rfl

/-- The warp of a lane in the warp of an index lane (same CTA) is warp 7. -/
theorem warpOf_of_inWarp (hp : Pre P L m) {g h : Nat} (hw : warpOf L g = 7)
    (hh : h % L.block / 32 = g % L.block / 32) : warpOf L h = 7 := by
  simp only [warpOf, tidOf_eq hp] at hw ⊢
  rw [hp.block] at hh
  omega

/-- **An index lane makes no ballot.** -/
theorem ix_noVote (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {h j : Nat} {e : Event} (hh : h < L.threads) (hw : warpOf L h = 7)
    (he : X.get (h, j) = some e) (hne : ∀ f, e.kind ≠ .ub f) : voteClass e.kind = none := by
  obtain ⟨σ, hσ, -, -, hev, -⟩ := ev_at hp hX hFw he hne
  rcases ix_cls hFw hh hw hσ with ⟨d, n, rfl, hW, hx⟩ | ⟨s, n, rfl, hs⟩ | ⟨d, n, rfl⟩
  · exact (Startup.ev_coll (show Startup.Ev L h d e from hev) hx).1
  · rcases hs with rfl | rfl
    · obtain ⟨inst, hk⟩ := (show Wg1.Ev L h .smr e from hev)
      simp [hk, voteClass]
    · obtain ⟨r, ok, hk⟩ := (show Wg1.Ev L h .hsh e from hev)
      simp [hk, voteClass]
  · obtain ⟨-, hK⟩ := (show Index.Ev P L h d e from hev)
    obtain ⟨pc1, kd⟩ := e
    obtain ⟨site, el, ac, c⟩ := d
    simp only at hK ⊢
    cases site <;> simp only [Index.EvK, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv,
      Index.StoreEv] at hK <;> cases kd <;> simp_all [voteClass]

/-- **The source of an index lane's shuffle** is a lane of its warp, in the same CTA, that made
the shuffle of the same instance, sending the receiver's word. -/
theorem ix_shflSrc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k pc : Nat} {md : ShflMode} {a r : Value} {b c : Nat} {ok : Bool}
    {d : Index.D} {n : Cls → Nat}
    (he : X.get (g, k) = some ⟨pc, .shfl md a b c r ok⟩)
    (hσ : Frame.stateAt (thread P L) X g k = some (some (idxState P L g d n))) :
    ∃ j pc' b' c' r' o',
      X.get (g - PTX.laneOf L g + (shflSource md (PTX.laneOf L g) b c).1, j) =
        some ⟨pc', .shfl md r b' c' r' o'⟩ ∧
      Frame.FollowedAt (thread P L) (table P L).J X
        (g - PTX.laneOf L g + (shflSource md (PTX.laneOf L g) b c).1) j ∧
      ((X.tr (g - PTX.laneOf L g + (shflSource md (PTX.laneOf L g) b c).1)).take j).countP
        Execution.isShfl = ((X.tr g).take k).countP Execution.isShfl ∧
      g - PTX.laneOf L g + (shflSource md (PTX.laneOf L g) b c).1 < L.threads ∧
      warpOf L (g - PTX.laneOf L g + (shflSource md (PTX.laneOf L g) b c).1) = 7 := by
  have hg := Frame.lt_of_get hX he
  have hb : L.block % 32 = 0 := by rw [hp.block]
  have hF := follow_iff.mp hFw
  obtain ⟨hev, hgate, h3⟩ := ix_evAt hp hX hFw he (fun f h => by cases h) hσ
  have hw7 : warpOf L g = 7 := by simpa [subOk] using hgate
  have hsite := ix_shflSite hev (md := md) (a := a) (b := b) (c := c) (r := r) (ok := ok) rfl
  have hfacts := ix_facts hp hX hFw (noUbBefore_of_get hX he) hσ hg hw7
  have hcnt : n .shfl = ((X.tr g).take k).countP Execution.isShfl := state_count hσ .shfl
  obtain ⟨j, pc', b', c', r', o', hsj, hG, hcs, -⟩ := Frame.shfl_src
    (nv := ((X.tr g).take k).countP (voteWith (2 ^ 32 - 1))) hb hX hg rfl he rfl
    (fun h j hw _ => hF h hw.1 j)
    (fun h j e hw hblk hej hv hG hcs hcv => by
      have hwh := warpOf_of_inWarp hp hw7 hw.2
      have hne : ∀ f, e.kind ≠ .ub f := fun f hf => by
        simp [voteWith, voteClass, hf] at hv
      have := ix_noVote hp hX hFw hw.1 hwh hej hne
      simp [voteWith, this] at hv)
    (fun h j pc2 hw hblk hex hG hcs hcv => by
      have hh := hw.1
      have hwh := warpOf_of_inWarp hp hw7 hw.2
      have hcount := ix_exitCount hp hX hFw hh hwh hex
      obtain ⟨b0, hsh, -, -, h1, h2, -⟩ := hfacts
      simp only [Frame.cnt] at hcs
      rw [← hcnt] at hcs
      rw [hcount, hsh, hblk] at hcs
      rcases hsite with hs | hs | hs | hs
      · have := (h1 (.inl hs)).2; simp [Index.soff, hs] at hcs; omega
      · have := (h1 (.inr hs)).2; simp [Index.soff, hs] at hcs; omega
      · have := (h2 (.inl hs)).2; simp [Index.soff, hs] at hcs; omega
      · have := (h2 (.inr hs)).2; simp [Index.soff, hs] at hcs; omega)
  obtain ⟨hsT, hsW, -, -, -⟩ := Frame.lane_facts hb hg rfl
    (Step.shflSource_lt md (show PTX.laneOf L g < 32 from Nat.mod_lt _ (by decide)) b c)
  exact ⟨j, pc', b', c', r', o', hsj, hG, hcs,
    hsT, warpOf_of_inWarp hp hw7 hsW⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
