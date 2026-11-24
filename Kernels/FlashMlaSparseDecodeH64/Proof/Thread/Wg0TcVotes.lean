-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveSites
import Lemmas.Flow.VoteSeq

public section

/-! # Uniform results of the votes selecting Tensor Memory rescale -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0TcVotes

open PTX PTX.Flow

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A completed full-mask any-mode vote supplies its actual warp inputs. -/
theorem full_instance
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {g i tag n : Nat} {p r : Bool}
    (he : X.get (g, i) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) p r⟩)
    (hk : X.MaskK voteClass (g, i) (2 ^ 32 - 1) n) :
    ∃ part, MaskInstance L voteClass X g (2 ^ 32 - 1) n .any part := by
  classical
  have hr : Ready L X (g, i) :=
    hX.dependency.ready _ (by simp [Returned, he, Kind.resume])
  have hparts (lane : Nat) : ∃ v : Option Bool, lane < 32 →
      ((∃ j pc k a, X.get (warpLane L g lane, j) = some ⟨pc, k⟩ ∧
        voteClass k = some ⟨2 ^ 32 - 1, .any, a⟩ ∧
        X.MaskK voteClass (warpLane L g lane, j) (2 ^ 32 - 1) n ∧ v = some a) ∨
        (MaskExited voteClass X (warpLane L g lane) (2 ^ 32 - 1) n ∧ v = none)) := by
    by_cases hl : lane < 32
    · have hb : (2 ^ 32 - 1 : Nat).testBit lane = true :=
        Nat.testBit_two_pow_sub_one 32 _ ▸ decide_eq_true hl
      have hn := maskNeeds_mem L voteClass X (g, i) he rfl hl hb
      have hneeds : Needs L X (g, i) = maskNeeds L voteClass X (g, i) := by
        simp [Needs, he, KindNeeds]
      obtain ⟨_, _, j, rfl, _, m', n', q, hat, hs⟩ := hr _ (hneeds ▸ hn)
      obtain ⟨⟨⟨pc', k'⟩, arg, he', hc', hm'⟩, hc⟩ := hat.1
      rw [he] at he'
      cases he'
      have harg : arg = ⟨2 ^ 32 - 1, .any, p⟩ := Option.some.inj hc'.symm
      subst arg
      subst m'
      have hn' : n' = n := hc.symm.trans hk.2
      rw [hn'] at hs
      obtain ⟨ev, arg, hv, hkind, hq⟩ := hat.2
      rw [he] at hv
      cases hv
      have harg : arg = ⟨2 ^ 32 - 1, .any, p⟩ := Option.some.inj hkind.symm
      subst arg
      subst q
      rcases hs with hs | ⟨_, hx⟩
      · obtain ⟨⟨ev, args, hget, hclass, hm⟩, _⟩ := hs.1
        obtain ⟨ev', args', hget', hclass', hmode⟩ := hs.2
        rw [hget] at hget'
        cases hget'
        rw [hclass] at hclass'
        cases hclass'
        obtain ⟨pc, k⟩ := ev
        have ha : args = ⟨2 ^ 32 - 1, .any, args.input⟩ := by
          cases args
          simp_all
        exact ⟨some args.input, fun _ => .inl
          ⟨j, pc, k, args.input, hget, hclass.trans (congrArg some ha), hs.1, rfl⟩⟩
      · exact ⟨none, fun _ => .inr ⟨(maskExited_iff voteClass X _ _ _).mpr ⟨j, hx⟩, rfl⟩⟩
    · exact ⟨none, fun h => (hl h).elim⟩
  choose part hp using hparts
  refine ⟨part, fun lane hl => ⟨fun _ => hp lane hl, ?_⟩⟩
  rw [Nat.testBit_two_pow_sub_one, decide_eq_true hl]
  simp

/-- Two actual full-mask any-mode votes in one warp and instance return the same predicate. -/
theorem same_result (hX : Consistent L kernel Assumptions.all mem0 X)
    {g h i j tag tag' n : Nat} {p p' r r' : Bool} (hw : SameWarp L g h)
    (he : X.get (g, i) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) p r⟩)
    (hf : X.get (h, j) = some ⟨tag', .voteMode .any (2 ^ 32 - 1) p' r'⟩)
    (hk : X.MaskK voteClass (g, i) (2 ^ 32 - 1) n)
    (hk' : X.MaskK voteClass (h, j) (2 ^ 32 - 1) n) : r = r' := by
  obtain ⟨part, hp⟩ := full_instance hX he hk
  have hp' : MaskInstance L voteClass X h (2 ^ 32 - 1) n .any part := by
    intro lane hl
    exact sameWarp_warpStart hw ▸ hp lane hl
  exact (hX.warpValue.1 g i tag .any _ _ _ n he hk part hp).trans
    (hX.warpValue.1 h j tag' .any _ _ _ n hf hk' part hp').symm

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0TcVotes
