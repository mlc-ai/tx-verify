-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerBallotProgress
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof Prologue

/-- A full-mask ballot of a lane prefix returns the same exact mask and preserves live registers. -/
theorem SchedulerWarpReached.consumePrefixBallot {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g pc shuffles votes dst n : Nat} (hg : g < l.threads) (hn : n ≤ 32)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g pc F shuffles votes ends)
    (hFresh : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ≠ dst)
    (hOut : ∀ lane < 32,
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
        .ev (.vote (2^32-1) (decide (lane < n))
          (fun word => next (setReg (cur.state lane) dst (b32 word.toNat))))) :
    Nonempty (SchedulerWarpReached l X g (pc+1)
      (fun lane => (dst,b32 (2^n-1))::F lane) shuffles (votes+1) ends) := by
  let thread := warpLane l g
  let hit := fun lane => decide (lane < n)
  let post := fun lane (word : BitVec 32) => next (setReg (cur.state lane) dst (b32 word.toNat))
  have hNext (lane : Nat) (hl : lane < 32) :
      Next kernel Assumptions.all l (thread lane) (cur.before lane) (cur.state lane)
        (.vote (2^32-1) (hit lane) (post lane)) :=
    ⟨cur.localSteps lane hl,hOut lane hl⟩
  have hSuffix := cur.ballotSuffix hp hMax hg hit post hNext
  have hRecorded (lane : Nat) : ∃ word, lane < 32 →
      X.get (thread lane,cur.pos lane) = some ⟨pc,.vote (2^32-1) (hit lane) word⟩ ∧
      Run kernel Assumptions.all l (thread lane) (post lane word)
        ((X.tr (thread lane)).drop (cur.pos lane+1)) (ends lane) := by
    by_cases hl : lane < 32
    · obtain ⟨word,he,_,hr⟩ := (hNext lane hl).ballot_at_nonempty
        (cur.continuation lane hl) (hSuffix lane hl) (cur.ordinals.vote lane hl)
      exact ⟨word,fun _ => ⟨by rwa [(cur.checkpoint lane hl).1] at he,hr⟩⟩
    · exact ⟨0,fun hh => (hl hh).elim⟩
  choose word seen using hRecorded
  obtain ⟨hK,_,hOrdinal⟩ := cur.ordinals.ballot (fun _ => pc) hit word
    (fun lane hl => (seen lane hl).1)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hMask (lane : Nat) (hl : lane < 32) : (word lane).toNat = 2^n-1 := by
    have hInstance : MaskInstance l voteClass X (thread lane) (2^32-1) votes .ballot
        (fun peer => some (hit peer)) := by
      intro peer hPeer
      have hLane : laneOf l (thread lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      have hEq : thread lane - laneOf l (thread lane) + peer = thread peer := by
        rw [hLane]
        unfold thread warpLane
        omega
      refine ⟨fun _ => .inl ?_,?_⟩
      · rw [hEq]
        exact ⟨cur.pos peer,pc,.vote (2^32-1) (hit peer) (word peer),_,
          (seen peer hPeer).1,rfl,hK peer hPeer,rfl⟩
      · intro h
        rw [Nat.testBit_two_pow_sub_one] at h
        simp [hPeer] at h
    have hWord : word lane = BitVec.ofNat 32 (2^n-1) := by
      apply BitVec.eq_of_getLsbD_eq
      intro peer hPeer
      have hBit := (hMax.1.vote (thread lane) (cur.pos lane) votes pc (2^32-1) (hit lane)
        (word lane) (seen lane hl).1 (hK lane hl) (fun peer => some (hit peer)) hInstance
        peer hPeer).1 _ rfl
      rw [BitVec.getLsbD_ofNat,Nat.testBit_two_pow_sub_one]
      simpa [hit,hPeer] using hBit
    rw [hWord,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have hPow : 2^n ≤ 2^32 := Nat.pow_le_pow_right (by decide) hn
    have hPos : 0 < 2^n := Nat.two_pow_pos n
    omega
  let result : SchedulerWarpAt l X g (pc+1)
      (fun lane => (dst,b32 (2^n-1))::F lane) shuffles (votes+1) ends :=
    ⟨fun lane => cur.pos lane+1,fun lane => post lane (word lane),
      fun lane => post lane (word lane),hOrdinal,fun lane hl => (seen lane hl).2,fun _ _ => .refl,
      fun lane hl => by
        simpa only [post,hMask lane hl] using
          (cur.checkpoint lane hl).set (v := b32 ((word lane).toNat)) (hFresh lane hl)⟩
  refine ⟨⟨result,fun _ _ => Nat.succ_pos _,fun lane hl => len_of_get (seen lane hl).1,
    fun lane hl => releasedIfLast (seen lane hl).1 (by intro h; cases h),?_⟩⟩
  intro lane hl
  have he := (seen lane hl).1
  have hLen : cur.pos lane < (X.tr (thread lane)).length := len_of_get he
  change Run kernel Assumptions.all l (thread lane) {}
    ((X.tr (thread lane)).take (cur.pos lane+1)) (some (post lane (word lane)))
  rw [List.take_succ_eq_append_getElem hLen,(List.getElem?_eq_some_iff.mp he).2]
  exact (cur.recorded lane hl).snoc (cur.localSteps lane hl)
    ⟨_,(hNext lane hl).stop,word lane,by rw [(cur.checkpoint lane hl).1],rfl⟩

end PTX.Kernels.TmlFa4Fwd.Epilogue
