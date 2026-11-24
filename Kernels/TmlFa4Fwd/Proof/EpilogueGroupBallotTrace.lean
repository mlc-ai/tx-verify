-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupRoute
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerBallotProgress
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The original group indices and register frame are still needed after the ballot. -/
def ballotCarry (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(7223, b32 first), (7220, b32 (groupLaneTiles p first lane)),
    (7221, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
    (1072, b32 cta)] ++ groupSchedulerFrame p lane F

/-- The actual selection ballot determines the batch and its index in the group. -/
def groupBallotFacts (p : Params) (cta first batch lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(1208, b32 (batch - first)), (7228, b32 batch), (294, .pred (decide (batch = first))),
    (7225, b32 0), (1207, b32 (tilePrefix p first * p.heads))] ++ ballotCarry p cta first lane F

private theorem ballotCarry_frame {p : Params} {cta first lane : Nat} {F : List (Nat × Value)}
    (hF : ∀ pair ∈ F, pair.1 ∈ schedulerFrameRegs) :
    ∀ pair ∈ ballotCarry p cta first lane F, pair.1 ∈ ballotRegs := by
  intro pair hm
  simp only [ballotCarry, groupSchedulerFrame, List.cons_append, List.nil_append, List.mem_cons]
    at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | hm
  all_goals first
    | exact List.mem_append.mpr (.inr (hF pair hm))
    | simp [ballotRegs, schedulerFrameRegs]

private theorem selectionModel {l : Launch} {g : Nat} {s : TState}
    (hLo : 2883 ≤ s.pc) (hHi : s.pc < 2959) :
    out kernel Assumptions.all l g s = out kernel [] l g s :=
  epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Every lane's actual full-mask vote yields the same selected request, preserving the trace. -/
theorem SchedulerWarpAt.selectBallotTo (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first batch shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 2883 (fun lane => groupChoiceFacts p cta first lane (F lane))
      shuffles votes ends) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch + 1) * p.heads)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs) {src index : Nat}
    {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 2887 < target.pc) :
    ∃ result : SchedulerWarpAt l X g 2892
        (fun lane => groupBallotFacts p cta first batch lane (F lane)) shuffles (votes + 1) ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g result.pos src index target := by
  let thread := warpLane l g
  let start := tilePrefix p first * p.heads
  let vote := fun lane => decide (first + lane < batch)
  let carry := fun lane => ballotCarry p cta first lane (F lane)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (thread lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  have hPrepare (lane : Nat) : ∃ t, lane < 32 →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) (cur.before lane) t ∧
        At t 2887 ((1207, b32 start) :: (293, .pred (vote lane)) :: carry lane) := by
    by_cases hl : lane < 32
    · have ht := cur.checkpoint lane hl
      have hs := ht.2.2.2.2
      let args := [(7222, b32 (∑ j ∈ Finset.range 32, groupLaneTiles p first j)),
        (7221, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
        (7224, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
        (7138, b32 p.heads), (1072, b32 cta)]
      have hArgs : At (cur.state lane) 2883 (args ++ carry lane) := by
        have hRest : Holds (cur.state lane).regs (carry lane) :=
          ⟨hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1, hs.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.2.2⟩
        exact ht.mono ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hRest⟩
      obtain ⟨u, hu, hU⟩ := prepareGroupVote hp (thread lane) hFirst hGroup hBatch hLo hHi
        (fun hlo hhi => selectionModel hlo (by omega)) (ballotCarry_frame (hF lane hl))
        (by simpa only [hLane lane hl] using hArgs)
      exact ⟨u, fun _ => ⟨(cur.localSteps lane hl).trans (run_rtg hu),
        by simpa only [hLane lane hl, start, vote, carry, List.cons_append, List.nil_append]
          using hU⟩⟩
    · exact ⟨cur.state lane, fun hh => False.elim (hl hh)⟩
  choose ready prep using hPrepare
  let after := fun lane (word : BitVec 32) => next (setReg (ready lane) 2352 (b32 word.toNat))
  have hNext (lane : Nat) (hl : lane < 32) :
      Next kernel Assumptions.all l (thread lane) (cur.before lane) (ready lane)
        (.vote (2 ^ 32 - 1) (vote lane) (after lane)) := by
    have ht := (prep lane hl).2
    have hOut := selectedGroupVote hp (thread lane) (ready lane) (vote lane)
      ht.1 ht.2.2.2.1 ht.2.2.2.2.2.1
    have hEq := selectionModel (l := l) (g := thread lane) (s := ready lane)
      (by rw [ht.1]; decide) (by rw [ht.1]; decide)
    exact ⟨(prep lane hl).1, hEq.trans hOut⟩
  have hSuffix : ∀ lane < 32, (X.tr (thread lane)).drop (cur.pos lane) ≠ [] := by
    rcases hProgress with he | hw
    · intro lane hl hNil
      have hr := cur.continuation lane hl
      rw [hNil, he lane hl] at hr
      cases hr
    · exact hw.ballotSuffix hX cur.ordinals hBlock hg (hNext src hw.lane)
        (cur.continuation src hw.lane)
  have hEvent (lane : Nat) : ∃ word, lane < 32 →
      X.get (thread lane, cur.pos lane) = some ⟨2887, .vote (2 ^ 32 - 1) (vote lane) word⟩ ∧
        Run kernel Assumptions.all l (thread lane) (after lane word)
          ((X.tr (thread lane)).drop (cur.pos lane + 1)) (ends lane) := by
    by_cases hl : lane < 32
    · obtain ⟨word, he, _, hr⟩ := (hNext lane hl).ballot_at_nonempty
        (cur.continuation lane hl) (hSuffix lane hl) (cur.ordinals.vote lane hl)
      exact ⟨word, fun _ => ⟨by rw [(prep lane hl).2.1] at he; exact he, hr⟩⟩
    · exact ⟨0, fun hh => False.elim (hl hh)⟩
  choose word observed using hEvent
  obtain ⟨hOrdinal, _, hNextOrd⟩ :=
    cur.ordinals.ballot (fun _ => 2887) vote word (fun lane hl => (observed lane hl).1)
  have hLocal (lane : Nat) : ∃ v, lane < 32 →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane))
        (after lane (word lane)) v ∧
        At v 2892 (groupBallotFacts p cta first batch lane (F lane)) := by
    by_cases hl : lane < 32
    · let frame := (1207, b32 start) :: carry lane
      have hFrame : ∀ pair ∈ frame, pair.1 ∈ popcountRegs := by
        intro pair hm
        rcases List.mem_cons.mp hm with rfl | hm
        · simp [popcountRegs]
        · exact List.mem_cons_of_mem _ (ballotCarry_frame (hF lane hl) pair hm)
      have ht := (prep lane hl).2
      have hAt : At (ready lane) 2887 ((293, .pred (vote lane)) :: frame) :=
        ht.mono ⟨ht.2.2.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.2⟩
      have hSource (j : Nat) : thread lane - laneOf l (thread lane) + j = thread j := by
        rw [hLane lane hl]
        simp only [thread, warpLane]
        omega
      have hPeers : ∀ j < 32, ∃ k val,
          let e := (thread lane - laneOf l (thread lane) + j, k)
          X.get e = some ⟨2887, .vote (2 ^ 32 - 1) (vote j) val⟩ ∧
            X.MaskK voteClass e (2 ^ 32 - 1) votes := by
        intro j hj
        refine ⟨cur.pos j, word j, ?_⟩
        dsimp only
        rw [hSource j]
        exact ⟨(observed j hj).1, hOrdinal j hj⟩
      obtain ⟨u, hu, hU⟩ := finishGroupVote hp hX hFirst hGroup hBatch
        (fun hlo hhi => selectionModel (by omega) (by omega))
        hFrame (by simp [frame, carry, ballotCarry]) hAt (observed lane hl).1
        (hOrdinal lane hl) hPeers
      refine ⟨u, fun _ => ⟨run_rtg hu, ?_⟩⟩
      simpa only [groupBallotFacts, frame, start, carry, List.cons_append, List.nil_append] using hU
    · exact ⟨after lane (word lane), fun hh => False.elim (hl hh)⟩
  choose u hu using hLocal
  refine ⟨⟨fun lane => cur.pos lane + 1, fun lane => after lane (word lane), u, hNextOrd,
    fun lane hl => (observed lane hl).2, fun lane hl => (hu lane hl).1,
    fun lane hl => (hu lane hl).2⟩, ?_⟩
  intro h
  apply h.afterCommonEvent hX hBlock hg hPc
  exact fun lane hl => ⟨_, (observed lane hl).1, rfl, by intro he; cases he⟩

/-- Every lane's actual full-mask vote yields the same selected request, preserving the trace. -/
theorem SchedulerWarpAt.selectBallot (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g cta first batch shuffles votes : Nat} (hg : g < l.threads) {F : Nat → List (Nat × Value)}
    (cur : SchedulerWarpAt l X g 2883 (fun lane => groupChoiceFacts p cta first lane (F lane))
      shuffles votes) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch + 1) * p.heads)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs) :
    Nonempty (SchedulerWarpAt l X g 2892
      (fun lane => groupBallotFacts p cta first batch lane (F lane)) shuffles (votes + 1)) := by
  obtain ⟨result, _⟩ := cur.selectBallotTo hp hX hg hFirst hGroup hBatch hLo hHi hF
    (src := 0) (index := 0) (target := ⟨2888, .exit⟩) (.inl (fun _ _ => rfl)) (by decide)
  exact ⟨result⟩

/-- All lanes of a reached selection ballot participate and recover the selected request. -/
theorem SchedulerWarpReached.selectBallotOfMaximal (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g cta first batch shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2883 (fun lane => groupChoiceFacts p cta first lane (F lane))
      shuffles votes ends) (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch + 1) * p.heads)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
    : Nonempty (SchedulerWarpReached l X g 2892
        (fun lane => groupBallotFacts p cta first batch lane (F lane))
        shuffles (votes + 1) ends) := by
  have hX := hMax.1
  let thread := warpLane l g
  let start := tilePrefix p first * p.heads
  let vote := fun lane => decide (first + lane < batch)
  let carry := fun lane => ballotCarry p cta first lane (F lane)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (thread lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  have hPrepare (lane : Nat) : ∃ t, lane < 32 →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) (cur.before lane) t ∧
        At t 2887 ((1207, b32 start) :: (293, .pred (vote lane)) :: carry lane) := by
    by_cases hl : lane < 32
    · have ht := cur.checkpoint lane hl
      have hs := ht.2.2.2.2
      let args := [(7222, b32 (∑ j ∈ Finset.range 32, groupLaneTiles p first j)),
        (7221, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
        (7224, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
        (7138, b32 p.heads), (1072, b32 cta)]
      have hArgs : At (cur.state lane) 2883 (args ++ carry lane) := by
        have hRest : Holds (cur.state lane).regs (carry lane) :=
          ⟨hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1, hs.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.2.2⟩
        exact ht.mono ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hRest⟩
      obtain ⟨u, hu, hU⟩ := prepareGroupVote hp (thread lane) hFirst hGroup hBatch hLo hHi
        (fun hlo hhi => selectionModel hlo (by omega)) (ballotCarry_frame (hF lane hl))
        (by simpa only [hLane lane hl] using hArgs)
      exact ⟨u, fun _ => ⟨(cur.localSteps lane hl).trans (run_rtg hu),
        by simpa only [hLane lane hl, start, vote, carry, List.cons_append, List.nil_append]
          using hU⟩⟩
    · exact ⟨cur.state lane, fun hh => False.elim (hl hh)⟩
  choose ready prep using hPrepare
  let after := fun lane (word : BitVec 32) => next (setReg (ready lane) 2352 (b32 word.toNat))
  have hNext (lane : Nat) (hl : lane < 32) :
      Next kernel Assumptions.all l (thread lane) (cur.before lane) (ready lane)
        (.vote (2 ^ 32 - 1) (vote lane) (after lane)) := by
    have ht := (prep lane hl).2
    have hOut := selectedGroupVote hp (thread lane) (ready lane) (vote lane)
      ht.1 ht.2.2.2.1 ht.2.2.2.2.2.1
    have hEq := selectionModel (l := l) (g := thread lane) (s := ready lane)
      (by rw [ht.1]; decide) (by rw [ht.1]; decide)
    exact ⟨(prep lane hl).1, hEq.trans hOut⟩
  let atVote : SchedulerWarpAt l X g 2887
      (fun lane => (1207,b32 start) :: (293,.pred (vote lane)) :: carry lane)
      shuffles votes ends :=
    ⟨cur.pos,cur.before,ready,cur.ordinals,cur.continuation,
      fun lane hl => (prep lane hl).1,fun lane hl => (prep lane hl).2⟩
  have hSuffix := (cur.reframe atVote rfl rfl).ballotSuffix hp hMax hg vote after hNext
  have hEvent (lane : Nat) : ∃ word, lane < 32 →
      X.get (thread lane, cur.pos lane) = some ⟨2887, .vote (2 ^ 32 - 1) (vote lane) word⟩ ∧
        Run kernel Assumptions.all l (thread lane) (after lane word)
          ((X.tr (thread lane)).drop (cur.pos lane + 1)) (ends lane) := by
    by_cases hl : lane < 32
    · obtain ⟨word, he, _, hr⟩ := (hNext lane hl).ballot_at_nonempty
        (cur.continuation lane hl) (hSuffix lane hl) (cur.ordinals.vote lane hl)
      exact ⟨word, fun _ => ⟨by rw [(prep lane hl).2.1] at he; exact he, hr⟩⟩
    · exact ⟨0, fun hh => False.elim (hl hh)⟩
  choose word observed using hEvent
  obtain ⟨hOrdinal, _, hNextOrd⟩ :=
    cur.ordinals.ballot (fun _ => 2887) vote word (fun lane hl => (observed lane hl).1)
  have hLocal (lane : Nat) : ∃ v, lane < 32 →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane))
        (after lane (word lane)) v ∧
        At v 2892 (groupBallotFacts p cta first batch lane (F lane)) := by
    by_cases hl : lane < 32
    · let frame := (1207, b32 start) :: carry lane
      have hFrame : ∀ pair ∈ frame, pair.1 ∈ popcountRegs := by
        intro pair hm
        rcases List.mem_cons.mp hm with rfl | hm
        · simp [popcountRegs]
        · exact List.mem_cons_of_mem _ (ballotCarry_frame (hF lane hl) pair hm)
      have ht := (prep lane hl).2
      have hAt : At (ready lane) 2887 ((293, .pred (vote lane)) :: frame) :=
        ht.mono ⟨ht.2.2.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.2⟩
      have hSource (j : Nat) : thread lane - laneOf l (thread lane) + j = thread j := by
        rw [hLane lane hl]
        simp only [thread, warpLane]
        omega
      have hPeers : ∀ j < 32, ∃ k val,
          let e := (thread lane - laneOf l (thread lane) + j, k)
          X.get e = some ⟨2887, .vote (2 ^ 32 - 1) (vote j) val⟩ ∧
            X.MaskK voteClass e (2 ^ 32 - 1) votes := by
        intro j hj
        refine ⟨cur.pos j, word j, ?_⟩
        dsimp only
        rw [hSource j]
        exact ⟨(observed j hj).1, hOrdinal j hj⟩
      obtain ⟨u, hu, hU⟩ := finishGroupVote hp hX hFirst hGroup hBatch
        (fun hlo hhi => selectionModel (by omega) (by omega))
        hFrame (by simp [frame, carry, ballotCarry]) hAt (observed lane hl).1
        (hOrdinal lane hl) hPeers
      refine ⟨u, fun _ => ⟨run_rtg hu, ?_⟩⟩
      simpa only [groupBallotFacts, frame, start, carry, List.cons_append, List.nil_append] using hU
    · exact ⟨after lane (word lane), fun hh => False.elim (hl hh)⟩
  choose u hu using hLocal
  let result : SchedulerWarpAt l X g 2892
      (fun lane => groupBallotFacts p cta first batch lane (F lane))
      shuffles (votes + 1) ends :=
    ⟨fun lane => cur.pos lane + 1,fun lane => after lane (word lane),u,hNextOrd,
      fun lane hl => (observed lane hl).2,fun lane hl => (hu lane hl).1,
      fun lane hl => (hu lane hl).2⟩
  refine ⟨{ toSchedulerWarpAt := result
            positive := ?_, bounded := ?_, released := ?_, recorded := ?_ }⟩
  · exact fun _ _ => Nat.succ_pos _
  · exact fun lane hl => len_of_get (observed lane hl).1
  · exact fun lane hl => Prologue.releasedIfLast (observed lane hl).1 (by intro h; cases h)
  · intro lane hl
    have hGet := (observed lane hl).1
    have hLen : cur.pos lane < (X.tr (thread lane)).length := len_of_get hGet
    change Run kernel Assumptions.all l (thread lane) {}
      ((X.tr (thread lane)).take (cur.pos lane+1)) (some (after lane (word lane)))
    rw [List.take_succ_eq_append_getElem hLen,(List.getElem?_eq_some_iff.mp hGet).2]
    apply (cur.recorded lane hl).snoc (prep lane hl).1
    exact ⟨_,(hNext lane hl).stop,word lane,by rw [(prep lane hl).2.1],rfl⟩


end
end PTX.Kernels.TmlFa4Fwd.Epilogue
