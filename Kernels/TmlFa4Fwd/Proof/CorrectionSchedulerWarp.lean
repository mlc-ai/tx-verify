-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionSchedulerEntry
public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupRoute

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

private theorem shuffleDestFresh {p : Params} {l : Launch} {g : Nat} :
    ∀ pair ∈ firstShuffleFacts p l g, pair.1 ≠ 5869 := by
  intro pair hPair hEq
  have hm := List.mem_map_of_mem (f := Prod.fst) hPair
  rw [hEq] at hm
  have hNot : 5869 ∉ (firstShuffleFacts p l g).map Prod.fst := by
    simp only [firstShuffleFacts, afterCreditFacts, creditFacts, entryFacts, nonzeroBarrierFacts,
      abiFacts, List.cons_append, List.nil_append, List.map_cons, List.map_nil]
    decide
  exact hNot hm

/-- A later correction event forces the warp's initial down-shuffle and all of its
peer lane inputs, without requiring any lane to finish. -/
theorem firstCorrectionWarpOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src index : Nat} {target : Event} (hg : g < l.threads)
    (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12) (hSrc : src < 32)
    (hEvent : X.get (warpLane l g src, index) = some target) (hPc : 7762 < target.pc) :
    ∃ (ends : Nat → Option TState)
      (cur : SchedulerWarpAt l X g 7763
        (fun lane => (5869, b32 (firstSchedulerWord p (shflSource .down lane 1 31).1)) ::
          firstShuffleFacts p l (warpLane l g lane)) 4 0 ends),
      WarpFollowsEvent l X g cur.pos src index target := by
  classical
  let thread := warpLane l g
  let pos (lane : Nat) := if p.batch < laneOf l (thread lane) then 9 else 10
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hWarp (lane : Nat) (hl : lane < 32) : SameWarp l g (thread lane) :=
    (Step.sameWarp_lane hBlock hg hl).1
  have hThread (lane : Nat) (hl : lane < 32) : thread lane < l.threads := (hWarp lane hl).1.2.1
  have hLow (lane : Nat) (hl : lane < 32) : 8 ≤ warpIndex l (thread lane) := by
    have hEq : warpIndex l g = warpIndex l (thread lane) := (hWarp lane hl).2
    exact hEq ▸ hLo
  have hHigh (lane : Nat) (hl : lane < 32) : warpIndex l (thread lane) < 12 := by
    have hEq : warpIndex l g = warpIndex l (thread lane) := (hWarp lane hl).2
    exact hEq ▸ hHi
  have cursorOf {lane j : Nat} {e : Event} (hl : lane < 32)
      (he : X.get (thread lane, j) = some e)
      (hDemand : 7761 < e.pc ∨ e.kind = .exit ∨ 3 ≤ j ∧ Execution.isShfl e = true) :
      ∃ t o, At t 7762 (firstShuffleFacts p l (thread lane)) ∧
        Run kernel Assumptions.all l (thread lane) t ((X.tr (thread lane)).drop (pos lane)) o ∧
        ((X.tr (thread lane)).take (pos lane)).countP Execution.isShfl = 3 ∧
        ((X.tr (thread lane)).take (pos lane)).countP isFullWarpVote = 0 ∧ pos lane ≤ j :=
    firstCorrectionCursorOfEvent hp hX (hThread lane hl) (hLow lane hl) (hHigh lane hl)
      he hDemand
  obtain ⟨t, o, ht, hRun, hCount, _, hBefore⟩ := cursorOf hSrc hEvent (.inl (by omega))
  have hSrcNonempty : (X.tr (thread src)).drop (pos src) ≠ [] := by
    intro h
    have hn : index < (X.tr (thread src)).length := (List.getElem?_eq_some_iff.mp hEvent).1
    exact Nat.not_le_of_lt hn ((List.drop_eq_nil_iff.mp h).trans hBefore)
  have hNext : Next kernel Assumptions.all l (thread src) t t (.shfl .down
      (b32 (firstSchedulerWord p (laneOf l (thread src)))) 1 31
      (fun x _ => next (setReg t 5869 x))) := ⟨.refl, firstShuffleOut hp ht⟩
  obtain ⟨recv, ok, he, hk, _⟩ := hNext.shuffle_at_nonempty hRun hSrcNonempty hCount
  have peers (lane : Nat) (hl : lane < 32) :
      ∃ t o, At t 7762 (firstShuffleFacts p l (thread lane)) ∧
      Run kernel Assumptions.all l (thread lane) t ((X.tr (thread lane)).drop (pos lane)) o ∧
      ((X.tr (thread lane)).take (pos lane)).countP Execution.isShfl = 3 ∧
      ((X.tr (thread lane)).take (pos lane)).countP isFullWarpVote = 0 ∧
      (∀ j < pos lane, ∀ pc, X.get (thread lane, j) ≠ some ⟨pc, .exit⟩) := by
    have hSame := Step.sameWarp_trans (sameWarp_symm (hWarp src hSrc)) (hWarp lane hl)
    have hPeer := Step.shfl_lane_of_ready hX he hk hSame
    obtain ⟨j, e, he, hDemand⟩ :
        ∃ j e, X.get (thread lane, j) = some e ∧
          (7761 < e.pc ∨ e.kind = .exit ∨ 3 ≤ j ∧ Execution.isShfl e = true) := by
      rcases hPeer with ⟨j, hPeer⟩ | ⟨j, pc, he, _⟩
      · have hJ : 3 ≤ j :=
          hPeer.2.symm.le.trans ((List.countP_le_length ..).trans (List.length_take_le ..))
        obtain ⟨⟨pc, mode, a, b, c, recv, ok, he⟩, _⟩ := hPeer
        exact ⟨j, _, he, .inr (.inr ⟨hJ, rfl⟩)⟩
      · exact ⟨j, _, he, .inr (.inl rfl)⟩
    obtain ⟨t, o, ht, hr, hs, hv, hJ⟩ := cursorOf hl he hDemand
    refine ⟨t, o, ht, hr, hs, hv, ?_⟩
    intro k hk pc hExit
    have hLast := Execution.exit_last hX (hThread lane hl) hExit
    have hLen : j < (X.tr (thread lane)).length := (List.getElem?_eq_some_iff.mp he).1
    omega
  let _ : Inhabited TState := ⟨{}⟩
  choose! states ends hs hr hShfl hVote hNoExit using peers
  let cur : SchedulerWarpAt l X g 7762
      (fun lane => firstShuffleFacts p l (thread lane)) 3 0 ends :=
    ⟨pos, states, states, ⟨hShfl, hVote⟩, hr, fun _ _ => .refl, hs⟩
  have hFollow : WarpFollowsEvent l X g cur.pos src index target :=
    ⟨hSrc, hEvent, hBefore, hNoExit⟩
  obtain ⟨next, hAdvance⟩ := cur.consumeShuffleTo hp hX hg (dst := 5869) .down
    (fun lane => b32 (firstSchedulerWord p lane)) (fun _ => 1) (fun _ => 31)
    (fun _ _ => shuffleDestFresh) (by
      intro lane hl
      have hLane : laneOf l (thread lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      simpa only [hLane] using firstShuffleOut hp (cur.checkpoint lane hl))
    (.inr hFollow) hPc
  exact ⟨ends, next, hAdvance hFollow⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
