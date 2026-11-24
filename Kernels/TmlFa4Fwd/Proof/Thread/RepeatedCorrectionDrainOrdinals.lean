-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalDrainWarp
public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleWarpBackedge
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalDrainWarp
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalDrainStart
import Lemmas.Flow.RecordedCheckpointPath
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread Softmax

/-- Between the active tile and its LSE tail there is no shuffle. After
the first terminal statistics rendezvous there is also no further ballot. -/
private theorem tailCollectiveCount {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g batch i : Nat}
    {s₀ s : TState} (hi : i ≤ (X.tr g).length)
    (recorded : Run kernel Assumptions.all l g {} ((X.tr g).take i) (some s₀))
    (localPath : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s₀ s)
    (tail : LseTailReached p l X g batch) (vote : Bool)
    (pc : s.pc = if vote then 8466 else 7932) :
    let test := if vote then isFullWarpVote else Execution.isShfl
    ((X.tr g).take tail.cursor.pos).countP test = ((X.tr g).take i).countP test := by
  let floor := if vote then 8466 else 7932
  let bound : RowDrainSpan := ⟨floor,floor,floor⟩
  have floorPc : s.pc = floor := pc
  have lower : ∀ {a b : TState} {es : List Event},
      TraceReach kernel Assumptions.all l g a es b → floor ≤ a.pc → floor ≤ b.pc := by
    intro a b es path ha
    apply bound.traceAboveExit path _ _ ha
    · cases vote <;> set_option maxRecDepth 100000 in kernel_rfl
    · intro pc hm
      simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hm
      change pc < floor
      dsimp only [floor]
      split <;> omega
  have afterFloor {a b : TState} {es : List Event}
      (path : TraceReach kernel Assumptions.all l g a es b) (ha : floor ≤ a.pc) :
      ∀ e ∈ es, floor ≤ e.pc := by
    induction path with
    | refl => simp
    | tau ht _ ih => exact ih (lower (.tau ht (.refl _)) ha)
    | event he _ ih =>
      intro e hm
      rcases List.mem_cons.mp hm with rfl | hm
      · obtain ⟨_,_,fires⟩ := he
        rwa [fires_pc fires]
      · exact ih (lower (.event he (.refl _)) ha) e hm
  let last : RowDrainSpan := ⟨9083,9083,9083⟩
  have noBack (es : List Event) :
      ¬ TraceReach kernel Assumptions.all l g tail.cursor.ready es s := by
    intro path
    have h := last.traceAboveExit path (by set_option maxRecDepth 100000 in kernel_rfl)
      (fun _ hm => beforeCorrectionDrain hm) tail.cursor.checkpoint.1.ge
    change 9083 ≤ s.pc at h
    rw [pc] at h
    split at h <;> omega
  obtain ⟨order,path⟩ := recordedCheckpointsPath hi tail.cursor.bounded recorded localPath
    tail.cursor.recorded tail.cursor.localSteps noBack
  let es := ((X.tr g).drop i).take (tail.cursor.pos-i)
  let test := if vote then isFullWarpVote else Execution.isShfl
  have none : es.countP test = 0 := by
    apply List.countP_eq_zero.mpr
    intro e hm
    have lo := afterFloor path floorPc.ge e hm
    have ⟨elo,ehi⟩ := correctionWorkEvents path (by rw [pc]; split <;> decide)
      tail.cursor.checkpoint.1 e hm
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hm
    have inside := (List.getElem?_eq_some_iff.mp hj).1.trans_le (List.length_take_le ..)
    change (((X.tr g).drop i).take (tail.cursor.pos-i))[j]? = some e at hj
    rw [List.getElem?_take_of_lt inside,List.getElem?_drop] at hj
    obtain ⟨hs,hv⟩ := correctionWorkCollectives hX hj elo ehi
    cases vote
    · simp [test,hs]
    · change isFullWarpVote e ≠ true
      change 8466 ≤ e.pc at lo
      intro he
      rcases hv he with h | h <;> omega
  have splitAt := List.take_add (l := X.tr g) (i := i) (j := tail.cursor.pos-i)
  rw [Nat.add_sub_of_le order] at splitAt
  change _ = ((X.tr g).take i).countP test
  rw [splitAt,List.countP_append,none,Nat.add_zero]

theorem terminalFirstDownOfRescales {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch votes tensor : Nat} (hg : g < l.threads)
    (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hb : batch < p.batch) (lo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hi : g/l.block < tilePrefix p (batch+1)*p.heads) (hCuQ : DrainCuQProtected p X)
    (warp : RescaleWarpTerminal p l X g batch votes tensor)
    (tails : ∀ lane < 32, Nonempty (LseTailReached p l X (warpLane l g lane) batch)) :
    ∃ n ends, Nonempty (SchedulerWarpReached l X g 9091
      (fun lane => (7082,b32 (drainCuQ p (shflSource .down lane 1 31).1)) ::
        terminalFirstFrame p l (warpLane l g lane)) (n+1) votes ends) := by
  obtain ⟨n,_,⟨init⟩⟩ := activeTileOfMaximal hp hMax hg hw.1 hw.2 hCuQ hb lo hi
  refine ⟨n,terminalFirstDownOfOrdinals hp hMax hg hw hCuQ (fun lane hl tail => ?_) tails⟩
  have hSh := tailCollectiveCount hMax.1 (init.bounded lane hl) (init.recorded lane hl)
    (init.localSteps lane hl) tail false (init.checkpoint lane hl).1
  refine ⟨hSh.trans (init.ordinals.shfl lane hl),?_⟩
  let h := warpLane l g lane
  have hs : SameWarp l g h := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
  have self : warpLane l h (laneOf l h) = h :=
    Step.warpLane_of_sameWarp ⟨⟨hs.1.2.1,hs.1.2.1,rfl⟩,rfl⟩
  let c := warp.lane h hs
  obtain ⟨e,he,ha⟩ := c.waited
  have kind := correctionStatsWait hp hMax.1 he ha
  rw [self] at he
  have past : Run kernel Assumptions.all l h {} ((X.tr h).take (c.index+1)) (some c.state) := by
    simpa only [self] using c.recorded
  have hv := tailCollectiveCount hMax.1 (Nat.succ_le_of_lt (len_of_get he)) past .refl
    tail true c.ready.1
  have noVote : isFullWarpVote e = false := by
    obtain ⟨pc,k⟩ := e
    change k = _ at kind
    subst k
    rfl
  exact hv.trans ((countP_take_succ_false he noVote).trans (warp.rank h hs).2)

end PTX.Kernels.TmlFa4Fwd.Correction
