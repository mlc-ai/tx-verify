-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleEntry
public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupRoute
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.PrologueStartupUnique
import Kernels.TmlFa4Fwd.Proof.PrologueFenceProgress
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Lemmas.Flow.NotShfl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue

private def earlyShuffle (i : Instr) (pc : Nat) : Bool :=
  !i.op.isShfl || decide (pc < 36 ∨ 174 ≤ pc ∧ pc < 3103 ∧ pc ∉ registerHintSites)

private theorem earlyShuffleAt {pc : Nat} {i : Instr} (hPc : pc < 3111)
    (hc : kernel.code[pc]? = some i) (hShfl : i.op.isShfl = true) :
    pc < 36 ∨ 174 ≤ pc ∧ pc < 3103 ∧ pc ∉ registerHintSites := by
  let code := (kernel.code.take 3111).zipIdx
  have hAll : code.all (fun (i, pc) => earlyShuffle i pc) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hm : (i,pc) ∈ code := by
    apply List.mem_of_getElem? (i := pc)
    dsimp only [code]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt hPc, hc, Nat.zero_add]
    rfl
  simpa only [earlyShuffle, hShfl, Bool.not_true, Bool.false_or, decide_eq_true_eq] using
    List.all_eq_true.mp hAll _ hm

private theorem shuffleAfterBroadcasts {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {e : Event} (he : X.get (g,j) = some e)
    (hIndex : 3 ≤ j) (hWarp : warpIndex l g < 8)
    (hShuffle : Execution.isShfl e = true) : 3110 < e.pc := by
  have hg := event_thread_lt hX he
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hThree : 3 ≤ (X.tr g).length := by omega
  obtain ⟨_, _, _, heq⟩ := broadcastTraceSplit hThree
  obtain ⟨t, o, ht, _, _, _, _, _, _, hr⟩ := broadcastPrefix hp hX g hg heq
  have he' : ((X.tr g).drop 3)[j-3]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  have h36 : 36 ≤ e.pc := runAtOrPastStartupPc (by decide) (by rw [ht])
    hr e (List.mem_of_getElem? he')
  obtain ⟨s, result, _, hEvent⟩ := hr.before_event he'
  cases result with
  | none =>
    obtain ⟨_, _, hFire⟩ := hEvent
    rcases fires_none_ends hFire with ⟨_, hb⟩ | hb <;>
      obtain ⟨_, kind⟩ := e <;> cases hb <;> cases hShuffle
  | some u =>
    obtain ⟨ins, hc, _, hf⟩ := estep_event_source hEvent
    have hSource := estep_source_pc hEvent
    by_contra! hBefore
    have hEarly := (earlyShuffleAt (by omega) hc (fires_shfl_op hf hShuffle)).resolve_left
      (by omega)
    rw [← hSource] at hEarly
    have hRole := roleBodyPcOfEvent hp hX he (by omega) hEarly.2.2
    simp only [roleBodyPc, show ¬ 14 ≤ warpIndex l g by omega,
      show warpIndex l g ≠ 13 by omega, show warpIndex l g ≠ 12 by omega,
      hWarp, ↓reduceIte] at hRole
    omega

/-- The cumulative-query word read by the scheduler or zero beyond the batch sentinel. -/
def schedulerInputWord (p : Params) (lane : Nat) : Nat :=
  if lane ≤ p.batch then p.qOffset lane else 0

/-- The scheduler register frame before the first warp shuffle. -/
def schedulerFirstWarpFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8)
    (lane : Nat) : List (Nat × Value) :=
  schedulerLane p l (warpLane l g lane) warp (schedulerInputWord p lane)

/-- Even on an unfinished execution, a later softmax observation establishes a
whole-warp scheduler checkpoint after the first down shuffle. -/
theorem firstSchedulerWarpOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src index : Nat} {target : Event} (hg : g < l.threads) (hWarp : warpIndex l g < 8)
    (hSrc : src < 32)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    (hEvent : X.get (warpLane l g src,index) = some target) (hPc : 3111 < target.pc) :
    let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
    ∃ (ends : Nat → Option TState)
      (cur : SchedulerWarpAt l X g 3112
        (fun lane => (2683, b32 (schedulerInputWord p (shflSource .down lane 1 31).1)) ::
          schedulerFirstWarpFacts p l g warp lane) 4 0 ends),
      WarpFollowsEvent l X g cur.pos src index target := by
  dsimp only
  classical
  let thread := warpLane l g
  let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
  let F := schedulerFirstWarpFacts p l g warp
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSame (lane : Nat) (hl : lane < 32) : SameWarp l g (thread lane) :=
    (Step.sameWarp_lane hBlock hg hl).1
  have fits {lane : Nat} (hl : lane < 32) : warpIndex l (thread lane) < 8 := by
    have hEq : warpIndex l g = warpIndex l (thread lane) := (hSame lane hl).2
    exact hEq ▸ hWarp
  have cursorOf {lane j : Nat} {e : Event} (hl : lane < 32)
      (he : X.get (thread lane,j) = some e) (hLate : 3110 < e.pc) :
      ∃ pos t o, pos ≤ j ∧ beforeFirstScan X (thread lane) pos ∧ At t 3111 (F lane) ∧
        Run kernel Assumptions.all l (thread lane) t ((X.tr (thread lane)).drop pos) o := by
    obtain ⟨pos, t, o, hj, hCount, ht, hRun⟩ := firstSchedulerOperandOfEvent hp hX he hLate
      (fits hl) (hProtected _)
    have hLane : laneOf l (thread lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
    have hW : (⟨warpIndex l (thread lane), fits hl⟩ : Fin 8) = warp :=
      Fin.ext (hSame lane hl).2.symm
    refine ⟨pos, t, o, hj, hCount, ?_, hRun⟩
    simpa only [F, schedulerFirstWarpFacts, schedulerInputWord, hLane, hW] using ht
  obtain ⟨pos, t, o, hIndex, hCount, ht, hRun⟩ := cursorOf hSrc hEvent (by omega)
  have hNonempty : (X.tr (thread src)).drop pos ≠ [] := by
    intro h
    have hn : index < (X.tr (thread src)).length := (List.getElem?_eq_some_iff.mp hEvent).1
    exact Nat.not_le_of_lt hn ((List.drop_eq_nil_iff.mp h).trans hIndex)
  have hNext : Next kernel Assumptions.all l (thread src) t t (.shfl .down
      (b32 (schedulerInputWord p src)) 1 31 (fun x _ => next (setReg t 2683 x))) :=
    ⟨.refl, schedulerFirstShuffleOut hp ht⟩
  obtain ⟨recv, ok, he, hk, _⟩ := hNext.shuffle_at_nonempty hRun hNonempty hCount.1
  have peers (lane : Nat) (hl : lane < 32) :
      ∃ pos t o, beforeFirstScan X (thread lane) pos ∧ At t 3111 (F lane) ∧
        Run kernel Assumptions.all l (thread lane) t ((X.tr (thread lane)).drop pos) o ∧
        (∀ j < pos, ∀ pc, X.get (thread lane,j) ≠ some ⟨pc,.exit⟩) ∧
        (lane = src → pos ≤ index) := by
    by_cases hSelf : lane = src
    · subst lane
      refine ⟨pos, t, o, hCount, ht, hRun, ?_, fun _ => hIndex⟩
      intro j hj pc hExit
      have hLast := Execution.exit_last hX (hSame src hSrc).1.2.1 hExit
      have hLen : index < (X.tr (thread src)).length := (List.getElem?_eq_some_iff.mp hEvent).1
      omega
    have hPair := Step.sameWarp_trans (sameWarp_symm (hSame src hSrc)) (hSame lane hl)
    obtain ⟨j, e, hGet, hLate⟩ : ∃ j e, X.get (thread lane,j) = some e ∧ 3110 < e.pc := by
      rcases Step.shfl_lane_of_ready hX he hk hPair with ⟨j, hPeer⟩ | ⟨j, pc, hExit, _⟩
      · have hJ : 3 ≤ j :=
          hPeer.2.symm.le.trans ((List.countP_le_length ..).trans (List.length_take_le ..))
        obtain ⟨⟨pc, mode, a, b, c, value, ok, hGet⟩, _⟩ := hPeer
        exact ⟨j, _, hGet, shuffleAfterBroadcasts hp hX hGet hJ (fits hl) rfl⟩
      · have hExitPc := actualExitPc hX hExit
        exact ⟨j, _, hExit, by change 3110 < pc; omega⟩
    obtain ⟨q, state, last, hj, hc, hs, hr⟩ := cursorOf hl hGet hLate
    refine ⟨q, state, last, hc, hs, hr, ?_, fun h => (hSelf h).elim⟩
    intro k hk pc hExit
    have hEnd := Execution.exit_last hX (hSame lane hl).1.2.1 hExit
    have hLen : j < (X.tr (thread lane)).length := (List.getElem?_eq_some_iff.mp hGet).1
    omega
  let _ : Inhabited TState := ⟨{}⟩
  choose! positions states ends hBefore hs hr hNoExit hFollows using peers
  let cur : SchedulerWarpAt l X g 3111 F 3 0 ends :=
    ⟨positions, states, states, ⟨fun lane hl => (hBefore lane hl).1,
      fun lane hl => (hBefore lane hl).2⟩, hr, fun _ _ => .refl, hs⟩
  have hFollow : WarpFollowsEvent l X g cur.pos src index target :=
    ⟨hSrc, hEvent, hFollows src hSrc rfl, hNoExit⟩
  obtain ⟨next, hAdvance⟩ := cur.consumeShuffleTo hp hX hg (dst := 2683) .down
    (fun lane => b32 (schedulerInputWord p lane)) (fun _ => 1) (fun _ => 31)
    (fun _ _ => by simp [F, schedulerFirstWarpFacts, schedulerLane, schedulerEntry,
      dispatchOutput, dispatchInput])
    (fun lane hl => schedulerFirstShuffleOut hp (cur.checkpoint lane hl)) (.inr hFollow) hPc
  exact ⟨ends, next, hAdvance hFollow⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
