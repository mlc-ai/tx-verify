-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputWritebackRetireProgress
import Kernels.TmlFa4Fwd.Proof.EpilogueDrainEntry
import Lemmas.Step.ProtectedReadProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

/-- The initial drain word and the preserved writeback frame. -/
def firstDrainFrame (p : Params) (l : Launch) (g lane : Nat) : List (Nat × Value) :=
  (7229,b32 (drainCuQ p lane)) :: outputDrainFrame p l g lane

private theorem outputDrainFrameRegs (p : Params) (l : Launch) (g lane : Nat) :
    ∀ item ∈ outputDrainFrame p l g lane, item.1 ∉ [7872,7873,7229,2401] := by
  intro item hItem
  simp only [outputDrainFrame,schedulerStartupFrame,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hItem
  rcases hItem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> exact of_decide_eq_true rfl

private theorem firstDrainLane {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g lane batch head tile shuffles votes : Nat} (hg : g < l.threads) (hl : lane < 32)
    (hCuQ : DrainCuQProtected p X) {ending : Option TState}
    (cur : WritebackReached p l X (warpLane l g lane) batch head tile (outputDrainFrame p l g lane)
      ending none shuffles votes) :
    let thread := warpLane l g lane
    let pos := cur.pos + if lane ≤ p.batch then 1 else 0
    ∃ before state, At state 2990 (firstDrainFrame p l g lane) ∧
      out kernel Assumptions.all l thread state =
        .ev (.shfl .down (b32 (drainCuQ p lane)) 1 31 (fun v _ => next (setReg state 2401 v))) ∧
      0 < pos ∧ pos ≤ (X.tr thread).length ∧
      (pos = (X.tr thread).length → Step.Released l X thread) ∧
      ((X.tr thread).take pos).countP Execution.isShfl = shuffles ∧
      ((X.tr thread).take pos).countP isFullWarpVote = votes ∧
      Run kernel Assumptions.all l thread {} ((X.tr thread).take pos) (some before) ∧
      Run kernel Assumptions.all l thread before ((X.tr thread).drop pos) ending ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l thread) before state := by
  let thread := warpLane l g lane
  let word := b32 (drainCuQ p lane)
  have hSame := Step.sameWarp_lane (by rw [hp.block]) hg hl
  have hLane : laneOf l thread = lane := hSame.2
  have hModel {s : TState} (hLo : 2986 ≤ s.pc) (hHi : s.pc ≤ 2990) :
      out kernel Assumptions.all l thread s = out kernel [] l thread s :=
    epilogue_out_all_eq_nil (.inl ⟨by omega,by omega⟩)
  have hGate : cur.state.regs 307 = some (.pred (p.batch < laneOf l thread)) := by
    rw [hLane]
    exact holds_mem cur.saved (by simp [outputDrainFrame])
  have hReg : cur.state.regs 1201 = some (b32 (laneOf l thread)) := by
    rw [hLane]
    exact holds_mem cur.saved (by simp [outputDrainFrame])
  have hBase : cur.state.regs 7506 = some (b64 p.cuQBase) :=
    holds_mem cur.saved (by simp [outputDrainFrame])
  have hZero : cur.state.regs 7229 = some (b32 0) :=
    holds_mem cur.checkpoint.2.2.2.2 (by simp [writebackFacts,writebackEntry])
  rcases drainFirstEvent hp thread cur.state hModel cur.checkpoint.1 cur.checkpoint.2.2.2.1
    hGate hReg hBase hZero with ⟨hPast,u,hu,hNext⟩ | ⟨hRead,u,hu,hSub,hAcc,hFault,hFrame,hNext⟩
  · have hOther : ¬ lane ≤ p.batch := by rw [hLane] at hPast; omega
    have hWord : word = b32 0 := by simp [word,drainCuQ,hOther]
    simp only [ite_eq_right hOther,Nat.add_zero]
    refine ⟨cur.before,u,?_,?_,cur.positive,cur.bounded,cur.released,
      cur.shuffleCount,cur.voteCount,cur.recorded,cur.continuation,
      cur.localSteps.trans hNext.steps⟩
    · rw [hu]
      have hWord' : cur.state.regs 7229 = some word := by rw [hWord]; exact hZero
      exact ⟨rfl,cur.checkpoint.2.1,cur.checkpoint.2.2.1,cur.checkpoint.2.2.2.1,hWord',cur.saved⟩
    · simpa only [hLane] using hNext.stop
  · rw [hLane] at hRead
    simp only [ite_eq_left hRead]
    let a : Acc := {loc := globalLoc (p.cuQBase+4*lane),size := 4}
    have hn : Next kernel Assumptions.all l thread cur.before u (.read a (afterLoad u [7229])) :=
      ⟨cur.localSteps.trans hNext.steps,by simpa only [hLane] using hNext.stop⟩
    have hValue : word = b32 (p.qOffset lane) := by simp [word,drainCuQ,hRead]
    have hInit : HasValue m a.loc word := hValue ▸ hp.cuQ lane hRead
    obtain ⟨he,hRecorded,hRun⟩ := Step.protected_read_of_maximal hMax hSame.1.1.2.1
      (a := a) (value := word) rfl hInit (hCuQ lane hRead) hn cur.recorded cur.continuation
      cur.positive cur.bounded cur.released (Assumptions.wf_snoc_initial hMax.1)
    let v := afterLoad u [7229] (word.toBytes.map some)
    obtain ⟨hv,hvs,hva,hvf,hWord,hKeep,hNext⟩ :=
      drainAfterRead hp thread u (fun hp => hModel (by omega) (by omega)) hu hSub hAcc hFault
    simp only [hLane] at hWord hKeep hNext hv hvs hva hvf
    have hSaved : Holds v.regs (outputDrainFrame p l g lane) := by
      have hh (r : Nat) (hr : r ∈ (outputDrainFrame p l g lane).map Prod.fst) :
          v.regs r = cur.state.regs r := by
        obtain ⟨item,hm,rfl⟩ := List.mem_map.mp hr
        have hFree := outputDrainFrameRegs p l g lane item hm
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hFree
        exact (hKeep _ hFree.2.2.1).trans (hFrame _ hFree.1 hFree.2.1)
      exact holdsSchedulerFrame cur.saved hh (fun item hm => List.mem_map_of_mem hm)
    have hTake := List.take_succ_eq_append_getElem (len_of_get he)
    rw [(List.getElem?_eq_some_iff.mp he).2] at hTake
    change (X.tr thread).take (cur.pos+1) =
      (X.tr thread).take cur.pos ++ [⟨u.pc,.rd a (word.toBytes.map some)⟩] at hTake
    refine ⟨v,v,⟨hv,hvs,hva,hvf,hWord,hSaved⟩,hNext,Nat.succ_pos _,len_of_get he,
      releasedIfLast he (by intro h; cases h),?_,?_,hRecorded,hRun,.refl⟩
    · rw [hTake,List.countP_append,cur.shuffleCount]; rfl
    · rw [hTake,List.countP_append,cur.voteCount]; rfl

/-- The output drain starts with its actual protected lane words and a full-warp down shuffle. -/
theorem outputDrainDownOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hCuQ : DrainCuQProtected p X)
    (hDrain : OutputWritebackDrained p l X g) :
    ∃ shuffles ends, Nonempty (SchedulerWarpReached l X g 2991
      (fun lane => (2401,b32 (drainCuQ p (if lane+1 < 32 then lane+1 else lane))) ::
        firstDrainFrame p l g lane) (shuffles+1) 1 ends) := by
  classical
  obtain ⟨_,_,_,_,shuffles,ends,hLanes⟩ := hDrain
  let cur (lane : Nat) (hl : lane < 32) := Classical.choice (hLanes lane hl)
  let pos (lane : Nat) :=
    if hl : lane < 32 then (cur lane hl).pos + (if lane ≤ p.batch then 1 else 0)
    else 0
  let _ : Nonempty TState := ⟨(cur 0 (by decide)).state⟩
  have hEach (lane : Nat) (hl : lane < 32) : ∃ before state,
      At state 2990 (firstDrainFrame p l g lane) ∧
      out kernel Assumptions.all l (warpLane l g lane) state =
        .ev (.shfl .down (b32 (drainCuQ p lane)) 1 31 (fun v _ => next (setReg state 2401 v))) ∧
      0 < pos lane ∧ pos lane ≤ (X.tr (warpLane l g lane)).length ∧
      (pos lane = (X.tr (warpLane l g lane)).length → Step.Released l X (warpLane l g lane)) ∧
      ((X.tr (warpLane l g lane)).take (pos lane)).countP Execution.isShfl = shuffles ∧
      ((X.tr (warpLane l g lane)).take (pos lane)).countP isFullWarpVote = 1 ∧
      Run kernel Assumptions.all l (warpLane l g lane) {}
        ((X.tr (warpLane l g lane)).take (pos lane)) (some before) ∧
      Run kernel Assumptions.all l (warpLane l g lane) before
        ((X.tr (warpLane l g lane)).drop (pos lane)) (ends lane) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) before state := by
    simpa only [pos,dite_eq_left hl] using firstDrainLane hp hMax hg hl hCuQ (cur lane hl)
  choose! before state hAt hOut hPos hBound hRelease hSh hVote hPrefix hTail hLocal using hEach
  let ready : SchedulerWarpReached l X g 2990 (firstDrainFrame p l g) shuffles 1 ends :=
    ⟨⟨pos,before,state,⟨hSh,hVote⟩,hTail,hLocal,hAt⟩,hPos,hBound,hRelease,hPrefix⟩
  have hFresh : ∀ lane < 32, ∀ item ∈ firstDrainFrame p l g lane, item.1 ≠ 2401 := by
    intro lane _ item hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact of_decide_eq_true rfl
    · intro h
      exact outputDrainFrameRegs p l g lane item hi (by simp [h])
  obtain ⟨advanced⟩ := ready.consumeShuffle hp hMax hg .down (fun lane => b32 (drainCuQ p lane))
    (fun _ => 1) (fun _ => 31) hFresh hOut
  refine ⟨shuffles,ends,advanced.advanceLocal (pc' := 2991) ?_⟩
  intro lane hl
  refine ⟨advanced.state lane,.refl,?_⟩
  simpa only [shflSource_down_one, apply_ite Prod.fst] using advanced.checkpoint lane hl

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
