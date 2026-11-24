-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalDrainStart
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalDrainStart
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionBallotWindow
import Lemmas.Flow.RecordedCheckpointPath
import Lemmas.Flow.NotShfl
import Lemmas.Flow.WaitTmpl
import Kernels.TmlFa4Fwd.Flow.Code.Part142

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread Softmax

private theorem correctionWorkEvents {l : Launch} {g : Nat}
    {s t : TState} {events : List Event}
    (hPath : TraceReach kernel Assumptions.all l g s events t)
    (hStart : 7932 ≤ s.pc) (hEnd : t.pc = 9083) :
    ∀ e ∈ events, 7932 ≤ e.pc ∧ e.pc < 9084 := by
  let lo : RowDrainSpan := ⟨7932,7932,7932⟩
  let hi : RowDrainSpan := ⟨9084,9084,9084⟩
  have hLow {a b : TState} {es : List Event}
      (h : TraceReach kernel Assumptions.all l g a es b) (ha : 7932 ≤ a.pc) :
      7932 ≤ b.pc :=
    lo.traceAboveExit h (by set_option maxRecDepth 100000 in kernel_rfl)
      (by
        intro pc hm
        simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hm
        change pc < 7932
        omega)
      ha
  have hUpper {a : TState} {es : List Event}
      (h : TraceReach kernel Assumptions.all l g a es t) : a.pc < 9084 := by
    by_contra! ha
    have hh := hi.traceAboveExit h (by set_option maxRecDepth 100000 in kernel_rfl)
      (fun _ hm => (beforeCorrectionDrain hm).trans (by decide)) ha
    change 9084 ≤ t.pc at hh
    omega
  induction hPath with
  | refl => simp
  | tau hs _ ih => exact ih (hLow (.tau hs (.refl _)) hStart) hEnd hUpper
  | event he hRest ih =>
    intro e hm
    rcases List.mem_cons.mp hm with rfl | hm
    · have hBefore := hUpper (.event he hRest)
      obtain ⟨_,_,hFires⟩ := he
      rw [fires_pc hFires]
      exact ⟨hStart,hBefore⟩
    · exact ih (hLow (.event he (.refl _)) hStart) hEnd hUpper e hm

private theorem correctionWorkCollectives {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {e : Event}
    (he : X.get (g,j) = some e) (hLo : 7932 ≤ e.pc) (hHi : e.pc < 9084) :
    Execution.isShfl e = false ∧
      (isFullWarpVote e = true → e.pc = 8009 ∨ e.pc = 8228) := by
  rcases get_source hX he with ⟨_,hf⟩ | ⟨_,ins,_,_,hc,hf⟩
  · obtain ⟨pc,kind⟩ := e
    change kind = _ at hf
    subst kind
    exact ⟨rfl,fun h => by cases h⟩
  have hTable : (((kernel.code.drop 7932).take (9084-7932)).zipIdx 7932).all
      (fun (i,pc) => !i.op.isShfl && (!voteDataOp i.op || (pc == 8009 || pc == 8228))) =
      true := by set_option maxRecDepth 100000 in kernel_rfl
  have hGet : (((kernel.code.drop 7932).take (9084-7932)).zipIdx 7932)[e.pc-7932]? =
      some (ins,e.pc) := by
    rw [List.getElem?_zipIdx,List.getElem?_take_of_lt (by omega),List.getElem?_drop,
      Nat.add_sub_of_le hLo,hc]
    rfl
  have hCode := List.all_eq_true.mp hTable _ (List.mem_of_getElem? hGet)
  simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at hCode
  refine ⟨?_,?_⟩
  · cases hShfl : Execution.isShfl e
    · rfl
    · have hBad := hCode.1
      rw [fires_shfl_op hf hShfl] at hBad
      cases hBad
  · intro hv
    exact hCode.2.resolve_left (by rw [fires_voteData_op hf (fullBallotIsVoteData hv)]; decide)

private theorem singleVisitDrainOrdinals {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch shuffles : Nat} {ends : Nat → Option TState}
    (c : SchedulerWarpReached l X g 7932 (correctionActiveTileFacts p l g batch) shuffles 1 ends)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*i)).at k))
    {lane : Nat} (hl : lane < 32) (d : LseTailReached p l X (warpLane l g lane) batch) :
    ((X.tr (warpLane l g lane)).take d.cursor.pos).countP Execution.isShfl = shuffles ∧
      ((X.tr (warpLane l g lane)).take d.cursor.pos).countP isFullWarpVote = 1 := by
  let span : RowDrainSpan := ⟨9083,9083,9083⟩
  let thread := warpLane l g lane
  let stop := d.cursor
  have hNoBack (events : List Event) :
      ¬ TraceReach kernel Assumptions.all l thread stop.ready events (c.state lane) := by
    intro h
    have hPc := span.traceAboveExit h (by set_option maxRecDepth 100000 in kernel_rfl)
      (fun _ hm => beforeCorrectionDrain hm) stop.checkpoint.1.ge
    change 9083 ≤ (c.state lane).pc at hPc
    rw [(c.checkpoint lane hl).1] at hPc
    omega
  obtain ⟨hOrder,hPath⟩ := recordedCheckpointsPath (c.bounded lane hl) stop.bounded
    (c.recorded lane hl) (c.localSteps lane hl) stop.recorded stop.localSteps hNoBack
  let tail := ((X.tr thread).drop (c.pos lane)).take (stop.pos-c.pos lane)
  have hTail (e : Event) (hm : e ∈ tail) :
      Execution.isShfl e = false ∧ isFullWarpVote e = false := by
    have ⟨hElo,hEhi⟩ := correctionWorkEvents hPath (c.checkpoint lane hl).1.ge
      stop.checkpoint.1 e hm
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hm
    have hi' := (List.getElem?_eq_some_iff.mp hi).1.trans_le (List.length_take_le ..)
    change (((X.tr thread).drop (c.pos lane)).take (stop.pos-c.pos lane))[i]? = some e at hi
    rw [List.getElem?_take_of_lt hi',List.getElem?_drop] at hi
    have he : X.get (thread,c.pos lane+i) = some e := hi
    obtain ⟨hs,hv⟩ := correctionWorkCollectives hX he hElo hEhi
    refine ⟨hs,?_⟩
    cases hVote : isFullWarpVote e
    · rfl
    · have hSite := hv hVote
      have hPast : WarpFollowsEvent l X g c.pos lane (c.pos lane+i) e := by
        refine ⟨hl,he,by omega,?_⟩
        intro peer hPeer j hj pc hExit
        have hm : (⟨pc,.exit⟩ : Event) ∈ (X.tr (warpLane l g peer)).take (c.pos peer) := by
          apply List.mem_of_getElem?
          rw [List.getElem?_take_of_lt hj]
          exact hExit
        exact PTX.Flow.Run.no_end (c.recorded peer hPeer) _ hm (.inr rfl)
      have hBound : 7988 < e.pc := by rcases hSite with h | h <;> omega
      let stage : Fin 2 := if e.pc = 8009 then 0 else 1
      have hLimit := rescaleBallotWholeBoundOfActive hp hX c.toSchedulerWarpAt hPast
        hb hLo hHi hUsedK hBound stage
      have hIs : isRescaleStageVote stage e = true := by
        rcases hSite with h | h <;>
          simp [stage,isRescaleStageVote,correctionRescaleMarkPc,barrierMark,h]
      have hCount : 0 < (X.tr thread).countP (isRescaleStageVote stage) := by
        have hm := List.mem_of_getElem? he
        by_contra! hz
        exact (List.countP_eq_zero.mp (Nat.eq_zero_of_le_zero hz) e hm) hIs
      rw [hSingle] at hLimit
      exact (Nat.not_lt_of_ge (show (X.tr thread).countP (isRescaleStageVote stage) ≤ 0
        from hLimit) hCount).elim
  have hSplit := List.take_add (l := X.tr thread) (i := c.pos lane) (j := stop.pos-c.pos lane)
  rw [Nat.add_sub_of_le hOrder] at hSplit
  have hS : tail.countP Execution.isShfl = 0 := List.countP_eq_zero.mpr
    (fun e hm he => by rw [(hTail e hm).1] at he; cases he)
  have hV : tail.countP isFullWarpVote = 0 := List.countP_eq_zero.mpr
    (fun e hm he => by rw [(hTail e hm).2] at he; cases he)
  rw [hSplit,List.countP_append,List.countP_append,c.ordinals.shfl lane hl,
    c.ordinals.vote lane hl,hS,hV,Nat.add_zero,Nat.add_zero]
  exact ⟨rfl,rfl⟩

/-- The first terminal scan uses the protected endpoint and the original lane guard. -/
def terminalFirstFrame (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  (685,.pred (!decide (laneHasRequest (laneOf l g) p.batch))) ::
    (7279,b32 (drainCuQ p (laneOf l g))) :: RowDrainRole.correction.roots p l g

/-- A correction warp exchanges its first terminal endpoints once its ordinals match. -/
theorem terminalFirstDownOfOrdinals {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hCuQ : DrainCuQProtected p X) {n votes : Nat}
    (ordinals : ∀ lane < 32, ∀ tail : LseTailReached p l X (warpLane l g lane) batch,
      ((X.tr (warpLane l g lane)).take tail.cursor.pos).countP Execution.isShfl = n ∧
      ((X.tr (warpLane l g lane)).take tail.cursor.pos).countP isFullWarpVote = votes)
    (tails : ∀ lane < 32, Nonempty (LseTailReached p l X (warpLane l g lane) batch)) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 9091
      (fun lane =>
        (7082,b32 (drainCuQ p (shflSource .down lane 1 31).1)) ::
          terminalFirstFrame p l (warpLane l g lane)) (n+1) votes ends) := by
  classical
  let thread := warpLane l g
  let F := fun lane => terminalFirstFrame p l (thread lane)
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have schedule (lane : Nat) (hl : lane < 32) :
      ∃ c : OpeningTripCursor l X (thread lane) 9090 (F lane),
        ((X.tr (thread lane)).take c.pos).countP Execution.isShfl = n ∧
        ((X.tr (thread lane)).take c.pos).countP isFullWarpVote = votes := by
    have ⟨hSame,_⟩ := Step.sameWarp_lane hBlock hg hl
    have hWarp : warpIndex l g = warpIndex l (thread lane) := hSame.2
    have hRole : 8 ≤ warpIndex l (thread lane) ∧ warpIndex l (thread lane) < 12 := hWarp ▸ hw
    obtain ⟨tail⟩ := tails lane hl
    obtain ⟨d,hShfl,hVote⟩ := tail.drainFirstWordOfMaximal hp hMax hCuQ hSame.1.2.1 hRole
    have hGuard := terminalDrainKeepsFirstGuard hp hMax hCuQ hSame.1.2.1 hRole d
    have hRegs : Holds d.ready.regs (F lane) := ⟨hGuard.1,d.checkpoint.2.2.2.2⟩
    obtain ⟨hs,hv⟩ := ordinals lane hl tail
    exact ⟨withFrame d hRegs,hShfl.trans hs,hVote.trans hv⟩
  let c (lane : Nat) (hl : lane < 32) := Classical.choose (schedule lane hl)
  let pos : Nat → Nat := fun lane => if hl : lane < 32 then (c lane hl).pos else 0
  let before : Nat → TState := fun lane => if hl : lane < 32 then (c lane hl).before else {}
  let state : Nat → TState := fun lane => if hl : lane < 32 then (c lane hl).ready else {}
  let ends : Nat → Option TState := fun lane => if hl : lane < 32 then (c lane hl).ending else none
  have hPos (lane : Nat) (hl : lane < 32) : pos lane = (c lane hl).pos := dite_eq_left hl
  have hBefore (lane : Nat) (hl : lane < 32) : before lane = (c lane hl).before := dite_eq_left hl
  have hState (lane : Nat) (hl : lane < 32) : state lane = (c lane hl).ready := dite_eq_left hl
  have hEnds (lane : Nat) (hl : lane < 32) : ends lane = (c lane hl).ending := dite_eq_left hl
  let cur : SchedulerWarpReached l X g 9090 F n votes ends := ⟨⟨pos,before,state,
    ⟨fun lane hl => by rw [hPos lane hl]; exact (Classical.choose_spec (schedule lane hl)).1,
     fun lane hl => by rw [hPos lane hl]; exact (Classical.choose_spec (schedule lane hl)).2⟩,
    fun lane hl => by rw [hBefore lane hl,hPos lane hl,hEnds lane hl]; exact (c lane hl).remaining,
    fun lane hl => by rw [hBefore lane hl,hState lane hl]; exact (c lane hl).localSteps,
    fun lane hl => by rw [hState lane hl]; exact (c lane hl).checkpoint⟩,
    fun lane hl => by dsimp only; rw [hPos lane hl]; exact (c lane hl).positive,
    fun lane hl => by dsimp only; rw [hPos lane hl]; exact (c lane hl).bounded,
    fun lane hl => by dsimp only; rw [hPos lane hl]; exact (c lane hl).released,
    fun lane hl => by dsimp only; rw [hPos lane hl,hBefore lane hl]; exact (c lane hl).recorded⟩
  obtain ⟨down⟩ := cur.consumeShuffle (dst := 7082) hp hMax hg .down
    (fun lane => b32 (drainCuQ p lane)) (fun _ => 1) (fun _ => 31)
    (fun _ _ => by simp [F,terminalFirstFrame,RowDrainRole.roots,RowDrainRole.batchReg,
      RowDrainRole.frame,RowDrainRole.laneReg,RowDrainRole.ctaReg])
    (by
      intro lane hl
      have ht := cur.checkpoint lane hl
      have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      have hReg : (cur.state lane).regs 7279 = some (b32 (drainCuQ p lane)) := by
        simpa only [F,terminalFirstFrame,thread,hLane] using ht.2.2.2.2.2.1
      have hCore := RowDrainRole.correction.drainCore (l := l) (g := thread lane)
        (s := cur.state lane) (by rw [ht.1]; decide) (by rw [ht.1]; decide)
      rw [hCore,out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_9090) rfl rfl]
      change Out.ev (shflTmpl l (thread lane) (cur.state lane) .down 7082 none
        (.reg 7279) (.imm 1) (.imm 31) (.imm (-1))) = _
      simp [shflTmpl,readValue,readReg,hReg,hBlock,b32,Value.bytes,readBits,pure,Except.pure]
      rfl)
  exact ⟨ends,⟨down⟩⟩

/-- The actual single-visit correction warp exchanges its first terminal endpoints. -/
theorem terminalFirstDownOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hCuQ : DrainCuQProtected p X)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*i)).at k))
    (tails : ∀ lane < 32, Nonempty (LseTailReached p l X (warpLane l g lane) batch)) :
    ∃ n ends, Nonempty (SchedulerWarpReached l X g 9091
      (fun lane =>
        (7082,b32 (drainCuQ p (shflSource .down lane 1 31).1)) ::
          terminalFirstFrame p l (warpLane l g lane)) (n+1) 1 ends) := by
  obtain ⟨n,_,⟨init⟩⟩ := activeTileOfMaximal hp hMax hg hw.1 hw.2 hCuQ hb hLo hHi
  refine ⟨n,terminalFirstDownOfOrdinals hp hMax hg hw hCuQ (fun _ hl tail => ?_) tails⟩
  exact singleVisitDrainOrdinals hp hMax.1 init hb hLo hHi hSingle hUsedK hl tail

end PTX.Kernels.TmlFa4Fwd.Correction
