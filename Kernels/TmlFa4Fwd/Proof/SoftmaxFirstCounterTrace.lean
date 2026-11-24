-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.SoftmaxActiveGeometry
public import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Flow.Code.Part053
import Kernels.TmlFa4Fwd.Flow.Code.Part068
import Kernels.TmlFa4Fwd.Flow.Code.Part078
import Lemmas.Step.ExitLast
import Lemmas.Flow.MarkedCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Epilogue

noncomputable section

private def keepsFirstNotice (pc : Nat) (op : Op) : Bool :=
  match op with
  | .bra dst _ => decide (pc ≤ 4397 ↔ dst ≤ 4397)
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem firstNoticeCode :
    (((kernel.code.drop 3425).take (5006-3425)).zipIdx 3425).all
      (fun p => keepsFirstNotice p.2 p.1.op) = true := by kernel_rfl

private theorem markerAt {pc : Nat} {ins : Instr}
    (hLo : 3425 ≤ pc) (hHi : pc < 5006) (hc : kernel.code[pc]? = some ins) :
    keepsFirstNotice pc ins.op = true := by
  apply List.all_eq_true.mp firstNoticeCode (ins,pc)
  apply List.mem_of_getElem? (i := pc-3425)
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem segmentKeepsFirstNotice {pc : Nat} {m : SegMatch CuteSlot}
    (hs : pc ∈ Assumptions.swExp2Sites) (hm : cuteExp2.matchAt kernel pc = some m) :
    pc ≤ 4397 ↔ m.stop ≤ 4397 := by
  have hAll : Assumptions.swExp2Sites.all (fun pc =>
      match cuteExp2.matchAt kernel pc with
      | some m => decide (pc ≤ 4397 ↔ m.stop ≤ 4397)
      | none => false) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAll pc hs
  rw [hm] at h
  exact of_decide_eq_true h

private def firstCounterRegion (origin t : TState) : Prop :=
  3425 ≤ t.pc ∧ t.pc ≤ 5006 ∧ t.sub ≤ 3 ∧
    (t.pc = 5006 → t.fault = none) ∧ ScoreScratchState t ∧
    ∀ r ∈ [1225,1226,1228,1229], t.regs r = origin.regs r

private theorem firstCounterStep {l : Launch} {g : Nat} {origin s u : TState}
    {ev : Option Event} (hS : firstCounterRegion origin s) (hCut : s.pc ≠ 5006)
    (he : WStep kernel Assumptions.all l g s ev u) :
    firstCounterRegion origin u ∧ barrierRemaining 4397 s =
      ev.toList.countP (barrierMark 4397) + barrierRemaining 4397 u := by
  obtain ⟨hLo,hHi,hSub,_,hScratch,hRegs⟩ := hS
  have hLt : s.pc < 5006 := by omega
  obtain ⟨hl,hh,hs,hf,hKeep⟩ := windowStepFrame .firstRoundCounters hLo hLt hSub he
  simp only [windowSite, List.not_mem_nil, or_false] at hl hh hKeep
  refine ⟨⟨hl,hh,hs,fun hp => hf.resolve_right (fun he => hCut (he.symm.trans hp)),
    windowStepScratch .firstRoundCounters hLo hLt hSub he hScratch,
    fun r hr => (hKeep r hr).trans (hRegs r hr)⟩,?_⟩
  refine markedBarrierTransition ⟨_,Flow.code_4397,rfl,rfl⟩ ?_ ?_
    (fun m hm => segmentKeepsFirstNotice hm) he
  · intro ins dest uni hc hop
    simpa only [keepsFirstNotice, hop, decide_eq_true_eq] using markerAt hLo hLt hc
  · intro ins ix ds uni hc hop
    simpa [keepsFirstNotice, hop] using markerAt hLo hLt hc

/-- Any trace reaching the kernel return completes the first round and publishes statistics
once before entering the repeated rounds, preserving the computed loop geometry. -/
theorem firstCounterWalkOfLateEvent {l : Launch} {g blocks biasCap pastTile : Nat}
    {s : TState} {es : List Event} {vs : List Visit} {target : Event}
    (hs : At s 3425 (firstLoopGeometry blocks biasCap pastTile))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hExit : target ∈ es) (hLate : 7605 ≤ target.pc) :
    ∃ u before rest tail, es = before ++ rest ∧
      target ∈ rest ∧ before.countP (barrierMark 4397) = 1 ∧
      At u 5006 (firstLoopGeometry blocks biasCap pastTile) ∧
      Walk kernel Assumptions.all l g u rest tail ∧
      ∀ e ∈ before, e.pc < 5006 := by
  have hS : firstCounterRegion s s := ⟨hs.1.ge,by rw [hs.1]; decide,
    by rw [hs.2.1]; decide,fun _ => hs.2.2.2.1,
    scratchStateOfClear ⟨hs.2.1,hs.2.2.1⟩,fun _ _ => rfl⟩
  obtain ⟨u,before,rest,tail,hEs,hRest,hU,hCut,hCount,hSpan,hWalk⟩ :=
    hw.cut_marked_where (P := firstCounterRegion s) (cut := fun t => t.pc = 5006)
      (good := fun e => e.pc < 5006)
      (barrierRemaining 4397) (barrierMark 4397)
      (fun t _ h => by simp [barrierRemaining,h]) firstCounterStep
      (fun ht hn he => (estep_source_pc he).symm ▸ lt_of_le_of_ne ht.2.1 hn)
      hS hExit
      (fun t ht _ => by
        intro h
        change t.pc = target.pc at h
        have hh := ht.2.1
        omega)
  have hF := holdsSchedulerFrame hs.2.2.2.2 hU.2.2.2.2.2 (fun _ h => by
    simpa [firstLoopGeometry] using List.mem_map_of_mem (f := Prod.fst) h)
  have hClear := scratchClearOfLocal (hCut.symm ▸ Flow.code_5006) rfl hU.2.2.2.2.1
  exact ⟨u,before,rest,tail,hEs,hRest,by simpa [barrierRemaining,hs.1] using hCount,
    ⟨hCut,hClear.1,hClear.2,hU.2.2.2.1 hCut,hF⟩,hWalk,hSpan⟩

private theorem ackFrame {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : 3418 ≤ s.pc) (hHi : s.pc < 3423)
    (hSub : s.sub = 0) (hAcc : s.acc = []) (hF : s.fault = none)
    (he : WStep kernel Assumptions.all l g s ev u) :
    u.sub = 0 ∧ u.acc = [] ∧ u.fault = none := by
  rcases he with ⟨rfl,hT⟩ | ⟨e,rfl,hE⟩
  · obtain ⟨ins,_,_,hStep⟩ := tauScoreSource hT
    rcases hStep with ⟨rfl,_⟩ | ⟨_,_,hExec⟩
    · exact ⟨rfl,rfl,hF⟩
    have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hLocal := (scoreExecLocal hExec).resolve_right
      (fun ⟨_,hm,_⟩ => hOff hm)
    exact ⟨hLocal.sub.trans hSub,hLocal.acc.trans hAcc,hLocal.fault.trans hF⟩
  · obtain ⟨ins,hc,hLocal,hFire⟩ := estep_event_source hE
    have hCode : ∃ dst base off par acq scope, ins.op = .mbarWait dst base off par acq scope := by
      generalize hPc : s.pc = pc at hLo hHi hc
      interval_cases pc
      · rw [Flow.code_3418] at hc
        obtain rfl := Option.some.inj hc.symm
        cases hLocal
      · rw [Flow.code_3419] at hc
        obtain rfl := Option.some.inj hc.symm
        cases hLocal
      · rw [Flow.code_3420] at hc
        obtain rfl := Option.some.inj hc.symm
        exact ⟨_,_,_,_,_,_,rfl⟩
      · rw [Flow.code_3421] at hc
        obtain rfl := Option.some.inj hc.symm
        cases hLocal
      · rw [Flow.code_3422] at hc
        obtain rfl := Option.some.inj hc.symm
        cases hLocal
    obtain ⟨dst,base,off,par,acq,scope,hop⟩ := hCode
    rw [hop] at hFire
    obtain ⟨_,_,_,_,_,rfl⟩ := fires_wait hFire
    exact ⟨hSub,hAcc,hF⟩

private def ackRegion (origin t : TState) : Prop :=
  3418 ≤ t.pc ∧ t.pc ≤ 3423 ∧ t.sub = 0 ∧ t.acc = [] ∧ t.fault = none ∧
    ∀ r ∈ [1225,1226,1228], t.regs r = origin.regs r

private theorem cutFirstAck {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {target : Event} (hs : s.pc = 3418)
    (hSub : s.sub = 0) (hAcc : s.acc = []) (hf : s.fault = none)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hExit : target ∈ es) (hLate : 7605 ≤ target.pc) :
    ∃ u before rest tail, es = before ++ rest ∧
      target ∈ rest ∧ u.pc = 3423 ∧ ackRegion s u ∧
      Walk kernel Assumptions.all l g u rest tail := by
  have hS : ackRegion s s := ⟨hs.ge,by omega,hSub,hAcc,hf,fun _ _ => rfl⟩
  obtain ⟨u,before,rest,tail,hEs,hRest,hU,hCut,_,hWalk⟩ :=
    hw.cut_marked (P := ackRegion s) (cut := fun t => t.pc = 3423)
      (fun _ => 0) (fun _ => false) (by intros; rfl)
      (fun {t u ev} hT hNe he => by
        obtain ⟨hl,hh,hs,ha,hf,hR⟩ := hT
        have hlt : t.pc < 3423 := by omega
        obtain ⟨hl',hh',_,_,hKeep⟩ := windowStepFrame .firstGeometryCounters hl hlt
          (hs.symm ▸ Nat.zero_le _) he
        simp only [windowSite, List.not_mem_nil, or_false] at hl' hh' hKeep
        obtain ⟨hs,ha,hf⟩ := ackFrame hl hlt hs ha hf he
        exact ⟨⟨hl',hh',hs,ha,hf,fun r hr => (hKeep r hr).trans (hR r hr)⟩,by
          cases ev <;> rfl⟩) hS hExit (fun t ht _ h => by
        change t.pc = target.pc at h
        have hh := ht.2.1
        omega)
  exact ⟨u,before,rest,tail,hEs,hRest,hCut,hU,hWalk⟩

private theorem setupFirstCounter (l : Launch) (g blocks cap past : Nat) (hPos : 0 < blocks)
    (hb : blocks < 2^31) :
    Seg kernel Assumptions.all l g 2 3423 [(1225,b32 (past+256)), (1226,b32 blocks),
      (1228,b32 cap)] 3425 (firstLoopGeometry blocks cap past) := by
  intro t ht
  simp only [firstLoopGeometry]
  seg_fp ht using norm_bits

/-- The real request geometry survives the first correction poll and the complete first
softmax pass. Exiting forces that pass to have issued exactly one statistics publication. -/
theorem firstGeometryCounterWalkOfLateEvent {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch tile : Nat} (stage : Fin 2) (hb : batch < p.batch)
    (hTile : 256*tile < p.qLength batch)
    {s : TState} {es : List Event} {vs : List Visit} {target : Event}
    (hs : At s 3418 (firstGeometryFacts p batch tile stage))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hExit : target ∈ es) (hLate : 7605 ≤ target.pc) :
    let blocks := Mma.trips p batch tile
    let cap := blocks-stageGeometryBlocks p batch tile stage+10
    let past := p.kLength batch-p.qLength batch+256*tile
    ∃ u waits before rest tail, es = waits ++ before ++ rest ∧
      target ∈ rest ∧ before.countP (barrierMark 4397) = 1 ∧
      At u 5006 (firstLoopGeometry blocks cap past) ∧
      Walk kernel Assumptions.all l g u rest tail ∧
      ∀ e ∈ before, e.pc < 5006 := by
  dsimp only
  let blocks := Mma.trips p batch tile
  let cap := blocks-stageGeometryBlocks p batch tile stage+10
  let past := p.kLength batch-p.qLength batch+256*tile
  obtain ⟨v,waits,rest,tail,hEs,hExit',hPc,hV,hWalk⟩ :=
    cutFirstAck hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hw hExit hLate
  have hpast : p.kLength batch-p.qLength batch + 256*(tile+1) = past+256 := by
    dsimp [past]
    omega
  have hEntry : At v 3423 [(1225,b32 (past+256)), (1226,b32 blocks), (1228,b32 cap)] := by
    refine ⟨hPc,hV.2.2.1,hV.2.2.2.1,hV.2.2.2.2.1,?_,?_,?_,trivial⟩
    · rw [← hpast]
      exact (hV.2.2.2.2.2 _ (by decide)).trans
        (holds_mem hs.2.2.2.2 (by simp [firstGeometryFacts]))
    · exact (hV.2.2.2.2.2 _ (by decide)).trans
        (holds_mem hs.2.2.2.2 (by simp [firstGeometryFacts, blocks]))
    · exact (hV.2.2.2.2.2 _ (by decide)).trans
        (holds_mem hs.2.2.2.2 (by simp [firstGeometryFacts, blocks, cap]))
  have hBounds := firstGeometryBounds hp stage hb hTile (lane := 0) (by decide)
  obtain ⟨w,hRun,hwAt⟩ := (setupFirstCounter l g blocks cap past hBounds.1 hBounds.2.1).apply hEntry
  rcases Mma.advanceWalkLocals hRun hWalk with rfl | ⟨_,_,_,hBody⟩
  · cases hExit'
  obtain ⟨u,body,last,out,hSplit,hIn,hCount,hAt,hOut,hSpan⟩ :=
    firstCounterWalkOfLateEvent hwAt hBody hExit' hLate
  exact ⟨u,waits,body,last,out,by rw [hEs,hSplit,List.append_assoc],hIn,hCount,
    hAt,hOut,hSpan⟩

theorem firstGeometryCounterWalk {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch tile : Nat} (stage : Fin 2) (hb : batch < p.batch)
    (hTile : 256*tile < p.qLength batch) {s : TState} {es : List Event} {vs : List Visit}
    (hs : At s 3418 (firstGeometryFacts p batch tile stage))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hExit : (⟨9205,.exit⟩ : Event) ∈ es) :
    let blocks := Mma.trips p batch tile
    let cap := blocks-stageGeometryBlocks p batch tile stage+10
    let past := p.kLength batch-p.qLength batch+256*tile
    ∃ u waits before rest tail, es = waits ++ before ++ rest ∧
      (⟨9205,.exit⟩ : Event) ∈ rest ∧ before.countP (barrierMark 4397) = 1 ∧
      At u 5006 (firstLoopGeometry blocks cap past) ∧
      Walk kernel Assumptions.all l g u rest tail ∧
      ∀ e ∈ before, e.pc < 5006 :=
  firstGeometryCounterWalkOfLateEvent hp stage hb hTile hs hw hExit (by decide)

/-- The active softmax trace reaches repeated processing with the same trip count
as the assigned tile and has already published the first block's statistics. -/
theorem activeCountersOfExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src index pc : Nat} (hg : g < l.threads) (hWarp : Prologue.warpIndex l g < 8)
    (hSrc : src < 32) (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hCuQ : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4*i)).at k))
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k))
    (he : X.get (warpLane l g src,index) = some ⟨pc,.exit⟩) :
    let stage := stageOf ⟨Prologue.warpIndex l g,hWarp⟩
    ∃ batch, batch < p.batch ∧
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      let tile := (assignedCoordinates p batch (g/l.block)).1
      let blocks := Mma.trips p batch tile
      let cap := blocks-stageGeometryBlocks p batch tile stage+10
      let past := p.kLength batch-p.qLength batch+256*tile
      ∃ j u waits before rest tail,
        FirstGeometryReads p X (warpLane l g src) j batch ∧
        (X.tr (warpLane l g src)).drop (j+3) = waits ++ before ++ rest ∧
        (⟨9205,.exit⟩ : Event) ∈ rest ∧ before.countP (barrierMark 4397) = 1 ∧
        At u 5006 (firstLoopGeometry blocks cap past) ∧
        Walk kernel Assumptions.all l (warpLane l g src) u rest tail ∧
        ∀ e ∈ before, e.pc < 5006 := by
  dsimp only
  have hPc := actualExitPc hX he
  subst pc
  obtain ⟨batch,hb,hLo,hHi,j,s,hReads,hs,hRun⟩ :=
    activeGeometryOfExit hp hX hg hWarp hSrc hWork hCuQ hUsedK he
  have hLen := Execution.exit_last hX (Step.CtaBar.thread_lt_of_get hX he) he
  have h2 := hReads.2.2
  have hBound := (List.getElem?_eq_some_iff.mp h2).1
  change j+2 < (X.tr (warpLane l g src)).length at hBound
  change index+1 = (X.tr (warpLane l g src)).length at hLen
  have hNe : j+2 ≠ index := by
    intro h
    rw [h,he] at h2
    cases h2
  have hJ : j + 3 ≤ index := by omega
  have hExit : (⟨9205,.exit⟩ : Event) ∈ (X.tr (warpLane l g src)).drop (j+3) := by
    apply List.mem_of_getElem? (i := index-(j+3))
    rwa [List.getElem?_drop,Nat.add_sub_of_le hJ]
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  obtain ⟨vs,hWalk⟩ := Mma.walkFromRun hRun
  obtain ⟨u,waits,before,rest,tail,hEs,hExit',hCount,hAt,hSuffix,hSpan⟩ :=
    firstGeometryCounterWalk hp (stageOf ⟨Prologue.warpIndex l g,hWarp⟩) hb hTile hs hWalk hExit
  exact ⟨batch,hb,hLo,hHi,j,u,waits,before,rest,tail,hReads,hEs,hExit',hCount,
    hAt,hSuffix,hSpan⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
