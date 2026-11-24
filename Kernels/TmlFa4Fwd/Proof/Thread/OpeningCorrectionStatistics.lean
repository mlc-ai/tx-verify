-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionActiveGroup
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics
public import Kernels.TmlFa4Fwd.Proof.Thread.Softmax
public import Kernels.TmlFa4Fwd.Proof.CorrectionWarpRescaleSetup
public import Kernels.TmlFa4Fwd.Proof.Thread.Correction
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics
public import Kernels.TmlFa4Fwd.Proof.Thread.Softmax
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Flow.Code.Part124
import Lemmas.Step.DrainInOrder
import Lemmas.Step.Object

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Prologue Epilogue AsyncCopy

/-- The initial statistics wait is recorded with its returning per-lane cursor. -/
structure OpeningCorrectionStatistics (p : Params) (l : Launch) (X : Execution)
    (g batch lane : Nat) (stage : Fin 2) where
  index : Nat
  state : TState
  ending : Option TState
  waited : Thread.CorrectionWaits X (warpLane l g lane,index) .initial stage
  ready : At state (if stage.val = 0 then 7986 else 7989)
    (correctionBeforeRescale p l g batch lane)
  recorded : Run kernel Assumptions.all l (warpLane l g lane) {}
    ((X.tr (warpLane l g lane)).take (index+1)) (some state)
  remaining : Run kernel Assumptions.all l (warpLane l g lane) state
    ((X.tr (warpLane l g lane)).drop (index+1)) ending

/-- A decoded statistics rendezvous uses its actual register-selected group. -/
theorem statsSyncOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g site : Nat} (stage : Fin 2) {t : TState} {F : List (Nat × Value)}
    (ht : At t site F)
    (hCode : kernel.code[site]? =
      some ⟨none,.barSyncN (.reg (statsBarrierReg stage)) (.imm 64) true⟩)
    (hModel : out kernel Assumptions.all l g t = out kernel [] l g t)
    (hBar : t.regs (statsBarrierReg stage) = some (b32 (statsBarrierId l g stage))) :
    out kernel Assumptions.all l g t =
      .ev (.bar (statsBarrierId l g stage) (next t) (some 64) .sync) := by
  let id := statsBarrierId l g stage
  have hId : id < 16 := by
    have hs := stage.isLt
    have hw := Nat.mod_lt (warpIndex l g) (by decide : 0 < 4)
    dsimp [id,statsBarrierId]
    omega
  have hCount : 64 ≠ l.block := by rw [hp.block]; decide
  have hWord : readBits l g t 32 (.reg (statsBarrierReg stage)) =
      .ok (BitVec.ofNat 64 id) := readBits_b32 hBar (by omega)
  have hIdNat : (BitVec.ofNat 64 id).toNat = id := toNat_ofNat_lt (by omega)
  have hNum : readBits l g t 32 (.imm 64) = .ok (BitVec.ofNat 64 64) := rfl
  rw [hModel,out_event ht.2.2.2.1 (ht.1.symm ▸ hCode) rfl rfl]
  change Out.ev (barTmpl l g t (.reg (statsBarrierReg stage)) (some (.imm 64)) .sync) = _
  simp [barTmpl,hWord,hIdNat,hNum,hCount,id,show ¬16 ≤ id by omega]

private theorem initialStatsOut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (stage : Fin 2) {t : TState} {F : List (Nat × Value)}
    (ht : At t (if stage.val = 0 then 7985 else 7988) F)
    (hBar : t.regs (statsBarrierReg stage) = some (b32 (statsBarrierId l g stage))) :
    out kernel Assumptions.all l g t =
      .ev (.bar (statsBarrierId l g stage) (next t) (some 64) .sync) := by
  have hCode : kernel.code[(if stage.val=0 then 7985 else 7988)]? =
      some ⟨none,.barSyncN (.reg (statsBarrierReg stage)) (.imm 64) true⟩ := by
    fin_cases stage
    · exact Flow.code_7985
    · exact Flow.code_7988
  have hModel : out kernel Assumptions.all l g t = out kernel [] l g t := by
    apply Assumptions.out_all_eq_nil _ _ _ (ht.1.symm ▸ hCode) rfl
    all_goals rw [ht.1]; fin_cases stage <;> decide
  exact statsSyncOut hp stage ht hCode hModel hBar

/-- A released lane at a checked named-barrier template records its synchronous arrival. -/
theorem statsSyncOfCursor {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) {thread site id : Nat}
    (hg : thread < l.threads) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X thread site F)
    (hOut : out kernel Assumptions.all l thread c.ready =
      .ev (.bar id (next c.ready) (some 64) .sync)) :
    X.get (thread,c.pos) = some ⟨c.ready.pc,.bar id (some 64) .sync⟩ ∧
      Run kernel Assumptions.all l thread {} ((X.tr thread).take (c.pos+1)) (some (next c.ready)) ∧
      Run kernel Assumptions.all l thread (next c.ready)
        ((X.tr thread).drop (c.pos+1)) c.ending := by
  let t := c.ready
  let event : Event := ⟨t.pc,.bar id (some 64) .sync⟩
  have hStep : EStep kernel Assumptions.all l thread t event (some (next t)) :=
    ⟨_,hOut,rfl,rfl⟩
  have hLt : c.pos < (X.tr thread).length := by
    by_contra! hLe
    have hEq := Nat.le_antisymm c.bounded hLe
    have hStarted : X.tr thread ≠ [] := List.ne_nil_of_length_pos (c.positive.trans_le c.bounded)
    have hBefore := c.recorded
    rw [List.take_of_length_le hLe] at hBefore
    exact hMax.not_grows (Step.bar_counted_extension hMax.1 hg (.inl hStarted)
      (c.released hEq)
      (Assumptions.wfStep.quiet hMax.1 le_snoc rfl
        (Execution.noNewRead_snoc rfl)) hBefore c.localSteps hStep)
  let hn : Next kernel Assumptions.all l thread c.before t (.bar id (next t) (some 64) .sync) :=
    ⟨c.localSteps,hOut⟩
  obtain ⟨_,_,he,⟨rfl,hRet⟩,hTail⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,h⟩; cases h) c.remaining
    (fun h => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp h))
  obtain rfl := Option.some.inj hRet
  have hPrefix : Run kernel Assumptions.all l thread {}
      ((X.tr thread).take (c.pos+1)) (some (next t)) := by
    rw [List.take_add_one,show (X.tr thread)[c.pos]? = some event from he]
    exact c.recorded.snoc c.localSteps hStep
  exact ⟨he,hPrefix,hTail⟩

/-- The reached correction lane performs its decoded initial statistics arrival. -/
theorem initialStatsAtCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch lane : Nat} (hg : warpLane l g lane < l.threads) (stage : Fin 2)
    (c : OpeningTripCursor l X (warpLane l g lane) (if stage.val = 0 then 7985 else 7988)
      (correctionBeforeRescale p l g batch lane)) :
    ∃ d : OpeningCorrectionStatistics p l X g batch lane stage, d.index = c.pos := by
  let thread := warpLane l g lane
  let id := statsBarrierId l thread stage
  let t := c.ready
  have hBar : t.regs (statsBarrierReg stage) = some (b32 id) := by
    apply holds_mem c.checkpoint.2.2.2.2
    fin_cases stage <;>
      simp [correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts,
        statsBarrierReg,id,thread]
  have hOut := initialStatsOut hp stage c.checkpoint hBar
  obtain ⟨he,hPrefix,hTail⟩ := statsSyncOfCursor hMax hg c hOut
  have hFrame : At (next t) (if stage.val=0 then 7986 else 7989)
      (correctionBeforeRescale p l g batch lane) := by
    have h := c.checkpoint.next
    convert h using 1
    fin_cases stage <;> rfl
  exact ⟨⟨c.pos,next t,c.ending,Thread.initialWaitObservation stage (c.checkpoint.1 ▸ he),
    hFrame,hPrefix,hTail⟩,rfl⟩

theorem initialStatsOfCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch lane : Nat} (hg : warpLane l g lane < l.threads) (stage : Fin 2)
    (c : OpeningTripCursor l X (warpLane l g lane) (if stage.val = 0 then 7985 else 7988)
      (correctionBeforeRescale p l g batch lane)) :
    Nonempty (OpeningCorrectionStatistics p l X g batch lane stage) := by
  obtain ⟨d,_⟩ := initialStatsAtCursor hp hMax hg stage c
  exact ⟨d⟩

/-- From its actual selected tile, a maximal correction lane reads the metadata,
computes its trip count and arrives at the first statistics rendezvous. -/
theorem openingCorrectionFirstStatisticsOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (hwLo : 8 ≤ warpIndex l g) (hwHi : warpIndex l g < 12)
    (hCuQ : DrainCuQProtected p X) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*batch)).at k)) :
    ∀ lane < 32, Nonempty (OpeningCorrectionStatistics p l X g batch lane 0) := by
  obtain ⟨_,ends,⟨cur⟩⟩ := activeTileOfMaximal hp hMax hg hwLo hwHi hCuQ hb hLo hHi
  intro lane hl
  let thread := warpLane l g lane
  let tile := (assignedCoordinates p batch (g/l.block)).1
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hThread := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
  let F := tileSetupFrame p l g batch lane
  obtain ⟨u,hLocal,hU⟩ := correctionInputRun hp hb (cur.checkpoint lane hl)
  have hAt : At u 7955 (correctionInputFacts p batch tile ++ F) := by
    simpa only [F,tileSetupFrame,List.append_assoc] using hU
  let start : OpeningTripCursor l X thread 7955 (correctionInputFacts p batch tile ++ F) :=
    ⟨cur.pos lane,cur.before lane,u,ends lane,cur.positive lane hl,cur.bounded lane hl,
      cur.released lane hl,hAt,cur.recorded lane hl,cur.continuation lane hl,
      (cur.localSteps lane hl).trans (run_rtg hLocal)⟩
  have hFresh (rv : Nat × Value) (hm : rv ∈ F) : rv.1 ∉ [1634,5958,5959] := by
    intro hRead
    have hm' := List.mem_map_of_mem (f := Prod.fst) hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hRead
    rcases hRead with h | h | h <;> rw [h] at hm' <;>
      exact (of_decide_eq_true rfl : _ ∉ F.map Prod.fst) hm'
  obtain ⟨read⟩ := openingTripReadsOfMaximal hp hMax hThread hb start hFresh
    (by set_option maxRecDepth 100000 in kernel_rfl) hCuQ hUsedK
  have hRead := read.checkpoint.2.2.2.2
  let H := (1634,b32 (p.qOffset batch)) :: (1635,b32 (p.qLength batch)) :: F
  have hCountAt : At read.ready 7960
      ([(5959,b32 (p.kLength batch)),(7276,b32 tile),(1635,b32 (p.qLength batch))] ++ H) :=
    read.checkpoint.mono ⟨hRead.1,hRead.2.1,hRead.2.2.1,
      hRead.2.2.2.1,hRead.2.2.1,hRead.2.2.2.2⟩
  obtain ⟨w,hw,hW⟩ := correctionTripAndRowWithFrame hp thread hb hTile
    (by set_option maxRecDepth 100000 in kernel_rfl) read.ready hCountAt
  exact initialStatsOfCursor hp hMax hThread 0
    ⟨read.pos,read.before,w,read.ending,read.positive,read.bounded,read.released,
      hW,read.recorded,read.remaining,read.localSteps.trans (run_rtg hw)⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g batch lane : Nat}
    (hg : warpLane l g lane < l.threads) {stage : Fin 2}
    (c : OpeningCorrectionStatistics p l X g batch lane stage)
    (hRelease : c.index+1 = (X.tr (warpLane l g lane)).length →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
        Step.Released l Y (warpLane l g lane)) {t u : TState} {addr : Loc} {site : Nat}
    {F : List (Nat × Value)}
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) c.state t)
    (hOut : out kernel Assumptions.all l (warpLane l g lane) t = .ev (.arrive addr 0 u 1 true .cta))
include hg c hRelease hLocal hOut

/-- A released correction statistics cursor performs its next unit notification. -/
theorem OpeningCorrectionStatistics.notifyIndexedOfMaximal (hReady : At u site F) :
    X.Arrive (warpLane l g lane,c.index+1) addr 0 1 true .cta ∧
      (∃ d : OpeningTripCursor l X (warpLane l g lane) site F, d.pos = c.index+2) := by
  let thread := warpLane l g lane
  let event : Event := ⟨t.pc,.arrive addr 0 1 true .cta⟩
  have hStep : EStep kernel Assumptions.all l thread t event (some u) := ⟨_,hOut,rfl,rfl⟩
  obtain ⟨_,hWait,_⟩ := c.waited
  have hBound : c.index+1 ≤ (X.tr thread).length := len_of_get hWait
  have hLt : c.index+1 < (X.tr thread).length := by
    by_contra! hLe
    obtain ⟨Y,hY,hTrace,hRel⟩ := hRelease (Nat.le_antisymm hBound hLe)
    have hStart : Y.tr thread ≠ [] := by
      rw [hTrace]
      exact List.ne_nil_of_length_pos (by omega)
    have hRun := c.recorded
    rw [List.take_of_length_le hLe,← hTrace] at hRun
    apply hY.not_grows
    refine Step.object_counted_extension_silent hY.1 (by trivial) hg (.inl hStart)
      hRel hRun hLocal hStep ⟨trivial,fun _ h => by cases h⟩ (by trivial)
      (fun _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) rfl (mb := addr) (act := .arrive 1 0)
      (fun _ _ h => by cases h) ?_ ?_
    · intro loc
      by_cases h : loc = addr
      · subst loc
        simp [objectAction,snoc_get_new,event]
      · simp [objectAction,snoc_get_new,event,h,Ne.symm h]
    · intro rec
      exact Assumptions.wfStep.quiet hY.1
        (Execution.le_trans le_snoc (Execution.le_appendObject _ _ _)) rfl
          ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
            (Execution.noNewRead_of_tr rfl))
  let hn : Next kernel Assumptions.all l thread c.state t (.arrive addr 0 u 1 true .cta) :=
    ⟨hLocal,hOut⟩
  obtain ⟨_,_,he,⟨rfl,hRet⟩,hTail⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,h⟩; cases h) c.remaining
    (fun h => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp h))
  rw [Option.some.inj hRet] at hTail
  have hPrefix : Run kernel Assumptions.all l thread {}
      ((X.tr thread).take ((c.index+1)+1)) (some u) := by
    rw [List.take_add_one,show (X.tr thread)[c.index+1]? = some event from he]
    exact c.recorded.snoc hLocal hStep
  have hReleased (hLast : (c.index+1)+1 = (X.tr thread).length) : Step.Released l X thread := by
    apply Step.Released.of_get
    intro e hGet
    have hPrev : (X.tr thread).length-1 = c.index+1 := by omega
    rw [hPrev,he] at hGet
    cases hGet
    simp [Kind.resume]
  exact ⟨⟨_,he⟩,
    ⟨⟨(c.index+1)+1,u,u,c.ending,by omega,len_of_get he,hReleased,hReady,hPrefix,hTail,.refl⟩,rfl⟩⟩

theorem OpeningCorrectionStatistics.notifyRecordedOfMaximal (hReady : At u site F) :
    X.Arrive (warpLane l g lane,c.index+1) addr 0 1 true .cta ∧
      Nonempty (OpeningTripCursor l X (warpLane l g lane) site F) := by
  obtain ⟨he,d,_⟩ := c.notifyIndexedOfMaximal hg hRelease hLocal hOut hReady
  exact ⟨he,⟨d⟩⟩

/-- A released correction statistics cursor performs its next unit notification. -/
theorem OpeningCorrectionStatistics.notifyOfMaximal (hReady : At u site F)
    : Nonempty (OpeningTripCursor l X (warpLane l g lane) site F) :=
  (c.notifyRecordedOfMaximal hg hRelease hLocal hOut hReady).2
end

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch lane : Nat}
    (hg : warpLane l g lane < l.threads) (c : OpeningCorrectionStatistics p l X g batch lane 0)
    (hRelease : c.index+1 = (X.tr (warpLane l g lane)).length →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
        Step.Released l Y (warpLane l g lane))
include hp hMax hg c hRelease

/-- A released first statistics rendezvous permits the interstage credit and second arrival. -/
theorem OpeningCorrectionStatistics.secondIndexedOfMaximal :
    X.Arrive (warpLane l g lane,c.index+1)
        ⟨.shared,warpLane l g lane/l.block,l.sharedBase+192⟩ 0 1 true .cta ∧
      (∃ d : OpeningCorrectionStatistics p l X g batch lane 1, d.index = c.index+2) := by
  let thread := warpLane l g lane
  let F := correctionBeforeRescale p l g batch lane
  let t := next (setReg c.state 5978 (b32 1))
  let u := next (mbarStateDest t (some 8994))
  let addr : Loc := ⟨.shared,thread/l.block,l.sharedBase+192⟩
  let event : Event := ⟨t.pc,.arrive addr 0 1 true .cta⟩
  have ht : At t 7987 ((5978,b32 1) :: F) := c.ready.set (by
    intro pair hm h
    have hMem := List.mem_map_of_mem (f := Prod.fst) hm
    rw [h] at hMem
    exact (of_decide_eq_true rfl : 5978 ∉ F.map Prod.fst) hMem)
  have hMove : run kernel Assumptions.all l thread 1 c.state = some t := by
    apply run_local Flow.code_7986 rfl c.ready
    rw [Assumptions.execLocalA_all_eq_numeric,Assumptions.execLocalA_eq_nil
      (by rw [c.ready.1]; decide) rfl,execLocalA_nil,execLocal_move rfl]
    simp [execMove,readValue,readBits,Value.bytes,b32,bind,Except.bind,pure,Except.pure,
      DType.width,t,truncBits]
  have hCode : kernel.code[7987]? = some ⟨none,
      .mbarArrive 1069 0 (.imm 0) (.reg 5978) false true .cta (some 8994)⟩ := Flow.code_7987
  have hModel : out kernel Assumptions.all l thread t = out kernel [] l thread t := by
    apply Assumptions.out_all_eq_nil _ _ _ (ht.1.symm ▸ hCode) rfl
    all_goals rw [ht.1]; decide
  have hShared := hp.shared.2.1
  have hAlign := hp.shared.1
  have hOut : out kernel Assumptions.all l thread t = .ev (.arrive addr 0 u 1 true .cta) :=
    correctionReleaseOut (base := l.sharedBase+192) (off := 0) ht hModel hCode
      (holds_lookup ht.2.2.2.2 (by rfl)) ht.2.2.2.2.1 (by omega) (by omega)
  have hReady : At u 7988 F := At.clear_state (ht.mono ht.2.2.2.2.2) (by
    intro pair hm h
    have hMem := List.mem_map_of_mem (f := Prod.fst) hm
    rw [h] at hMem
    exact (of_decide_eq_true rfl : 8994 ∉ F.map Prod.fst) hMem)
  obtain ⟨he,cursor,hPos⟩ := c.notifyIndexedOfMaximal hg hRelease (run_rtg hMove) hOut hReady
  obtain ⟨d,h⟩ := initialStatsAtCursor hp hMax hg 1 cursor
  exact ⟨he,d,h.trans hPos⟩

theorem OpeningCorrectionStatistics.secondAndCreditOfMaximal :
    X.Arrive (warpLane l g lane,c.index+1)
        ⟨.shared,warpLane l g lane/l.block,l.sharedBase+192⟩ 0 1 true .cta ∧
      Nonempty (OpeningCorrectionStatistics p l X g batch lane 1) := by
  obtain ⟨he,d,_⟩ := c.secondIndexedOfMaximal hp hMax hg hRelease
  exact ⟨he,⟨d⟩⟩

end

/-- The first repeated statistics wait has recorded its continuation before reading alpha. -/
structure FirstRescaleReached (p : Params) (l : Launch) (X : Execution)
    (g batch lane : Nat) where
  index : Nat
  state : TState
  ending : Option TState
  waited : Thread.CorrectionWaits X (warpLane l g lane,index) .rescale 0
  ready : At state (statsPc 0 .alpha) (correctionRescaleSetupFacts p l g batch lane)
  recorded : Run kernel Assumptions.all l (warpLane l g lane) {}
    ((X.tr (warpLane l g lane)).take (index+1)) (some state)
  remaining : Run kernel Assumptions.all l (warpLane l g lane) state
    ((X.tr (warpLane l g lane)).drop (index+1)) ending

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) {g batch lane : Nat}
    (hg : warpLane l g lane < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRepeat : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (c : OpeningCorrectionStatistics p l X g batch lane 1)
    (hRelease : c.index+1 = (X.tr (warpLane l g lane)).length →
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
        Step.Released l Y (warpLane l g lane))
include hp hg hb hLo hHi hRepeat c hRelease

/-- Record the first rescale rendezvous and retain its actual returning checkpoint. -/
theorem OpeningCorrectionStatistics.firstRescaleIndexedOfMaximal :
    ∃ d : FirstRescaleReached p l X g batch lane, d.index = c.index+1 := by
  let thread := warpLane l g lane
  let id := statsBarrierId l thread 0
  let F := correctionRescaleSetupFacts p l g batch lane
  obtain ⟨n,u,hRun,hu⟩ := correctionLaneRescaleSetup hp hb hLo hHi c.ready
  have hAt : At u (statsBarrierPc 0 true) F := by
    have hSite : statsBarrierPc 0 true = 8006 := by decide
    simpa only [F,hSite,ite_eq_right (Nat.not_lt_of_ge hRepeat)] using hu
  have hBar : u.regs (statsBarrierReg 0) = some (b32 id) := by
    apply holds_mem hAt.2.2.2.2
    unfold F correctionRescaleSetupFacts
    rw [ite_eq_right (Nat.not_lt_of_ge hRepeat)]
    simp [correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts,
      statsBarrierReg,thread,id]
  have hLocal := run_rtg hRun
  have hCode := statsBarrierCode (0 : Fin 2) true
  have hModel : out kernel Assumptions.all l thread u = out kernel [] l thread u := by
    apply Assumptions.out_all_eq_nil _ _ _ (hAt.1.symm ▸ hCode) rfl
    all_goals rw [hAt.1]; decide
  have hOut := statsSyncOut hp 0 hAt hCode hModel hBar
  obtain ⟨_,he,_⟩ := c.waited
  have hBound : c.index+1 ≤ (X.tr thread).length := len_of_get he
  have hLt : c.index+1 < (X.tr thread).length := by
    by_contra! hLe
    obtain ⟨Y,hY,hTrace,hRel⟩ := hRelease (Nat.le_antisymm hBound hLe)
    have hBefore := c.recorded
    rw [List.take_of_length_le hLe,← hTrace] at hBefore
    have hStart : Y.tr thread ≠ [] := by
      rw [hTrace]
      exact List.ne_nil_of_length_pos (by omega)
    exact hY.not_grows (Step.bar_counted_extension hY.1 hg (.inl hStart) hRel
      (Assumptions.wfStep.quiet hY.1 le_snoc rfl
        (Execution.noNewRead_snoc rfl)) hBefore hLocal ⟨_,hOut,rfl,rfl⟩)
  let hn : Next kernel Assumptions.all l thread c.state u (.bar id (next u) (some 64) .sync) :=
    ⟨hLocal,hOut⟩
  obtain ⟨v,_,he,⟨rfl,hReturn⟩,hTail⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,h⟩; cases h) c.remaining
    (fun h => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp h))
  obtain rfl := Option.some.inj hReturn
  have hPrefix : Run kernel Assumptions.all l thread {}
      ((X.tr thread).take (c.index+1+1)) (some (next u)) := by
    rw [List.take_succ_eq_append_getElem hLt,(List.getElem?_eq_some_iff.mp he).2]
    exact c.recorded.snoc hLocal ⟨_,hOut,rfl,rfl⟩
  exact ⟨⟨c.index+1,next u,c.ending,Thread.rescaleWaitObservation 0 (hAt.1 ▸ he),
    hAt.next,hPrefix,hTail⟩,rfl⟩

end PTX.Kernels.TmlFa4Fwd.Correction

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX Prologue

/-- The correction initial wait is the synchronous arrival for its stage's statistics group. -/
theorem initialCorrectionStatisticsBarrier {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {stage : Fin 2} (hWait : CorrectionWaits X i .initial stage) :
    BarrierArrival X i (Correction.statsBarrierId l i.1 stage) (some 64) .sync := by
  obtain ⟨_,⟨e,he,hKind,_,_⟩,_,_⟩ := correctionWaits hp hX hWait
  exact ⟨e,he,hKind⟩

/-- The first statistics publication is the producer arrival for its statistics group. -/
theorem openingSoftmaxStatisticsBarrier {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} (hPub : Scores.Publishes X i .first) :
    BarrierArrival X i (3+warpIndex l i.1) (some 64) .arrive := by
  obtain ⟨_,⟨e,he,hKind,_,_⟩,_,_⟩ := Scores.publishes hp hX hPub
  exact ⟨e,he,hKind⟩

end PTX.Kernels.TmlFa4Fwd.Thread
