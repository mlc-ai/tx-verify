-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFallbackWord
import all Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect
import all Kernels.TmlFa4Fwd.Proof.LoaderSelectedCoordinates
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Flow.Code.Part027
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Loader
  (RingShape ringShapeOfAt loaderPipelineCutOp pipelineCutStep loaderSubstepAtNewPc
    loaderEntryFacts loaderBarrierFacts loaderChosenFacts loaderVoteCarry loaderCuQFacts
    loaderOwnPrefixEventRequiresActiveTile loaderActiveBatchOfEvent loaderLinear loaderOutCore
    loaderParam19Name scalarLoad traceAfterObservedEvent)

private def drainRootFrame (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(1073,b32 (laneOf l g)),(7506,b64 p.cuQBase),(1072,b32 (g/l.block))]

private theorem drainTailFloor {l : Launch} {g : Nat} {s u : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events u) (hs : 1862 ≤ s.pc) : 1862 ≤ u.pc := by
  have hAudit : (kernel.code.drop 1862).all (fun i => staysPastEvent 1862 i.op) = true := by
    decide +kernel
  have hSeg : Assumptions.swExp2Sites.all (fun pc =>
      match PTX.Assumption.cuteExp2.matchAt kernel pc with
      | some seg => decide (1862 ≤ seg.stop)
      | none => false) = true := by decide +kernel
  induction h with
  | refl => exact hs
  | tau he _ ih => exact ih (eventTailStepOfAudit hAudit hSeg hs (.inl ⟨rfl,he⟩))
  | event he _ ih => exact ih (eventTailStepOfAudit hAudit hSeg hs (.inr ⟨_,rfl,he⟩))

private theorem loaderCutOfObservedPath {l : Launch} {g low cut bypass : Nat}
    {F : List (Nat × Value)} {s u : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events u)
    (hLow : 174 ≤ low) (hCut : cut ≤ 1901)
    (hCode : ((kernel.code.drop low).take (cut-low)).all
      (fun ins => loaderPipelineCutOp low cut bypass (F.map Prod.fst) ins.op) = true)
    (hFloor : ∀ {a b : TState} {es : List Event},
      TraceReach kernel Assumptions.all l g a es b → bypass < a.pc → bypass < b.pc)
    (hs : low ≤ s.pc ∧ s.pc ≤ cut) (hShape : RingShape s)
    (hSub : s.pc = cut → s.sub = 0) (hRegs : Holds s.regs F)
    (hu : cut ≤ u.pc ∧ u.pc ≤ bypass) :
    ∃ mid pre tail, events = pre ++ tail ∧ mid.pc = cut ∧ mid.sub = 0 ∧ mid.acc = [] ∧
      Holds mid.regs F ∧
      TraceReach kernel Assumptions.all l g s pre mid ∧
      TraceReach kernel Assumptions.all l g mid tail u := by
  have advance {a b : TState} {ev : Option Event} {es : List Event}
      (ha : low ≤ a.pc ∧ a.pc ≤ cut) (hne : a.pc ≠ cut)
      (hShape : RingShape a) (hR : Holds a.regs F)
      (he : WStep kernel Assumptions.all l g a ev b)
      (hTail : TraceReach kernel Assumptions.all l g b es u) :
      (low ≤ b.pc ∧ b.pc ≤ cut) ∧ RingShape b ∧
      (b.pc = cut → b.sub = 0) ∧ Holds b.regs F := by
    obtain ⟨hLo,hHi,hS,hF⟩ := pipelineCutStep (F := F) hLow hCut ⟨ha.1,by omega⟩ hCode he hShape hR
    have hBound := hHi.resolve_right fun hb => Nat.not_lt_of_ge hu.2 (hFloor hTail hb)
    refine ⟨⟨hLo,hBound⟩,hS,?_,hF⟩
    intro hPc
    exact loaderSubstepAtNewPc (show 174 ≤ a.pc by omega) (show a.pc < 1901 by omega)
      hShape he (by omega)
  induction h with
  | refl s =>
    have hPc : s.pc = cut := by omega
    have hZero := hSub hPc
    exact ⟨s,[],[],rfl,hPc,hZero,hShape.2 hZero,hRegs,.refl _, .refl _⟩
  | @tau a b c es hStep hTail ih =>
    by_cases hEq : a.pc = cut
    · exact ⟨a,[],es,rfl,hEq,hSub hEq,hShape.2 (hSub hEq),hRegs,.refl _, .tau hStep hTail⟩
    obtain ⟨hb,hShapeB,hSubB,hRegsB⟩ :=
      advance hs hEq hShape hRegs (.inl ⟨rfl,hStep⟩) hTail
    obtain ⟨mid,pre,tail,hTrace,hPc,hZero,hAcc,hF,hFront,hEnd⟩ :=
      ih hb hShapeB hSubB hRegsB hu advance
    exact ⟨mid,pre,tail,hTrace,hPc,hZero,hAcc,hF,.tau hStep hFront,hEnd⟩
  | @event a b c es e hStep hTail ih =>
    by_cases hEq : a.pc = cut
    · exact ⟨a,[],e::es,rfl,hEq,hSub hEq,hShape.2 (hSub hEq),hRegs,
        .refl _, .event hStep hTail⟩
    obtain ⟨hb,hShapeB,hSubB,hRegsB⟩ :=
      advance hs hEq hShape hRegs (.inr ⟨_,rfl,hStep⟩) hTail
    obtain ⟨mid,pre,tail,hTrace,hPc,hZero,hAcc,hF,hFront,hEnd⟩ :=
      ih hb hShapeB hSubB hRegsB hu advance
    exact ⟨mid,e::pre,tail,congrArg (List.cons e) hTrace,hPc,hZero,hAcc,hF,.event hStep hFront,hEnd⟩

private theorem firstDrainCutOfObservedPath {p : Params} {l : Launch} {g : Nat}
    {s u : TState} {events : List Event} (h : TraceReach kernel Assumptions.all l g s events u)
    (hs : 302 ≤ s.pc ∧ s.pc ≤ 1744) (hShape : RingShape s)
    (hSub : s.pc = 1744 → s.sub = 0) (hRegs : Holds s.regs (drainRootFrame p l g))
    (hu : 1744 ≤ u.pc ∧ u.pc < 1862) :
    ∃ mid pre tail, events = pre ++ tail ∧ mid.pc = 1744 ∧ mid.sub = 0 ∧ mid.acc = [] ∧
      Holds mid.regs (drainRootFrame p l g) ∧
      TraceReach kernel Assumptions.all l g s pre mid ∧
      TraceReach kernel Assumptions.all l g mid tail u := by
  have hCode : ((kernel.code.drop 302).take (1744-302)).all
      (fun ins => loaderPipelineCutOp 302 1744 1861 [1073,7506,1072] ins.op) = true := by
    set_option maxRecDepth 100000 in decide +kernel
  exact loaderCutOfObservedPath h (by decide) (by decide) hCode
    (fun hPath hBefore => drainTailFloor hPath (by omega))
    hs hShape hSub hRegs ⟨hu.1,by omega⟩

private theorem resumeAtCut {l : Launch} {X : Execution} {g pos j : Nat}
    {s mid : TState} {pre tail : List Event} {ending : Option TState} {e : Event}
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hPos : pos ≤ j) (he : X.get (g,j) = some e)
    (hSplit : ((X.tr g).drop pos).take (j-pos) = pre ++ tail)
    (hPrefix : TraceReach kernel Assumptions.all l g s pre mid) :
    pos+pre.length ≤ j ∧ Run kernel Assumptions.all l g mid
      ((X.tr g).drop (pos+pre.length)) ending := by
  have hLen := congrArg List.length hSplit
  have hBefore : pos+pre.length ≤ j := by
    simp only [List.length_take,List.length_append] at hLen
    omega
  have hFront : ((X.tr g).drop pos).take pre.length = pre := by
    have hPrefixLen : pre.length ≤ j-pos := by omega
    have hTake := congrArg (fun es : List Event => es.take pre.length) hSplit
    rw [List.take_take,Nat.min_eq_left hPrefixLen,List.take_left' rfl] at hTake
    exact hTake
  have hWhole : (X.tr g).drop pos = pre ++ (X.tr g).drop (pos+pre.length) := by
    have hFull := (List.take_append_drop pre.length ((X.tr g).drop pos)).symm
    rw [hFront,List.drop_drop] at hFull
    simpa only [Nat.add_comm] using hFull
  obtain ⟨before,hReturned,hLocal⟩ := hPrefix.returnedPrefix
  have hTail := (hReturned.after_returned_prefix (hWhole ▸ hr)).after_local_nonempty
    hLocal (traceAfterObservedEvent he hBefore)
  exact ⟨hBefore,hTail⟩

private theorem actualDrainCut {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X)
    {g j site : Nat} {a : Acc} {bytes : List (Option Byte)}
    (hSite : site = 1750 ∨ site = 1805)
    (he : X.get (g,j) = some ⟨site,.rd a bytes⟩) :
    ∃ pos ≤ j, ∃ s ending, At s 1744 (drainRootFrame p l g) ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending := by
  have hBand : 1744 ≤ site ∧ site < 1862 := by rcases hSite with rfl | rfl <;> decide
  have hg := event_thread_lt hX he
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < site by omega)
    (by change site ∉ registerHintSites; rcases hSite with rfl | rfl <;> decide)
  have hw : 14 ≤ warpIndex l g := by
    change roleBodyPc (warpIndex l g) site at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hWork := loaderOwnPrefixEventRequiresActiveTile hp hX hw hCuQ he
    (show 297 < site by omega) hBand.2
  have hGet : X.get (warpLane l g lane,j) = some ⟨site,.rd a bytes⟩ := hLane.symm ▸ he
  obtain ⟨first,batch,_,_,_,_,_,_,ending,cur,hFollow⟩ :=
    loaderActiveBatchOfEvent hp hX hg hw hl hCuQ hWork hGet (show 297 < site by omega)
  let pos := cur.pos lane
  have hs := cur.checkpoint lane hl
  have hLaneReg : (cur.state lane).regs 1073 = some (b32 (laneOf l (warpLane l g lane))) :=
    holds_mem hs.2.2.2.2 (by simp [loaderChosenFacts,loaderVoteCarry,loaderCuQFacts])
  have hCtaReg : (cur.state lane).regs 1072 = some (b32 (warpLane l g lane/l.block)) :=
    holds_mem hs.2.2.2.2 (by simp [loaderChosenFacts,loaderVoteCarry,loaderCuQFacts,
      loaderEntryFacts,loaderBarrierFacts])
  rw [hLane] at hLaneReg hCtaReg
  have hFrame : At (cur.state lane) 302 (drainRootFrame p l g) := by
    exact hs.mono ⟨hLaneReg,
      holds_mem hs.2.2.2.2 (by simp [loaderChosenFacts,loaderVoteCarry,loaderCuQFacts,
        loaderEntryFacts,loaderBarrierFacts,abiFacts]),hCtaReg,trivial⟩
  have hr := (cur.continuation lane hl).after_local_nonempty
    (cur.localSteps lane hl) hFollow.nonempty
  rw [hLane] at hr
  have hPos : pos ≤ j := hFollow.before
  have hIndexed : ((X.tr g).drop pos)[j-pos]? = some ⟨site,.rd a bytes⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
    exact he
  obtain ⟨t,_,hPath,hObserve⟩ := hr.before_event hIndexed
  have ht : t.pc = site := (estep_source_pc hObserve).symm
  obtain ⟨mid,pre,tail,hSplit,hPc,hSub,hAcc,hRegs,hPrefix,_⟩ :=
    firstDrainCutOfObservedPath hPath (by rw [hFrame.1]; decide) (ringShapeOfAt hFrame)
      (fun _ => hFrame.2.1) hFrame.2.2.2.2 (ht.symm ▸ hBand)
  obtain ⟨hBefore,hTail⟩ := resumeAtCut hr hPos he hSplit hPrefix
  have hFault : mid.fault = none := by
    cases hf : mid.fault with
    | none => rfl
    | some f =>
      have hIndex : ((X.tr g).drop (pos+pre.length))[j-(pos+pre.length)]? =
          some ⟨site,.rd a bytes⟩ := by
        rw [List.getElem?_drop,Nat.add_sub_of_le hBefore]
        exact he
      cases hTail.eventOfFault hf hIndex
  exact ⟨pos+pre.length,hBefore,mid,ending lane,⟨hPc,hSub,hAcc,hFault,hRegs⟩,hTail⟩

private theorem loaderFirstDrainGate {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} {t : TState} (ht : At t 1744 (drainRootFrame p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (if p.batch < laneOf l g then 1751 else 1748)
        ((7145,b32 p.batch)::drainRootFrame p l g) := by
  let F := drainRootFrame p l g
  let lane := laneOf l g
  let batch := p.batch
  obtain ⟨hBatch32,hParam⟩ := hp.values (19,p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  let v := next (setReg t 7145 (b32 batch))
  have hLoad : run kernel [] l g 1 t = some v :=
    scalarLoad ht hParam hBatch32 (by rw [loaderParam19Name]; exact Flow.code_1744)
  have hV : At v 1745 ((7145,b32 batch)::F) := ht.set (by simp [drainRootFrame])
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hBatch := hp.shape.2.1
  have signed {n : Nat} (hn : n < 2 ^ 31) :
      toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
    simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left hn]
  have hGate : Seg kernel [] l g 2 1745 ((7145,b32 batch)::F) 1747
      ((231,.pred (decide (batch < lane)))::(7145,b32 batch)::F) := by
    intro w hw
    dsimp [F,drainRootFrame] at hw ⊢
    change At w 1745 [(7145,b32 batch),(1073,b32 lane),(7506,b64 p.cuQBase),
      (1072,b32 (g/l.block))] at hw
    seg_fp hw using simp only [truncBits_ofNat (show lane < 2 ^ 32 by omega) (by decide),
      truncBits_ofNat (show batch < 2 ^ 32 by omega) (by omega), compare, Option.getD_some,
      signed (show lane < 2 ^ 31 by omega), signed (show batch < 2 ^ 31 by omega),
      gt_iff_lt, Int.ofNat_lt]
  obtain ⟨w,hToGate,hw⟩ := hGate v hV
  obtain ⟨u,hBranch,hu⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1747 _ hw hw.2.2.2.2.1 (by simp)
  have hLocal {lo n : Nat} {s u} (hLo : 174 ≤ lo) (hHi : lo+n ≤ 1906)
      (hp : s.pc = lo) (hCode : ((kernel.code.drop lo).take (n-1)).all
        (fun i => schedulerFallsThrough i.op) = true)
      (hr : run kernel [] l g n s = some u) :
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u :=
    run_rtg (loaderLinear (regs := []) hLo hHi hp (by simp) hCode hr).1
  exact ⟨u, (hLocal (by decide) (by decide) ht.1 (by decide) hLoad).trans
      ((hLocal (by decide) (by decide) hV.1 (by decide +kernel) hToGate).trans
        (hLocal (by decide) (by decide) hw.1 (by decide) hBranch)),
    by simpa only [decide_eq_true_eq] using hu.mono hu.2.2.2.2.2⟩

private theorem loaderFirstDrainAddress {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (hb : laneOf l g ≤ p.batch) :
    Seg kernel [] l g 2 1748 (drainRootFrame p l g) 1750
      [(7858,b64 (p.cuQBase+4*laneOf l g))] := by
  intro t ht
  have hRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRange
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hL32 : laneOf l g < 2 ^ 32 := by omega
  have hL64 : laneOf l g < 2 ^ 64 := by omega
  have hOff : 4 * laneOf l g < 2 ^ 64 := by omega
  have hBase : p.cuQBase < 2 ^ 64 := by omega
  have hAddr : p.cuQBase + 4 * laneOf l g < 2 ^ 64 := by omega
  have h4 : (truncBits 32 (BitVec.ofInt 64 4)).toNat = 4 := rfl
  unfold drainRootFrame at ht
  seg_fp ht using simp only [b64, kind_u_beq_s, Bool.false_eq_true, ↓reduceIte,
    truncBits_ofNat hL32 (by decide), toNat_ofNat_lt hL64, h4, Nat.mul_comm (laneOf l g),
    truncBits_ofNat hOff (by decide), truncBits_ofNat hBase (by decide),
    ← BitVec.ofNat_add, truncBits_ofNat hAddr (by decide)]

private theorem afterFirstDrainReadFloor {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {ending : Option TState} (hs : 1751 ≤ s.pc)
    (hr : Run kernel Assumptions.all l g s es ending) :
    ∀ e ∈ es, 1751 ≤ e.pc := by
  have hAudit : (kernel.code.drop 1751).all (fun i => staysPastEvent 1751 i.op) = true := by
    decide +kernel
  have hSeg : Assumptions.swExp2Sites.all (fun pc =>
      match PTX.Assumption.cuteExp2.matchAt kernel pc with
      | some seg => decide (1751 ≤ seg.stop)
      | none => false) = true := by decide +kernel
  obtain ⟨_,hw⟩ := Mma.walkFromRun hr
  exact eventTailEventsOfSegmentFloor hAudit (fun site _ hm seg hMatch => by
    have h := List.all_eq_true.mp hSeg site hm
    rw [hMatch] at h
    exact of_decide_eq_true h) hw hs

private theorem firstDrainCuQReadWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X)
    {g j : Nat} {a : Acc} {bytes : List (Option Byte)}
    (he : X.get (g,j) = some ⟨1750,.rd a bytes⟩) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4*index), size := 4} := by
  obtain ⟨pos,hPos,t,ending,ht,hRun⟩ := actualDrainCut hp hX hCuQ (.inl rfl) he
  have hMore := traceAfterObservedEvent he hPos
  obtain ⟨s,hLocal,hs⟩ := loaderFirstDrainGate hp ht
  by_cases hIndex : laneOf l g ≤ p.batch
  · have hs' : At s 1748 (drainRootFrame p l g) := by
      simpa only [ite_eq_right (Nat.not_lt_of_ge hIndex)] using hs.mono hs.2.2.2.2.2
    obtain ⟨v,hMove,hv⟩ := loaderFirstDrainAddress (g := g) hp hIndex s hs'
    have hRunA := (loaderLinear (regs := []) (by decide) (by decide) hs'.1
      (by simp) (by decide +kernel) hMove).1
    let acc : Acc := {loc := globalLoc (p.cuQBase + 4*laneOf l g), size := 4}
    have hRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
    change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRange
    have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
    have hOut : out kernel Assumptions.all l g v = .ev (.read acc (afterLoad v [7184])) := by
      rw [loaderOutCore (by rw [hv.1]; decide) (by rw [hv.1]; decide)]
      rw [out_event hv.2.2.2.1 (by rw [hv.1]; exact Flow.code_1750) rfl rfl]
      change Out.ev (loadTmpl [] l g v .global false 32 [7184] 7858 0) = _
      exact congrArg Out.ev (loadTmpl_global hv.2.1 hv.2.2.2.2.1 (by omega)
        (by decide) (by omega))
    let hn : Next kernel Assumptions.all l g t v (.read acc (afterLoad v [7184])) :=
      ⟨hLocal.trans (run_rtg hRunA), hOut⟩
    exact ⟨_,hIndex,(hn.uniqueScalarReadAt hv.1 hRun hPos he
      (fun _ _ hp => afterFirstDrainReadFloor hp)).2⟩
  · have hSite : s.pc = 1751 := by simpa only [ite_eq_left (Nat.lt_of_not_ge hIndex)] using hs.1
    have hMem : (⟨1750,.rd a bytes⟩ : Event) ∈ (X.tr g).drop pos := by
      apply List.mem_of_getElem? (i := j-pos)
      rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
      exact he
    exact (Nat.not_le_of_gt (by decide : 1750 < 1751)
      (afterFirstDrainReadFloor hSite.ge (hRun.after_local_nonempty hLocal hMore) _ hMem)).elim

/-- The loader's first optional lookup after finishing its active request. -/
@[no_expose] def FirstDrainCuQRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop :=
  X.get i = some ⟨1750,.rd a bytes⟩

/-- The first active drain lookup addresses the requesting lane's launch word. -/
theorem FirstDrainCuQRead.word {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X)
    {i : EvId} {a : Acc} {bytes : List (Option Byte)} (he : FirstDrainCuQRead X i a bytes) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4*index), size := 4} := by
  obtain ⟨g,j⟩ := i
  exact firstDrainCuQReadWord hp hX hCuQ he

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
