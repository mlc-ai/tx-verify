-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderBiasBudgetGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasTensorOrdinal
import Kernels.TmlFa4Fwd.Proof.LoaderBiasTailGuard
import Kernels.TmlFa4Fwd.Proof.LoaderBiasWarmCount
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingPrefixCoordinates
import Kernels.TmlFa4Fwd.Proof.LoaderWarmEntry
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Proof.OutputProtection
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
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue Epilogue Thread.Loader

private def biasPrimeIndex (stage half : Fin 2) : Fin 14 :=
  if stage = 0 then (if half = 0 then 2 else 3) else (if half = 0 then 6 else 7)

private def biasTailIndex (half : Fin 2) : Fin 14 := if half = 0 then 12 else 13

private def tensorMarker (opSite : Nat) (ev : Event) : Bool :=
  match ev.kind with
  | .tensorIssue .. => ev.pc == opSite
  | _ => false

private theorem tensorMarkerSite {pos : Nat} {e : Event} (h : tensorMarker pos e = true) :
    e.pc = pos ∧ ∃ addr spec, e.kind = .tensorIssue addr spec := by
  obtain ⟨loc,kind⟩ := e
  cases kind <;> simp [tensorMarker] at h
  exact ⟨h,_,_,rfl⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The actual Bias issuer retains its selected trip bounds after priming. -/
theorem biasTripFrameOfEvent (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g j : Nat} (hWarp : warpIndex l g = 14) {target : Event}
    (he : X.get (g,j) = some target) (hBounds : 488 ≤ target.pc ∧ target.pc < 1862) :
    ∃ batch < p.batch, tilePrefix p batch * p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1) * p.heads ∧
      let tile := (assignedCoordinates p batch (g/l.block)).1
      let trips := Mma.trips p batch tile
      ∃ pos s result, pos ≤ j ∧ At s 488
        [(1062,b32 14),(1088,b32 trips),(1089,b32 (vPrimingResidual p batch tile)),
          (1091,b32 (trips-1))] ∧
        Run kernel Assumptions.all l g s ((X.tr g).drop pos) result := by
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g := Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hWork := loaderOwnPrefixEventRequiresActiveTile hp hX hWarp.ge hCuQ he
    (by omega) hBounds.2
  have hFootprint := (outputIntentFootprint hp hX).performed
  obtain ⟨batch,hb,hLo,hHi,pos,hBefore,s,result,hs,hr,_⟩ :=
    loaderPrimingMetadataOfActiveEvent hp hX (event_thread_lt hX he) hWarp.ge hl
      (fun _ _ _ _ => loaderOutputWrites hFootprint) hWork (hLane.symm ▸ he) (by omega)
  obtain ⟨hTile,hHead⟩ := assignedCoordinates_valid hp hLo hHi
  obtain ⟨t,ht,hT⟩ := primingKActiveToAddressLane hp hb hTile hs
  obtain ⟨_,u,hu,hU⟩ :=
    primingVAdmissionWithTripsLane hp hb (hHead.trans hp.heads_signed) hTile hl hT
  have hSuffix := hr.after_local_nonempty (ht.trans hu)
    (traceAfterObservedEvent (hLane.symm ▸ he) hBefore)
  rw [hLane] at hSuffix
  refine ⟨batch,hb,hLo,hHi,pos,u,result,hBefore,hU.mono ?_,hSuffix⟩
  repeat' apply And.intro
  all_goals first
    | trivial
    | exact holds_mem hU.2.2.2.2 (by simp [primingVTripFrame,primingVAdmissionCarry,hWarp])

private theorem tensorSiteOnce {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    (site : Fin 14) (g : Nat)
    (hAudit : (kernel.code.drop ((inputSite site).pc+1)).all
      (fun i => Thread.staysPastEvent ((inputSite site).pc+1) i.op) = true)
    (hSegments : Assumptions.swExp2Sites.all (fun atPc =>
      match cuteExp2.matchAt kernel atPc with
      | some seg => decide ((inputSite site).pc+1 ≤ seg.stop) | none => false) = true) :
    (X.tr g).countP (tensorMarker (inputSite site).pc) ≤ 1 := by
  let mark := tensorMarker (inputSite site).pc
  by_contra! hCount
  change 1 < (X.tr g).countP mark at hCount
  obtain ⟨a,e,he,hm,hZero⟩ := MbarRing.Slot.exists_nth_countP mark
    (show 0+1 ≤ (X.tr g).countP mark by omega)
  obtain ⟨b,f,hf,hn,hOne⟩ := MbarRing.Slot.exists_nth_countP mark
    (show 1+1 ≤ (X.tr g).countP mark by omega)
  have hA : X.get (g,a) = some e := he
  have hB : X.get (g,b) = some f := hf
  have hALen := (List.getElem?_eq_some_iff.mp he).1
  have hBLen := (List.getElem?_eq_some_iff.mp hf).1
  have hOrder : a < b := by
    by_contra! h
    have hMono := countP_take_mono mark (X.tr g) h
    omega
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX hA)
  obtain ⟨s,u,hStep,hTail⟩ := hr.after_event he (by omega)
  have hs := (estep_source_pc hStep).symm.trans (tensorMarkerSite hm).1
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source hStep
  rw [hs,inputSiteCode site] at hCode
  obtain rfl := Option.some.inj hCode
  obtain ⟨_,_,_,rfl,_⟩ := fires_cpTensor_issue hFire
  have hPc : (inputSite site).pc+1 ≤ (next s).pc := by rw [show (next s).pc = s.pc+1 from rfl,hs]
  have hIndex : a+1 ≤ b := by omega
  have hMember : f ∈ (X.tr g).drop (a+1) := by
    apply List.mem_of_getElem? (i := b-(a+1))
    rw [List.getElem?_drop,Nat.add_sub_of_le hIndex]
    exact hf
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun hTail
  have hLater := Thread.eventTailEvents hAudit hSegments hWalk hPc f hMember
  have hTooEarly := (tensorMarkerSite hn).1
  omega

private theorem primingBiasCount {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage half : Fin 2) (g : Nat) :
    (X.tr g).countP (tensorMarker (inputSite (biasPrimeIndex stage half)).pc) ≤ 1 := by
  apply tensorSiteOnce hX
  all_goals fin_cases stage <;> fin_cases half <;>
    set_option maxRecDepth 100000 in kernel_rfl

private theorem tailBiasCount {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (half : Fin 2) (g : Nat) :
    (X.tr g).countP (tensorMarker (inputSite (biasTailIndex half)).pc) ≤ 1 := by
  apply tensorSiteOnce hX
  all_goals fin_cases half <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem warmCountFromPrimingFrame {l : Launch} {X : Execution} {g j pos trips : Nat}
    {s : TState} {result : Option TState} {e : Event} (stage half : Fin 2)
    (hTrips : trips < 2^31) (hs : At s 488 [(1088,b32 trips),(1091,b32 (trips-1))])
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) result)
    (he : X.get (g,j) = some e) (hPos : pos ≤ j)
    (hMark : tensorMarker (warmBiasIssueSite stage half) e = true)
    (hPrefix : ((X.tr g).take j).countP (tensorMarker (warmBiasIssueSite stage half)) = 0) :
    (X.tr g).countP (tensorMarker (warmBiasIssueSite stage half)) ≤ min (trips-1) 9 := by
  let marker := tensorMarker (warmBiasIssueSite stage half)
  have hSite := (tensorMarkerSite hMark).1
  have hSafe : ∀ f, e.kind ≠ .ub f := by
    obtain ⟨_,_,hk⟩ := (tensorMarkerSite hMark).2
    rw [hk]
    rintro _ ⟨⟩
  have hLate : 917 ≤ e.pc := by rw [hSite]; fin_cases stage <;> fin_cases half <;> decide
  have hEarly : e.pc < 1353 := by rw [hSite]; fin_cases stage <;> fin_cases half <;> decide
  have hAudit : ∀ branch, ((kernel.code.drop 488).take (908 - 488)).all
      (fun ins => loaderPipelineCutOp 488 908 branch [1088,1091] ins.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨u,index,result,hAt,hRun,hOrder⟩ :=
    observedBiasCut (start := 488) (stop := 908) (by decide) hs hAudit hr he hPos
      (by omega) hSafe
  obtain ⟨v,hMove,hV⟩ := loaderWarmGate (g := g) hTrips hAt
  have hVRun := hRun.after_local_nonempty (run_rtg hMove) (traceAfterObservedEvent he hOrder)
  have hLarge : 2 ≤ trips := by
    by_contra! hSmall
    have hv : 1353 ≤ v.pc := by simpa [hSmall] using hV.1.ge
    obtain ⟨_,hWalk⟩ := Mma.walkFromRun hVRun
    have hFloor : (kernel.code.drop 1353).all (fun i => Thread.staysPastEvent 1353 i.op) =
        true := by set_option maxRecDepth 100000 in kernel_rfl
    have hSegments : Assumptions.swExp2Sites.all (fun site =>
        match cuteExp2.matchAt kernel site with
        | some seg => decide (1353 ≤ seg.stop)
        | none => false) = true := by set_option maxRecDepth 100000 in kernel_rfl
    have hLater : e ∈ (X.tr g).drop index := by
      apply List.mem_of_getElem? (i := j-index)
      rw [List.getElem?_drop,Nat.add_sub_of_le hOrder]
      exact he
    exact (Nat.not_le_of_lt hEarly) (Thread.eventTailEvents hFloor hSegments hWalk hv e hLater)
  have hStart : At v 912 [(1091,b32 (trips-1))] := by simpa [Nat.not_lt.mpr hLarge] using hV
  have hSeedCode : ∀ branch, ((kernel.code.drop 912).take (913 - 912)).all
      (fun ins => loaderPipelineCutOp 912 913 branch [1091] ins.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨a,seed,_,ha,haRun,haOrder⟩ :=
    observedBiasCut (start := 912) (stop := 913) (by decide) hStart hSeedCode hVRun
      he hOrder (by omega) hSafe
  obtain ⟨b,hb,hB⟩ := (warmCounterSeedCore (l := l) (g := g)).apply (ha.mono trivial)
  obtain ⟨hbAll,hBKeep⟩ := loaderLinear (regs := [1091]) (by decide) (by decide) ha.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hb
  have hBRun := haRun.after_local_nonempty (run_rtg hbAll) (traceAfterObservedEvent he haOrder)
  have hBAt : At b 914 [(7174,b32 0),(1091,b32 (trips-1))] :=
    hB.mono ⟨hB.2.2.2.2.1,(hBKeep _ (by decide)).trans ha.2.2.2.2.1,trivial⟩
  have hBodyCode : ∀ branch, ((kernel.code.drop 914).take (917 - 914)).all
      (fun ins => loaderPipelineCutOp 914 917 branch [7174,1091] ins.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨t,start,_,ht,htRun,htOrder⟩ :=
    observedBiasCut (start := 914) (stop := 917) (by decide) hBAt hBodyCode hBRun
      he haOrder hLate hSafe
  obtain ⟨_,hWalk⟩ := Mma.walkFromRun htRun
  have hCount := warmBiasIssuesFromEntry stage half
    (show trips-1 < 2^31 by omega) (show 0 < min (trips-1) 9 by omega) ht hWalk
  have hMono : ((X.tr g).drop start).countP marker ≤
      ((X.tr g).drop start).countP (fun e => e.pc == warmBiasIssueSite stage half) := by
    apply List.countP_mono_left
    exact fun e _ h => beq_iff_eq.mpr (tensorMarkerSite h).1
  have hNone : ((X.tr g).take start).countP marker = 0 := by
    change ((X.tr g).take j).countP marker = 0 at hPrefix
    have h : ((X.tr g).take start).countP marker ≤ ((X.tr g).take j).countP marker :=
      countP_take_mono marker (X.tr g) htOrder
    omega
  change (X.tr g).countP marker ≤ _
  conv_lhs => rw [← List.take_append_drop start (X.tr g)]
  rw [List.countP_append,hNone,Nat.zero_add]
  exact hMono.trans (by simpa using hCount)

private theorem halfMarkerCovered (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} (stage half : Fin 2) {e : Event} (he : X.get (g,j) = some e)
    (hm : biasTensorHalf l (g/l.block) stage half e = true) :
    let priming := tensorMarker (inputSite (biasPrimeIndex stage half)).pc e
    let warm := tensorMarker (warmBiasIssueSite stage half) e
    let tail := tensorMarker (inputSite (biasTailIndex half)).pc e
    (priming || warm || (stage == 0 && tail)) = true := by
  obtain ⟨source,kind⟩ := e
  cases kind <;> try cases hm
  rename_i addr spec
  have hOffset := (of_decide_eq_true hm).2
  obtain ⟨site,rfl⟩ := actualInputIssuePc hX he
  obtain ⟨_,_,_,hLoc,_,_⟩ := actualInputBoxAt hp hX site he
  have hDst := congrArg Loc.addr (hLoc.symm.trans hOffset)
  change l.sharedBase + (inputSite site).sharedOffset =
    l.sharedBase + (166912 + 32768 * stage.val + 16384 * half.val) at hDst
  have hClass (stage half : Fin 2) (i : Fin 14) :
      (inputSite i).sharedOffset = 166912 + 32768 * stage.val + 16384 * half.val →
      ((inputSite i).pc == (inputSite (biasPrimeIndex stage half)).pc ||
        (inputSite i).pc == warmBiasIssueSite stage half ||
        (stage == 0 && (inputSite i).pc == (inputSite (biasTailIndex half)).pc)) = true := by
    fin_cases stage <;> fin_cases half <;> fin_cases i <;> decide
  exact hClass stage half site (Nat.add_left_cancel hDst)

/-- An actual Bias half occurs within the priming, warm, and optional tail budget
of the tile assigned by the consistent execution. -/
theorem biasTensorOrdinalWithinBudget (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X) {e : EvId}
    {stage half : Fin 2} {s : TensorCopy.Spec} (hBox : BiasSubbox p l X e stage half s) :
    ∃ batch < p.batch, tilePrefix p batch * p.heads ≤ e.1/l.block ∧
      e.1/l.block < tilePrefix p (batch+1) * p.heads ∧
      biasTensorOrdinal l X stage half e <
        biasLoaderBudget p batch (assignedCoordinates p batch (e.1/l.block)).1 stage := by
  obtain ⟨g,j⟩ := e
  have hw := biasTensorActorWarp hp hX hBox
  obtain ⟨source,he⟩ := hBox.1
  have hBound : 488 ≤ source ∧ source < 1862 := by
    obtain ⟨i,hi⟩ := actualInputIssuePc hX he
    rw [hi]
    fin_cases i <;> decide
  obtain ⟨batch,hb,hLo,hHi,pos,v,result,hPos,hAt,hRun⟩ :=
    biasTripFrameOfEvent hp hX hCuQ hw he hBound
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let trips := Mma.trips p batch tile
  have hWork : g/l.block < tilePrefix p p.batch * p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hTripLt (b : Nat) (hB : b < p.batch)
      (hLow : tilePrefix p b * p.heads ≤ g/l.block)
      (hHigh : g/l.block < tilePrefix p (b+1) * p.heads) :
      Mma.trips p b (assignedCoordinates p b (g/l.block)).1 < 2^31 := by
    have hCeil := (Mma.trips_bounds hp hB (assignedCoordinates_valid hp hLow hHigh).1).2.1
    have hLen := (hp.lengths b hB).2.2
    omega
  let prime := tensorMarker (inputSite (biasPrimeIndex stage half)).pc
  let warm := tensorMarker (warmBiasIssueSite stage half)
  let tail := fun f => stage == 0 && tensorMarker (inputSite (biasTailIndex half)).pc f
  have hPrime : (X.tr g).countP prime ≤ 1 := primingBiasCount hX stage half g
  have hWarm : (X.tr g).countP warm ≤ min (trips-1) 9 := by
    by_cases hz : (X.tr g).countP warm = 0
    · simp [hz]
    have hPos : 0+1 ≤ (X.tr g).countP warm := by omega
    obtain ⟨k,f,hGet,hMark,hZero⟩ := MbarRing.Slot.exists_nth_countP warm hPos
    have hSite := (tensorMarkerSite hMark).1
    have hSiteBounds : 488 ≤ f.pc ∧ f.pc < 1862 := by
      rw [hSite]
      fin_cases stage <;> fin_cases half <;> decide
    obtain ⟨b,hB,hLow,hHigh,index,w,final,hBefore,hFrame,hRest⟩ :=
      biasTripFrameOfEvent hp hX hCuQ hw (show X.get (g,k) = some f from hGet) hSiteBounds
    have hSame := (hUnique b ⟨hB,hLow,hHigh⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
    subst b
    exact warmCountFromPrimingFrame stage half (hTripLt batch hb hLo hHi)
      (hFrame.mono ⟨hFrame.2.2.2.2.2.1,hFrame.2.2.2.2.2.2.2.1,trivial⟩)
      hRest hGet hBefore hMark hZero
  have hTail : (X.tr g).countP tail ≤ biasTailExtra p batch tile stage := by
    by_cases hz : (X.tr g).countP tail = 0
    · simp [hz]
    have hPos : 0+1 ≤ (X.tr g).countP tail := by omega
    obtain ⟨k,f,hGet,hMark,_⟩ := MbarRing.Slot.exists_nth_countP tail hPos
    obtain ⟨hStage,hMark⟩ := Bool.and_eq_true_iff.mp hMark
    have hStage' : stage = 0 := beq_iff_eq.mp hStage
    have hSite := (tensorMarkerSite hMark).1
    have hSiteBounds : 1376 ≤ f.pc ∧ f.pc < 1384 := by rw [hSite]; fin_cases half <;> decide
    obtain ⟨b,hB,hLow,hHigh,index,w,final,hBefore,hFrame,hRest⟩ :=
      biasTripFrameOfEvent hp hX hCuQ hw (show X.get (g,k) = some f from hGet)
        ⟨by omega,by omega⟩
    have hSame := (hUnique b ⟨hB,hLow,hHigh⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
    subst b
    have hSafe : ∀ fault, f.kind ≠ .ub fault := by
      obtain ⟨_,_,hk⟩ := (tensorMarkerSite hMark).2
      rw [hk]
      rintro _ ⟨⟩
    have hResidue : vPrimingResidual p batch tile < 2^32 := Nat.mod_lt _ (by decide)
    obtain ⟨hTrips,hResid⟩ :=
      biasTailGuardOfPrimingFrame (hTripLt batch hb hLo hHi) hResidue
        (hFrame.mono ⟨hFrame.2.2.2.2.1,hFrame.2.2.2.2.2.1,hFrame.2.2.2.2.2.2.1,trivial⟩)
        hRest hGet hBefore hSiteBounds hSafe
    have hCap : (X.tr g).countP tail ≤ 1 := by
      simpa [tail,hStage'] using tailBiasCount hX half g
    unfold biasTailExtra
    rw [ite_eq_left ⟨hStage',hTrips,hResid⟩]
    exact hCap
  let marked := fun f => prime f || warm f || tail f
  let target := biasTensorHalf l (g/l.block) stage half
  have hCover : (X.tr g).countP target ≤ (X.tr g).countP marked := by
    apply List.countP_mono_left
    intro f hMem hMark
    obtain ⟨k,hGet⟩ := List.mem_iff_getElem?.mp hMem
    exact halfMarkerCovered hp hX stage half (show X.get (g,k) = some f from hGet) hMark
  have hSplit : (X.tr g).countP marked ≤
      (X.tr g).countP prime + (X.tr g).countP warm + (X.tr g).countP tail := by
    generalize X.tr g = xs
    induction xs with
    | nil => rfl
    | cons f rest ih =>
      simp only [List.countP_cons,marked]
      simp only [marked] at ih
      cases prime f <;> cases warm f <;> cases tail f <;>
        simp only [Bool.false_or,Bool.true_or,Bool.false_eq_true,ite_false,ite_true] <;>
        omega
  have hBudget : (X.tr g).countP target ≤ biasLoaderBudget p batch tile stage := by
    have h := hCover.trans hSplit
    change _ ≤ 1 + min (trips-1) 9 + biasTailExtra p batch tile stage
    omega
  have hHere : target ⟨source,.tensorIssue p.biasMapAddress s⟩ = true :=
    decide_eq_true ⟨hBox.2.1,hBox.2.2.1⟩
  have hCount := countP_take_succ (p := target) he hHere
  have hMono := countP_take_mono target (X.tr g) (i := j+1) (j := (X.tr g).length)
    (Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp he).1)
  rw [hCount,List.take_length] at hMono
  refine ⟨batch,hb,hLo,hHi,?_⟩
  change ((X.tr g).take j).countP target < biasLoaderBudget p batch tile stage
  omega

end PTX.Kernels.TmlFa4Fwd.Loader
