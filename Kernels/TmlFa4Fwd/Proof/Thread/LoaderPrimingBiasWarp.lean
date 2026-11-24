-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderFirstBiasOrigins
import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
import Kernels.TmlFa4Fwd.Proof.LoaderBiasTensorActor
import Lemmas.Flow.Elect
import Lemmas.Flow.TensorIssue
import Kernels.TmlFa4Fwd.Flow.Code.Part008
import Lemmas.Flow.ElectMask

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader Epilogue Prologue

private def biasLoaderRoots (l : Launch) (warp : Fin 2) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]

private def biasLoaderRole (l : Launch) (warp : Fin 2) : List (Nat × Value) :=
  (123, .pred (warp.val != 0)) :: biasLoaderRoots l warp

private theorem primingBiasTailBranches (bound : Nat) :
    ((kernel.code.drop 780).take (1901 - 780)).all
      (fun i => loaderPipelineCutOp 780 1901 bound [2535, 1062] i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem biasFullLoaderBranches (bound : Nat) :
    ((kernel.code.drop 174).take (1901 - 174)).all
      (fun i => loaderPipelineCutOp 174 1901 bound [2535, 1062] i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

/-- A loader event below a closed program-counter cut lies in the actual visits before it. -/
theorem loaderEventInClosedSlice {l : Launch} {g stop : Nat} (warp : Fin 2)
    (hStop : 174 ≤ stop) (hLimit : stop ≤ 1901)
    (hTail : ∀ bound, ((kernel.code.drop stop).take (1901 - stop)).all
      (fun i => loaderPipelineCutOp stop 1901 bound [2535, 1062] i.op) = true)
    {s : TState} {es : List Event} {vs : List Visit} {e : Event}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : 174 ≤ s.pc ∧ s.pc ≤ 1901) (hs : RingShape s)
    (hF : Holds s.regs [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
    (he : e ∈ es) (hEnd : e.pc < stop) : e ∈ loaderSliceEvents 174 stop vs := by
  have hActive {s : TState} {es : List Event} {vs : List Visit}
      (hw : Walk kernel Assumptions.all l g s es vs) (hPc : 174 ≤ s.pc ∧ s.pc ≤ 1901)
      (hs : RingShape s) (hF : Holds s.regs (biasLoaderRoots l warp)) (he : e ∈ es) :
      s.pc < stop := by
    by_contra! h
    have hRange := (loaderWalkEventRange warp hStop
      ⟨h, hPc.2⟩ hs hF hTail hw e he).1
    omega
  have hAdvance {s u : TState} {e : Option Event} (hs : RingShape s)
      (hPc : 174 ≤ s.pc ∧ s.pc < stop) (hF : Holds s.regs (biasLoaderRoots l warp))
      (hw : WStep kernel Assumptions.all l g s e u) :
      (174 ≤ u.pc ∧ u.pc ≤ 1901) ∧ RingShape u ∧ Holds u.regs (biasLoaderRoots l warp) := by
    obtain ⟨hLo, hHi, ht, hHeld⟩ := pipelineCutStep (F := biasLoaderRoots l warp)
      (by decide) (by decide) ⟨hPc.1, by omega⟩ (biasFullLoaderBranches u.pc) hw hs hF
    exact ⟨⟨hLo, hHi.resolve_right (Nat.lt_irrefl _)⟩, ht, hHeld⟩
  induction hw with
  | stop => cases he
  | @tau t u es vs ht hw ih =>
    have hIn := hActive (.tau ht hw) hPc hs hF he
    obtain ⟨hU, hShape, hFrame⟩ := hAdvance hs ⟨hPc.1, hIn⟩ hF (.inl ⟨rfl, ht⟩)
    simpa [loaderSliceEvents, visit, hPc.1, hIn] using ih hU hShape hFrame he
  | @ev t u ev es vs hStep hw ih =>
    have hIn := hActive (.ev hStep hw) hPc hs hF he
    rcases List.mem_cons.mp he with rfl | he
    · simp [loaderSliceEvents, visit, hPc.1, hIn]
    · obtain ⟨hU, hShape, hFrame⟩ := hAdvance hs ⟨hPc.1, hIn⟩ hF (.inr ⟨_, rfl, hStep⟩)
      simp only [loaderSliceEvents, List.takeWhile_cons, visit, hPc.1, hIn,
        decide_true, Bool.true_and, ↓reduceIte, List.filterMap_cons, List.mem_cons]
      exact .inr (ih hU hShape hFrame he)
  | @last t ev hStep =>
    obtain rfl := List.mem_singleton.mp he
    have h := estep_source_pc hStep
    have hIn : t.pc < stop := by omega
    simp [loaderSliceEvents, visit, hPc.1, hIn]

/-- A recorded event in a loader slice occurs in the underlying event trace. -/
theorem memEventsOfLoaderSlice {l : Launch} {g lower stop : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {e : Event}
    (hw : Walk kernel Assumptions.all l g s es vs) (he : e ∈ loaderSliceEvents lower stop vs) :
    e ∈ es := by
  induction hw with
  | stop => simp [loaderSliceEvents] at he
  | @tau t u es vs ht hw ih =>
    by_cases hp : lower ≤ t.pc ∧ t.pc < stop
    · exact ih (by simpa [loaderSliceEvents, visit, hp.1, hp.2] using he)
    · simp [loaderSliceEvents, visit, hp] at he
  | @ev t u ev es vs h hw ih =>
    by_cases hp : lower ≤ t.pc ∧ t.pc < stop
    · simp only [loaderSliceEvents, List.takeWhile_cons, visit, hp.1, hp.2, decide_true,
        Bool.true_and, ↓reduceIte, List.filterMap_cons, List.mem_cons] at he
      exact List.mem_cons.mpr (he.imp_right ih)
    · simp [loaderSliceEvents, visit, hp] at he
  | @last t ev h =>
    by_cases hp : lower ≤ t.pc ∧ t.pc < stop
    · simpa [loaderSliceEvents, visit, hp.1, hp.2] using he
    · simp [loaderSliceEvents, visit, hp] at he

private theorem biasWalkAfterTau {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs) (hNonempty : es ≠ [])
    (hTau : Tau kernel Assumptions.all l g s u) :
    ∃ vs', Walk kernel Assumptions.all l g u es vs' := by
  cases hw with
  | stop => exact (hNonempty rfl).elim
  | tau ht hw => exact ⟨_, tau_det ht hTau ▸ hw⟩
  | ev hActual _ => exact (not_tau_of_stops (stops_of_estep hActual) hTau).elim
  | last hActual => exact (not_tau_of_stops (stops_of_estep hActual) hTau).elim

/-- Follow known local loader steps without consuming an event from a nonempty walk. -/
theorem loaderWalkAfterLocals {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs) (hNonempty : es ≠ [])
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u) :
    ∃ vs', Walk kernel Assumptions.all l g u es vs' := by
  induction hLocal with
  | refl => exact ⟨_, hw⟩
  | tail _ ht ih =>
    obtain ⟨_, hW⟩ := ih
    exact biasWalkAfterTau hW hNonempty ht

private theorem biasLoaderRoleTest {l : Launch} {g : Nat} (warp : Fin 2) :
    Seg kernel Assumptions.all l g 1 538 (biasLoaderRoots l warp) 539
      (biasLoaderRole l warp) := by
  have hCore : Seg kernel [] l g 1 538 (biasLoaderRoots l warp) 539
      (biasLoaderRole l warp) := by
    intro s hs
    fin_cases warp <;>
      (simp only [biasLoaderRole, biasLoaderRoots] at hs ⊢; seg_fp hs using rfl)
  intro s hs
  obtain ⟨u, hu, hAt⟩ := hCore.apply hs
  exact ⟨u, (loaderLinear (regs := []) (by decide) (by decide) hs.1 (by simp) rfl hu).1, hAt⟩

private theorem biasLoaderRoleGate {l : Launch} {g : Nat} {s : TState} (warp : Fin 2)
    (hs : At s 676 (biasLoaderRole l warp)) :
    Tau kernel Assumptions.all l g s (if warp.val = 0 then next s else { s with pc := 780 }) := by
  unfold Tau
  rw [loaderOutCore (by rw [hs.1]; decide) (by rw [hs.1]; decide)]
  fin_cases warp <;>
    simp [out, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, Flow.code_676, guardHolds,
      readReg, skip, next, bind, Except.bind, pure, Except.pure, execLocalA_nil, execLocal,
      execBranch, Op.isLocal, Op.rule]

private theorem loaderWalkEventBefore {l : Launch} {g lower stop : Nat} {s : TState}
    {es : List Event} {vs : List Visit}
    (hWalk : Walk kernel Assumptions.all l g s es vs)
    (hBefore : ∀ v ∈ vs, lower ≤ v.pc ∧ v.pc < stop)
    {e : Event} (he : e ∈ es) : e.pc < stop := by
  induction hWalk with
  | stop => cases he
  | tau _ _ ih => exact ih (fun v hv => hBefore v (List.mem_cons_of_mem _ hv)) he
  | ev hStep _ ih =>
    rcases List.mem_cons.mp he with rfl | hmem
    · exact (estep_source_pc hStep).trans_lt (hBefore _ List.mem_cons_self).2
    · exact ih (fun v hv => hBefore v (List.mem_cons_of_mem _ hv)) hmem
  | last hStep =>
    obtain rfl := List.mem_singleton.mp he
    exact (estep_source_pc hStep).trans_lt (hBefore _ List.mem_cons_self).2

private theorem biasDrainBranches (bound : Nat) :
    ((kernel.code.drop 1862).take (1901 - 1862)).all
      (fun i => loaderPipelineCutOp 1862 1901 bound [2535,1062] i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem biasBeforeRoleGate (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {event : Event} (he : X.get (g,j) = some event)
    (hRange : 677 ≤ event.pc ∧ event.pc ≤ 1383) (hContinue : ¬ Ends event) :
    ∃ (warp : Fin 2) (s : TState) (pre tail : List Event) (visits : List Visit),
      14 + warp.val = warpIndex l g ∧ 5 ≤ j ∧ (X.tr g).drop 5 = pre ++ tail ∧
      (∀ e ∈ pre, e.pc < 677) ∧ At s 676 (biasLoaderRole l warp) ∧
      Walk kernel Assumptions.all l g s tail visits ∧ event ∈ tail := by
  obtain ⟨warp,t,vs,hW,hBound,hT,hWalk,hGet⟩ := biasInstructionWalk hp hX he hRange
  have hSeen := loaderEventInClosedSlice warp (by decide) (by decide : 1862 ≤ 1901)
    biasDrainBranches hWalk (by rw [hT.1]; decide) (ringShapeOfAt hT)
    hT.2.2.2.2 (List.mem_of_getElem? hGet) (by omega)
  have hCode : ((kernel.code.drop 174).take (538 - 174)).all
      (fun i => loaderPipelineCutOp 174 538 (1862 - 1) [2535,1062] i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨u,pre,tail,front,post,hSplit,_,hFront,hu,hShape,hFrame,hPre,hTail,hSaw⟩ :=
    loaderObservedCut (F := biasLoaderRoots l warp) (by decide) (by decide) (by decide)
      (by decide : 538 < 1862) hCode hWalk (by rw [hT.1]; decide) (ringShapeOfAt hT)
      hT.2.2.2.2 hSeen (by omega) hContinue
  have hMem := memEventsOfLoaderSlice hTail hSaw
  have hU : At u 538 (biasLoaderRoots l warp) := pipelineAtCut hu hShape hFrame
    (walkWithContinuingEventClean hTail hMem hContinue) ⟨_,Flow.code_538,rfl⟩
  obtain ⟨v,hv,hV⟩ := (biasLoaderRoleTest (g := g) warp).apply hU
  obtain ⟨other,hOther⟩ := biasWalkAfterTau hTail (List.ne_nil_of_mem hMem)
    (tauStep_iff.mp (by simpa [run] using hv))
  have hSeen' := loaderEventInClosedSlice warp (by decide) (by decide : 1862 ≤ 1901)
    biasDrainBranches hOther (by rw [hV.1]; decide) (ringShapeOfAt hV)
    hV.2.2.2.2.2 hMem (by omega)
  have hCode : ((kernel.code.drop 539).take (676 - 539)).all
      (fun i => loaderPipelineCutOp 539 676 (1862 - 1) [123,2535,1062] i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨s,pre',rest,front',post',hSplit',_,hFront',hs,hSh,hFr,hPre',hRest,hSaw'⟩ :=
    loaderObservedCut (F := biasLoaderRole l warp) (by decide) (by decide) (by decide)
      (by decide : 676 < 1862) hCode hOther (by rw [hV.1]; decide) (ringShapeOfAt hV)
      hV.2.2.2.2 hSeen' (by omega) hContinue
  have hMem' := memEventsOfLoaderSlice hRest hSaw'
  have hS : At s 676 (biasLoaderRole l warp) := pipelineAtCut hs hSh hFr
    (walkWithContinuingEventClean hRest hMem' hContinue) ⟨_,Flow.code_676,rfl⟩
  refine ⟨warp,s,pre ++ pre',rest,post',hW,hBound,by simp [hSplit,hSplit',List.append_assoc],
    ?_,hS,hRest,hMem'⟩
  intro e hm
  rcases List.mem_append.mp hm with hm | hm
  · exact (loaderWalkEventBefore hPre hFront hm).trans (by decide)
  · exact (loaderWalkEventBefore hPre' hFront' hm).trans (by decide)

private theorem primingBiasAfterRoleGate (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index addr pc : Nat} {spec : TensorCopy.Spec}
    (hLo : 677 ≤ pc) (hHi : pc < 780) (he : X.get (g, index) = some ⟨pc, .tensorIssue addr spec⟩) :
    ∃ pos t visits, warpIndex l g = 14 ∧ At t 677 (biasLoaderRoots l 0) ∧
      Walk kernel Assumptions.all l g t ((X.tr g).drop pos) visits ∧
      (⟨pc, .tensorIssue addr spec⟩ : Event) ∈ loaderSliceEvents 174 780 visits := by
  let event : Event := ⟨pc,.tensorIssue addr spec⟩
  have hContinue : ¬ Ends event := by simp [event, Ends]
  obtain ⟨warp,s,pre,tail,visits,hWarp,_,hSplit,_,hS,hWalk,hMem⟩ :=
    biasBeforeRoleGate hp hX he ⟨hLo,by change pc ≤ 1383; omega⟩ hContinue
  have hRole : warp.val = 0 := by
    by_contra hRole
    have hGate := biasLoaderRoleGate (g := g) warp hS
    rw [ite_eq_right hRole] at hGate
    obtain ⟨_,hRest⟩ := biasWalkAfterTau hWalk (List.ne_nil_of_mem hMem) hGate
    have hState : At { s with pc := 780 } 780 (biasLoaderRoots l warp) := by
      exact ⟨rfl,hS.2.1,hS.2.2.1,hS.2.2.2.1,hS.2.2.2.2.2⟩
    have hBad := (loaderWalkEventRange warp (by decide)
      (show 780 ≤ 780 ∧ 780 ≤ 1901 by decide) (ringShapeOfAt hState) hState.2.2.2.2
      primingBiasTailBranches hRest event hMem).1
    exact (not_le_of_gt hHi) hBad
  have hIssuer : warpIndex l g = 14 := by rw [← hWarp,hRole,Nat.add_zero]
  obtain rfl : warp = 0 := Fin.ext hRole
  have hBranch : Tau kernel Assumptions.all l g s (next s) := by
    simpa using biasLoaderRoleGate (g := g) 0 hS
  obtain ⟨after,hAfter⟩ := biasWalkAfterTau hWalk (List.ne_nil_of_mem hMem) hBranch
  have hState : At (next s) 677 (biasLoaderRoots l 0) := (hS.mono hS.2.2.2.2.2).next
  have hDrop : (X.tr g).drop (5 + pre.length) = tail := by
    simp [← List.drop_drop,hSplit]
  refine ⟨_,next s,after,hIssuer,hState,hDrop.symm ▸ hAfter,?_⟩
  exact loaderEventInClosedSlice 0 (by decide) (by decide) primingBiasTailBranches
    hAfter (by rw [hState.1]; decide) (ringShapeOfAt hState) hState.2.2.2.2 hMem hHi

private theorem biasWarp14PrimingCut (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {event : Event} (he : X.get (g,j) = some event)
    (hRange : 780 ≤ event.pc ∧ event.pc ≤ 1383) (hWarp : warpIndex l g = 14)
    (hContinue : ¬ Ends event) :
    ∃ (s : TState) (pre tail : List Event) (visits : List Visit),
      5 ≤ j ∧ (X.tr g).drop 5 = pre ++ tail ∧ (∀ e ∈ pre, e.pc < 677) ∧
      At s 677 (biasLoaderRoots l 0) ∧
      Walk kernel Assumptions.all l g s tail visits ∧
      event ∈ loaderSliceEvents 174 1862 visits := by
  obtain ⟨warp,s,pre,tail,_,hW,hBound,hSplit,hBefore,hS,hWalk,hMem⟩ :=
    biasBeforeRoleGate hp hX he ⟨by omega,hRange.2⟩ hContinue
  obtain rfl : warp = 0 := Fin.ext (by omega)
  have hBranch : Tau kernel Assumptions.all l g s (next s) := by
    simpa using biasLoaderRoleGate (g := g) 0 hS
  obtain ⟨after,hAfter⟩ := biasWalkAfterTau hWalk (List.ne_nil_of_mem hMem) hBranch
  have hState : At (next s) 677 (biasLoaderRoots l 0) := (hS.mono hS.2.2.2.2.2).next
  refine ⟨next s,pre,tail,after,hBound,hSplit,hBefore,hState,hAfter,?_⟩
  exact loaderEventInClosedSlice 0 (by decide) (by decide : 1862 ≤ 1901)
    biasDrainBranches hAfter (by rw [hState.1]; decide) (ringShapeOfAt hState)
    hState.2.2.2.2 hMem (by omega)

/-- All actual priming Bias issues come from warp 14, before the two loader roles converge. -/
theorem primingBiasIssuerWarp (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index addr pc : Nat} {spec : TensorCopy.Spec} (hLo : 677 ≤ pc) (hHi : pc < 780)
    (he : X.get (g, index) = some ⟨pc, .tensorIssue addr spec⟩) :
    warpIndex l g = 14 := by
  obtain ⟨_, _, _, hWarp, _, _, _⟩ := primingBiasAfterRoleGate hp hX hLo hHi he
  exact hWarp

/-- The full-warp election immediately upstream of each priming Bias copy. -/
def primingBiasElectPc : Fin 2 → Fin 2 → Nat
  | 0, 0 => 712
  | 0, 1 => 720
  | 1, 0 => 765
  | 1, 1 => 772

private def primingBiasElectDst : Fin 2 → Fin 2 → Nat
  | 0, 0 => 1901
  | 0, 1 => 1904
  | 1, 0 => 1921
  | 1, 1 => 1923

private def primingBiasElectPred : Fin 2 → Fin 2 → Nat
  | 0, 0 => 148
  | 0, 1 => 150
  | 1, 0 => 160
  | 1, 1 => 162

private theorem primingBiasElectCode (stage half : Fin 2) :
    kernel.code[primingBiasElectPc stage half]? = some ⟨none, .warp ⟨.elect, none,
      [some (primingBiasElectDst stage half), some (primingBiasElectPred stage half)], [],
      some (.imm (-1))⟩⟩ := by
  fin_cases stage <;> fin_cases half
  · exact Flow.code_712
  · exact Flow.code_720
  · exact Flow.code_765
  · exact Flow.code_772

private theorem primingBiasElectNegation {l : Launch} {g : Nat} (stage half : Fin 2)
    (flag result : Bool) (hResult : (!flag) = result) :
    Seg kernel [] l g (firstBiasPrepPc stage half - primingBiasElectPc stage half - 2)
      (primingBiasElectPc stage half + 1)
      [(primingBiasElectPred stage half, .pred flag)] (firstBiasPrepPc stage half - 1)
      [(primingBiasElectPred stage half + 1, .pred result)] := by
  fin_cases stage <;> fin_cases half
  all_goals
    dsimp [primingBiasElectPc, primingBiasElectPred, firstBiasPrepPc, firstBiasPrepSteps,
      firstBiasIssueSite, inputSite]
    intro t ht
    seg_fp ht using rw [← hResult]

private theorem primingBiasFallsThrough {l : Launch} {g : Nat} {s : TState}
    (stage half : Fin 2)
    (hRoots : Holds s.regs (biasLoaderRoots l 0))
    (hs : At s (primingBiasElectPc stage half + 1)
      [(primingBiasElectPred stage half, .pred true)]) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (firstBiasPrepPc stage half) (biasLoaderRoots l 0) := by
  let start := primingBiasElectPc stage half + 1
  let branch := firstBiasPrepPc stage half - 1
  obtain ⟨v,hRun,hV⟩ := (primingBiasElectNegation (l := l) (g := g)
    stage half true false rfl).apply hs
  have hFrame : ((kernel.code.drop start).take (branch - start)).all
      (fun i => [2535,1062].all (fun r => !(writesRegs i.op).contains r)) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hStraight : ((kernel.code.drop start).take (branch - start - 1)).all
      (fun i => schedulerFallsThrough i.op) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hBound : start + (branch - start) ≤ 1906 := by fin_cases stage <;> fin_cases half <;> decide
  have hn : firstBiasPrepPc stage half - primingBiasElectPc stage half - 2 = branch - start := by
    fin_cases stage <;> fin_cases half <;> decide
  rw [hn] at hRun
  obtain ⟨hr,hStable⟩ := loaderLinear (by fin_cases stage <;> fin_cases half <;> decide)
    hBound hs.1 hFrame hStraight hRun
  have hVBase : Holds v.regs (biasLoaderRoots l 0) :=
    holdsSchedulerFrame hRoots hStable (fun pair hp => List.mem_map_of_mem hp)
  have hBranch : Tau kernel Assumptions.all l g v (next v) := by
    unfold Tau
    rw [loaderOutCore (by rw [hV.1]; fin_cases stage <;> fin_cases half <;> decide)
      (by rw [hV.1]; fin_cases stage <;> fin_cases half <;> decide)]
    have hPred := hV.2.2.2.2.1
    fin_cases stage <;> fin_cases half <;>
      dsimp [firstBiasPrepPc, firstBiasPrepSteps, firstBiasIssueSite, inputSite,
        primingBiasElectPred] at hV hPred ⊢
    all_goals simp [out, hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hPred, Flow.code_714,
      Flow.code_722, Flow.code_767, Flow.code_775, guardHolds, readReg, skip, next, bind,
      Except.bind, pure, Except.pure]
  have hNext : firstBiasPrepPc stage half - 1 + 1 = firstBiasPrepPc stage half := by
    fin_cases stage <;> fin_cases half <;> decide
  exact ⟨next v,(run_rtg hr).tail hBranch,hNext ▸ (hV.mono hVBase).next⟩

private theorem primingBiasSelectedBranch {l : Launch} {g : Nat} {s : TState}
    (stage half : Fin 2)
    (hs : At s (firstBiasPrepPc stage half - 1)
      [(primingBiasElectPred stage half + 1, .pred true)]) :
    Tau kernel Assumptions.all l g s
      { s with pc := (inputSite (firstBiasIssueSite stage half)).pc + 1 } := by
  have hLo : 174 ≤ s.pc := by rw [hs.1]; fin_cases stage <;> fin_cases half <;> decide
  have hHi : s.pc < 1906 := by rw [hs.1]; fin_cases stage <;> fin_cases half <;> decide
  unfold Tau
  rw [loaderOutCore hLo hHi]
  have hPred := hs.2.2.2.2.1
  fin_cases stage <;> fin_cases half <;>
    dsimp [firstBiasPrepPc, firstBiasPrepSteps, firstBiasIssueSite, inputSite, primingBiasElectPred]
      at hs hPred ⊢
  all_goals simp [out, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hPred, Flow.code_714,
    Flow.code_722, Flow.code_767, Flow.code_775, guardHolds, readReg, bind,
    Except.bind, pure, Except.pure, execLocalA_nil, execLocal, execBranch, Op.isLocal, Op.rule]

/-- Each priming Bias issue is executed by the lane selected by its full-warp election. -/
theorem primingBiasElectedIssuer (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage half : Fin 2) {g index addr : Nat} {spec : TensorCopy.Spec}
    (he : X.get (g, index) = some
      ⟨(inputSite (firstBiasIssueSite stage half)).pc, .tensorIssue addr spec⟩) :
    ∃ j inst, X.Elect (g, j) (primingBiasElectPc stage half) (2 ^ 32 - 1) inst (laneOf l g) := by
  let site := inputSite (firstBiasIssueSite stage half)
  let elect := primingBiasElectPc stage half
  let event : Event := ⟨site.pc, .tensorIssue addr spec⟩
  have hLo : 677 ≤ elect := by fin_cases stage <;> fin_cases half <;> decide
  have hBefore : elect < site.pc := by fin_cases stage <;> fin_cases half <;> decide
  have hHi : site.pc < 780 := by fin_cases stage <;> fin_cases half <;> decide
  obtain ⟨pos, t, visits, _, hAt, hWalk, hSaw⟩ :=
    primingBiasAfterRoleGate hp hX (by omega : 677 ≤ site.pc) hHi he
  have hCode : ((kernel.code.drop 677).take (elect - 677)).all
      (fun i => loaderPipelineCutOp 677 elect (780 - 1) [2535, 1062] i.op) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hContinues : ¬ Ends event := by simp [event, Ends]
  obtain ⟨s, pre, rest, _, post, hSplit, _, _, hs, hShape, hRegs, _, hRest, hSeen⟩ :=
    loaderObservedCut (F := biasLoaderRoots l 0) (by decide) (by decide) (by omega : elect ≤ 1901)
      (by omega : elect < 780) hCode hWalk (by rw [hAt.1]; exact ⟨le_rfl, hLo⟩)
      (ringShapeOfAt hAt) hAt.2.2.2.2 hSaw hBefore.le hContinues
  have hSeenMem := memEventsOfLoaderSlice hRest hSeen
  have hSLo : 174 ≤ s.pc := by omega
  have hSHi : s.pc < 1906 := by omega
  change s.pc = primingBiasElectPc stage half at hs
  cases hRest with
  | stop => cases hSeenMem
  | @tau s u es vs ht _ =>
    have hCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore hSLo hSHi]
    exact (tau_core_not_event (hs.symm ▸ primingBiasElectCode stage half) rfl hCore).elim
  | @last s e hStep =>
    obtain rfl := List.mem_singleton.mp hSeenMem
    obtain ⟨_, _, hFire⟩ := hStep
    exact (hContinues (fires_none_ends hFire)).elim
  | @ev s u ev es vs hStep hTail =>
    have hMark : ev ≠ event := by
      intro hEq
      have hs' := estep_source_pc hStep
      rw [hEq, hs] at hs'
      exact (ne_of_lt hBefore) hs'.symm
    have hMem := (List.mem_cons.mp hSeenMem).resolve_left (Ne.symm hMark)
    obtain ⟨ins, hc, _, hf⟩ := estep_event_source hStep
    rw [hs, primingBiasElectCode stage half] at hc
    obtain rfl := Option.some.inj hc
    have hFire : Fires s.pc (eventTmpl Assumptions.all l g s (.warp ⟨.elect, none,
        [some (primingBiasElectDst stage half), some (primingBiasElectPred stage half)], [],
        some (.imm (-1))⟩)) ev (some u) := hf
    obtain ⟨mask, inst, leader, hEv, hu⟩ := fires_elect hFire
    have hE : ev = ⟨elect, .elect (2 ^ 32 - 1) inst leader⟩ := by
      rcases fires_elect_mask (bits := BitVec.ofNat 64 (2 ^ 32 - 1)) rfl hFire with
        ⟨instanceId, selected, he'⟩ | ⟨fault, hFault⟩
      · rw [hs] at he'
        obtain ⟨rfl, rfl, rfl⟩ := Kind.elect.inj (congrArg Event.kind (hEv.symm.trans he'))
        exact he'
      · cases congrArg Event.kind (hEv.symm.trans hFault)
    have hReg := (pipelineCutStep (F := biasLoaderRoots l 0) (by decide) (by decide)
      ⟨hSLo, by omega⟩ (biasFullLoaderBranches u.pc) (.inr ⟨ev, rfl, hStep⟩) hShape hRegs).2.2
    have hU : At u (elect + 1)
        [(primingBiasElectPred stage half, .pred (laneOf l g == leader))] := by
      refine pipelineAtCut (pc := elect + 1) ?_ hReg.1 ⟨?_, trivial⟩
        (walkWithContinuingEventClean hTail hMem hContinues) ?_
      · rw [hu]
        change s.pc + 1 = elect + 1
        exact congrArg (· + 1) hs
      · rw [hu]
        simp [next, setReg]
      · fin_cases stage <;> fin_cases half
        · exact ⟨_, Flow.code_713, rfl⟩
        · exact ⟨_, Flow.code_721, rfl⟩
        · exact ⟨_, Flow.code_766, rfl⟩
        · exact ⟨_, Flow.code_773, rfl⟩
    have hSelected : laneOf l g = leader := by
      by_contra hNe
      have hFlag : (laneOf l g == leader) = false := by simp [hNe]
      rw [hFlag] at hU
      obtain ⟨v, hv, hV⟩ :=
        (primingBiasElectNegation (l := l) (g := g) stage half false true rfl).apply hU
      have hLinear : ((kernel.code.drop (elect + 1)).take
          (firstBiasPrepPc stage half - elect - 2)).all (fun i => [2535, 1062].all
            (fun r => !(writesRegs i.op).contains r)) = true := by
        fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
      have hStraight : ((kernel.code.drop (elect + 1)).take
          (firstBiasPrepPc stage half - elect - 2 - 1)).all
          (fun i => schedulerFallsThrough i.op) = true := by
        fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
      have hBound : elect + 1 + (firstBiasPrepPc stage half - elect - 2) ≤ 1906 := by
        fin_cases stage <;> fin_cases half <;> decide
      obtain ⟨hvA, hvR⟩ := loaderLinear (by omega : 174 ≤ elect + 1) hBound
        hU.1 hLinear hStraight hv
      have hVBase : Holds v.regs (biasLoaderRoots l 0) :=
        holdsSchedulerFrame hReg.2 hvR (fun pair hp => List.mem_map_of_mem hp)
      have hRegV : At v (firstBiasPrepPc stage half - 1) [(primingBiasElectPred stage half + 1,
          .pred true)] := hV
      have hBranch := primingBiasSelectedBranch (l := l) (g := g) stage half hRegV
      obtain ⟨_, hFinal⟩ := loaderWalkAfterLocals hTail (List.ne_nil_of_mem hMem)
        ((run_rtg hvA).tail hBranch)
      have hCutAll (b : Nat) :
          ((kernel.code.drop (site.pc + 1)).take (1901 - (site.pc + 1))).all
            (fun i => loaderPipelineCutOp (site.pc + 1) 1901 b [2535, 1062] i.op) = true := by
        fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
      have hAfter : At { v with pc := site.pc + 1 } (site.pc + 1) (biasLoaderRoots l 0) :=
        ⟨rfl, hV.2.1, hV.2.2.1, hV.2.2.2.1, hVBase⟩
      have hPc : site.pc + 1 ≤ site.pc :=
        (loaderWalkEventRange 0 (by omega : 174 ≤ site.pc + 1)
          (show site.pc + 1 ≤ site.pc + 1 ∧ site.pc + 1 ≤ 1901 by omega)
          (ringShapeOfAt hAfter) hAfter.2.2.2.2 hCutAll hFinal event hMem).1
      omega
    have hInTrace : ev ∈ X.tr g := by
      apply List.mem_of_mem_drop (i := pos)
      rw [hSplit]
      exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hInTrace
    refine ⟨j, inst, ?_⟩
    change (X.tr g)[j]? = some ⟨elect, .elect (2 ^ 32 - 1) inst (laneOf l g)⟩
    rw [hSelected, ← hE]
    exact hj

/-- A recurring Bias issuer has already issued this stage and half's priming copy.
The uses of a full-warp election on both paths select the same physical lane. -/
theorem primingBiasEarlierThanRepeated (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {stage half : Fin 2}
    {spec : TensorCopy.Spec} (hBox : BiasSubbox p l X (g,j) stage half spec) {pc : Nat}
    (he : X.get (g,j) = some ⟨pc,.tensorIssue p.biasMapAddress spec⟩) (hLater : 780 ≤ pc) :
    ∃ k < j, ∃ other, BiasSubbox p l X (g,k) stage half other := by
  let later : Event := ⟨pc,.tensorIssue p.biasMapAddress spec⟩
  let elect := primingBiasElectPc stage half
  let site := inputSite (firstBiasIssueSite stage half)
  obtain ⟨i,_,_,hi⟩ := biasTensorSelectorOfSubbox hp hX hBox
  have hPc : pc = (biasTensorSelector i).issue :=
    congrArg Event.pc (Option.some.inj (he.symm.trans hi))
  have hLast : pc ≤ 1383 := hPc.trans_le (by fin_cases i <;> decide)
  have hContinue : ¬ Ends later := by simp [later, Ends]
  have hWarp := biasTensorActorWarp hp hX hBox
  obtain ⟨_,_,inst,hElected⟩ := biasTensorActualElection hp hX i (g := g) (j := j) hi
  obtain ⟨s,pre,tail,visits,hBound,hSplit,hBefore,hS,hWalk,hSeen⟩ :=
    biasWarp14PrimingCut hp hX he ⟨hLater,hLast⟩ hWarp hContinue
  have hCode : ((kernel.code.drop 677).take (elect - 677)).all
      (fun ins => loaderPipelineCutOp 677 elect (1862 - 1) [2535,1062] ins.op) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hElect : 677 ≤ elect ∧ elect < 780 := by fin_cases stage <;> fin_cases half <;> decide
  have hIssue : elect < site.pc ∧ site.pc < 780 := by fin_cases stage <;> fin_cases half <;> decide
  obtain ⟨t,pre',rest,front,post,hSplit',_,hFront,ht,hShape,hRegs,hPre,hRest,hSaw⟩ :=
    loaderObservedCut (F := biasLoaderRoots l 0) (by decide) (by decide) (by omega)
      (by omega : elect < 1862) hCode hWalk (by rw [hS.1]; exact ⟨le_rfl,hElect.1⟩)
      (ringShapeOfAt hS) hS.2.2.2.2 hSeen (by change elect ≤ pc; omega) hContinue
  have hMem := memEventsOfLoaderSlice hRest hSaw
  change t.pc = primingBiasElectPc stage half at ht
  have hTLo : 174 ≤ t.pc := by omega
  have hTHi : t.pc < 1901 := by omega
  have get {n : Nat} {e : Event} (hAt : rest[n]? = some e) :
      X.get (g,5 + pre.length + pre'.length + n) = some e := by
    change (X.tr g)[5 + pre.length + pre'.length + n]? = some e
    rw [← List.getElem?_drop, ← List.drop_drop, ← List.drop_drop, hSplit,
      List.drop_left,hSplit',List.drop_left]
    exact hAt
  cases hRest with
  | stop => cases hMem
  | @tau t u events visits hTau _ =>
    have hCore : Tau kernel [] l g t u := by
      unfold Tau at hTau ⊢
      rwa [← loaderOutCore hTLo (by omega)]
    exact (tau_core_not_event (ht.symm ▸ primingBiasElectCode stage half) rfl hCore).elim
  | last hStep =>
    obtain rfl := List.mem_singleton.mp hMem
    obtain ⟨_,_,hFire⟩ := hStep
    exact (hContinue (fires_none_ends hFire)).elim
  | @ev t u event events visits hStep hTail =>
    have hNe : event ≠ later := by
      intro h
      have hAddr := congrArg Event.pc h
      rw [estep_source_pc hStep, ht] at hAddr
      change elect = pc at hAddr
      omega
    have hRemaining := (List.mem_cons.mp hMem).resolve_left (Ne.symm hNe)
    obtain ⟨ins,hC,_,hFire⟩ := estep_event_source hStep
    rw [ht, primingBiasElectCode stage half] at hC
    obtain rfl := Option.some.inj hC
    obtain ⟨mask,instanceId,leader,hEvent,hu⟩ := fires_elect hFire
    have hFull : event = ⟨elect,.elect (2^32-1) instanceId leader⟩ := by
      rcases fires_elect_mask (bits := BitVec.ofNat 64 (2^32-1)) rfl hFire with
        ⟨inst',leader',hf⟩ | ⟨fault,hf⟩
      · rw [ht] at hf
        obtain ⟨_,rfl,rfl⟩ := Kind.elect.inj (congrArg Event.kind (hEvent.symm.trans hf))
        exact hf
      · cases congrArg Event.kind (hEvent.symm.trans hf)
    have hActual := get (n := 0) (e := event) rfl
    rw [hFull,Nat.add_zero] at hActual
    have hg := event_thread_lt hX he
    have hLeader := hX.elect.deterministic hActual hElected ⟨⟨hg,hg,rfl⟩,rfl⟩
    have hShape' := loaderPipelineStepShape hTLo hTHi hShape (.inr ⟨_,rfl,hStep⟩)
    have hU : At u (elect + 1) [(primingBiasElectPred stage half, .pred true)] := by
      refine pipelineAtCut (pc := elect + 1) ?_ hShape' ⟨?_,trivial⟩
        (walkWithContinuingEventClean hTail hRemaining hContinue) ?_
      · rw [hu]
        change t.pc + 1 = elect + 1
        exact congrArg (· + 1) ht
      · rw [hu]
        simp [next,setReg,hLeader]
      · fin_cases stage <;> fin_cases half
        · exact ⟨_,Flow.code_713,rfl⟩
        · exact ⟨_,Flow.code_721,rfl⟩
        · exact ⟨_,Flow.code_766,rfl⟩
        · exact ⟨_,Flow.code_773,rfl⟩
    have hRoot := (pipelineCutStep (F := biasLoaderRoots l 0) (by decide) (by decide)
      ⟨hTLo,by omega⟩ (biasFullLoaderBranches u.pc) (.inr ⟨event,rfl,hStep⟩) hShape hRegs).2.2.2
    obtain ⟨v,hTau,hV⟩ := primingBiasFallsThrough stage half hRoot hU
    obtain ⟨restVisits,hContinueWalk⟩ :=
      loaderWalkAfterLocals hTail (List.ne_nil_of_mem hRemaining) hTau
    let start := firstBiasPrepPc stage half
    have hStart : 174 ≤ start ∧ start ≤ site.pc := by
      fin_cases stage <;> fin_cases half <;> decide
    have hSeen' := loaderEventInClosedSlice 0 (by decide) (by decide : 1862 ≤ 1901)
      biasDrainBranches hContinueWalk (by rw [hV.1]; change 174 ≤ start ∧ start ≤ 1901; omega)
      (ringShapeOfAt hV) hV.2.2.2.2 hRemaining (by change pc < 1862; omega)
    have hCode' : ((kernel.code.drop start).take (site.pc - start)).all
        (fun ins => loaderPipelineCutOp start site.pc (1862 - 1) [2535,1062] ins.op) = true := by
      fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
    obtain ⟨w,beforeIssue,afterIssue,beforeVisits,afterVisits,hIssueSplit,_,hIssueFront,hW,_,_,
        hIssuePre,hFinal,hFinalSeen⟩ :=
      loaderObservedCut (F := biasLoaderRoots l 0) hStart.1 hStart.1 (by omega)
        (by omega : site.pc < 1862) hCode' hContinueWalk (by rw [hV.1]; exact ⟨le_rfl,hStart.2⟩)
        (ringShapeOfAt hV) hV.2.2.2.2 hSeen' (by change site.pc ≤ pc; omega) hContinue
    have hFinalMem := memEventsOfLoaderSlice hFinal hFinalSeen
    have hWave : w.pc = (inputSite (firstBiasIssueSite stage half)).pc := hW
    cases hFinal with
    | stop => cases hFinalMem
    | @tau t u events vs hTau _ =>
      have hRange : 174 ≤ w.pc ∧ w.pc < 1906 := by
        rw [hW]
        omega
      have hCore : Tau kernel [] l g w u := by
        unfold Tau at hTau ⊢
        rwa [← loaderOutCore hRange.1 hRange.2]
      have hIns := inputSiteCode (firstBiasIssueSite stage half)
      dsimp only at hIns
      rw [← hWave] at hIns
      exact (tau_core_not_event hIns rfl hCore).elim
    | last hStep =>
      obtain rfl := List.mem_singleton.mp hFinalMem
      obtain ⟨_,_,hFire⟩ := hStep
      exact (hContinue (fires_none_ends hFire)).elim
    | @ev t u prime suffix vs hStep hTail =>
      have hPrimeIndex : (event :: events)[beforeIssue.length+1]? = some prime := by
        rw [List.getElem?_cons_succ, hIssueSplit, List.getElem?_append_right (by simp)]
        simp
      have hSeenPrime := get hPrimeIndex
      obtain ⟨ins,hc,_,hFire⟩ := estep_event_source hStep
      rw [hWave,inputSiteCode (firstBiasIssueSite stage half)] at hc
      obtain rfl := Option.some.inj hc
      obtain ⟨address,other,hPrime,_,_⟩ := fires_cpTensor_issue hFire
      rw [hWave] at hPrime
      rw [hPrime] at hSeenPrime
      obtain ⟨hAddress,_,_,hShared,_,_⟩ := actualInputBoxAt hp hX
        (firstBiasIssueSite stage half) hSeenPrime
      have hSharedEq : site.sharedOffset = 166912 + 32768 * stage.val + 16384 * half.val := by
        fin_cases stage <;> fin_cases half <;> decide
      have hGet : ((X.tr g).drop 5)[j-5]? = some later := by
        rw [List.getElem?_drop,Nat.add_sub_of_le hBound]
        exact he
      have hLen : pre.length + pre'.length + (beforeIssue.length + 1) < j-5 := by
        by_contra! hNot
        let early := pre ++ pre' ++ [event] ++ beforeIssue ++ [prime]
        have hEarly : ∀ e ∈ early, e.pc < 780 := by
          intro e hm
          rcases List.mem_append.mp hm with hm | hm
          · rcases List.mem_append.mp hm with hm | hm
            · rcases List.mem_append.mp hm with hm | hm
              · rcases List.mem_append.mp hm with hm | hm
                · exact (hBefore e hm).trans (by decide)
                · exact (loaderWalkEventBefore hPre hFront hm).trans hElect.2
              · obtain rfl := List.mem_singleton.mp hm
                simpa [hFull] using hElect.2
            · exact (loaderWalkEventBefore hIssuePre hIssueFront hm).trans hIssue.2
          · obtain rfl := List.mem_singleton.mp hm
            simpa [hPrime] using hIssue.2
        have hDecomp : (X.tr g).drop 5 = early ++ suffix := by
          rw [hSplit,hSplit',hIssueSplit]
          simp [early,List.append_assoc]
        have hj : j-5 < early.length := by
          simp only [early,List.length_append,List.length_cons,List.length_nil]
          omega
        rw [hDecomp,List.getElem?_append_left hj] at hGet
        exact (not_lt_of_ge hLater) (hEarly later (List.mem_of_getElem? hGet))
      let primeId : EvId := (g,5 + pre.length + pre'.length + (beforeIssue.length+1))
      have hMap : address = p.biasMapAddress := by
        fin_cases stage <;> fin_cases half <;> exact hAddress
      rw [hMap] at hSeenPrime
      have hMbar : other.mbar = biasReadyObject l (g/l.block) stage := by
        have hMbar := loaderTensorOffset hp hX (firstBiasIssueSite stage half) hSeenPrime
        have hOff : inputBarrierBase (firstBiasIssueSite stage half) + site.barrierOffset =
            320 + 8 * stage.val := by
          fin_cases stage <;> fin_cases half <;> rfl
        rw [biasReadyObject, ← hOff]
        exact hMbar
      obtain ⟨_,side,hOther⟩ := biasSubboxOfBarrier hp hX stage
        (i := primeId) ⟨site.pc,hSeenPrime⟩ hMbar
      have hSide := congrArg Loc.addr (hShared.symm.trans hOther.2.2.1)
      change l.sharedBase + site.sharedOffset =
        l.sharedBase + (166912 + 32768 * stage.val + 16384 * side.val) at hSide
      rw [hSharedEq] at hSide
      have hSame : half = side := Fin.ext (by omega)
      exact ⟨primeId.2,by dsimp [primeId]; omega,other,hSame.symm ▸ hOther⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
