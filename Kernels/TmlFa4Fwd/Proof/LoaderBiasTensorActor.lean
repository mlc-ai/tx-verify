-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderBiasGuard
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasCredits
import Lemmas.Flow.ElectActor
import Lemmas.Flow.ContinuingEvent
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Flow.Code.Part011
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part018
import Kernels.TmlFa4Fwd.Flow.Code.Part021

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

/-- The current stage and half at each Bias tensor site's selecting election. -/
structure BiasTensorSelector where
  input : Fin 14
  stage : Fin 2
  half : Fin 2
  elect : Nat
  destination : Nat
  result : Nat
  branch : Nat

/-- The two halves in each of the priming, recurring and final Bias packets. -/
def biasTensorSelector : Fin 10 → BiasTensorSelector
  | 0 => ⟨2, 0, 0, 712, 1901, 148, 714⟩
  | 1 => ⟨3, 0, 1, 720, 1904, 150, 722⟩
  | 2 => ⟨6, 1, 0, 765, 1921, 160, 767⟩
  | 3 => ⟨7, 1, 1, 772, 1923, 162, 775⟩
  | 4 => ⟨8, 0, 0, 1154, 2042, 188, 1156⟩
  | 5 => ⟨9, 0, 1, 1164, 2047, 190, 1166⟩
  | 6 => ⟨10, 1, 0, 1183, 2055, 194, 1185⟩
  | 7 => ⟨11, 1, 1, 1192, 2059, 196, 1194⟩
  | 8 => ⟨12, 0, 0, 1370, 2124, 205, 1372⟩
  | 9 => ⟨13, 0, 1, 1377, 2126, 207, 1379⟩

/-- The selected tensor issue instruction of this Bias half. -/
def BiasTensorSelector.issue (s : BiasTensorSelector) : Nat := (inputSite s.input).pc

private theorem tensorSelectorRange (i : Fin 10) :
    let s := biasTensorSelector i
    174 ≤ s.elect ∧ s.elect < s.branch ∧ s.branch < s.issue ∧ s.issue < 1901 := by
  fin_cases i <;> decide

private def selectorElect (s : BiasTensorSelector) : Op :=
  .warp ⟨.elect, none, [some s.destination, some s.result], [], some (.imm (-1))⟩

private theorem selectorElectCode (i : Fin 10) :
    let s := biasTensorSelector i
    kernel.code[s.elect]? = some ⟨none, selectorElect s⟩ := by
  fin_cases i
  · exact Flow.code_712
  · exact Flow.code_720
  · exact Flow.code_765
  · exact Flow.code_772
  · exact Flow.code_1154
  · exact Flow.code_1164
  · exact Flow.code_1183
  · exact Flow.code_1192
  · exact Flow.code_1370
  · exact Flow.code_1377

private theorem selectorBranchCode (i : Fin 10) :
    let s := biasTensorSelector i
    kernel.code[s.branch]? = some ⟨some (s.result + 1, false), .bra (s.issue + 1) false⟩ := by
  fin_cases i
  · exact Flow.code_714
  · exact Flow.code_722
  · exact Flow.code_767
  · exact Flow.code_775
  · exact Flow.code_1156
  · exact Flow.code_1166
  · exact Flow.code_1185
  · exact Flow.code_1194
  · exact Flow.code_1372
  · exact Flow.code_1379

private theorem selectorNegation {l : Launch} {g : Nat} (i : Fin 10) :
    let s := biasTensorSelector i
    Seg kernel [] l g (s.branch - s.elect - 1) (s.elect + 1) [(s.result, .pred false)]
      s.branch [(s.result + 1, .pred true)] := by
  fin_cases i <;> dsimp [biasTensorSelector] <;> intro t ht <;> seg_fp ht using rfl

private def selectorInterior (s : BiasTensorSelector) (pc : Nat) : Prop :=
  s.elect < pc ∧ pc ≤ s.issue

private instance (s : BiasTensorSelector) (pc : Nat) : Decidable (selectorInterior s pc) :=
  inferInstanceAs (Decidable (s.elect < pc ∧ pc ≤ s.issue))

private def selectorLanding (s : BiasTensorSelector) (pc : Nat) (op : Op) : Bool :=
  match op with
  | .bra dst _ => decide (selectorInterior s dst → selectorInterior s pc)
  | .brx .. => false
  | _ => true

private theorem selectorLandingAt (i : Fin 10) {pc : Nat} {ins : Instr}
    (hLo : 174 ≤ pc) (hHi : pc < 1901) (hc : kernel.code[pc]? = some ins) :
    selectorLanding (biasTensorSelector i) pc ins.op = true := by
  let code := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have hAll : code.all (fun (ins, pc) => selectorLanding (biasTensorSelector i) pc ins.op) =
      true := by fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (ins,pc)
  apply List.mem_of_getElem? (i := pc - 174)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem followsSelector {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (i : Fin 10) (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hShape : RingShape s) (hIn : selectorInterior (biasTensorSelector i) u.pc)
    (hOut : ¬ selectorInterior (biasTensorSelector i) s.pc)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    s.pc = (biasTensorSelector i).elect := by
  have next (hp : u.pc = s.pc ∨ u.pc = s.pc + 1) :
      s.pc = (biasTensorSelector i).elect := by
    unfold selectorInterior at hIn hOut
    omega
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore hLo (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code hCore
    rcases tau_core_frame hc hCore with rfl | hFrame
    · exact next (.inr rfl)
    have hPc := hFrame.pc
    have hSafe := selectorLandingAt i hLo hHi hc
    cases hOp : ins.op <;> simp only [hOp, nextPc, BrxTarget, or_false] at hPc
    case bra dst align =>
      rw [hOp] at hSafe
      exact (hOut (of_decide_eq_true hSafe (hPc ▸ hIn))).elim
    case brx => simp [hOp, selectorLanding] at hSafe
    all_goals exact next (.inr hPc)
  · obtain ⟨_, hPc | ⟨hPc, _⟩⟩ := loaderEventProgress hLo (by omega) hShape.1 he
    · exact next (.inr hPc)
    · exact next (.inl hPc)


private def BeforeTensorSelection (i : Fin 10) (l : Launch) (g : Nat) (s : TState) : Prop :=
  let site := biasTensorSelector i
  selectorInterior site s.pc →
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧ u.pc = site.issue + 1

private def tensorSelected (i : Fin 10) (l : Launch) (g : Nat) (e : Event) : Prop :=
  ∃ inst, e = ⟨(biasTensorSelector i).elect, .elect (2^32-1) inst (laneOf l g)⟩

private theorem skipUnselectedTensor {l : Launch} {g : Nat} {s : TState} (i : Fin 10)
    (hPc : s.pc = (biasTensorSelector i).elect + 1) (hShape : RingShape s)
    (hClean : s.fault = none) (hPred : s.regs (biasTensorSelector i).result = some (.pred false)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      u.pc = (biasTensorSelector i).issue + 1 := by
  let site := biasTensorSelector i
  let F : List (Nat × Value) := [(site.result, .pred false)]
  have hDef : ∃ ins, kernel.code[site.elect+1]? = some ins ∧ ins.op.isLocal = true := by
    have hAll : (List.ofFn (fun j : Fin 10 =>
        (kernel.code[(biasTensorSelector j).elect + 1]?).any (·.op.isLocal))).all id =
        true := by set_option maxRecDepth 100000 in kernel_rfl
    have hs : (kernel.code[site.elect + 1]?).any (·.op.isLocal) = true :=
      List.all_eq_true.mp hAll _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    cases hc : kernel.code[site.elect + 1]? with
    | none => simp [hc] at hs
    | some ins => exact ⟨ins, rfl, by simpa [hc] using hs⟩
  have hStart : At s (site.elect+1) F := pipelineAtCut hPc hShape ⟨hPred, trivial⟩ hClean hDef
  obtain ⟨v, hRun, hV⟩ := (selectorNegation (l := l) (g := g) i).apply hStart
  have hRange : 174 ≤ site.elect ∧ site.elect < site.branch ∧
      site.branch < site.issue ∧ site.issue < 1901 := tensorSelectorRange i
  have hRight : site.elect + 1 + (site.branch - site.elect - 1) = site.branch := by
    omega
  obtain ⟨hr, _⟩ := loaderLinear (regs := []) (lo := site.elect + 1)
    (n := site.branch - site.elect - 1)
    (by omega) (by rw [hRight]; omega) hStart.1 (by simp) (by
      fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl) hRun
  have hc : kernel.code[site.branch]? = some
      ⟨some (site.result+1, false), .bra (site.issue + 1) false⟩ := selectorBranchCode i
  have hvPc : v.pc = site.branch := hV.1
  rw [← hvPc] at hc
  have hReg : v.regs (site.result + 1) = some (.pred true) := hV.2.2.2.2.1
  have hBranch : Tau kernel Assumptions.all l g v { v with pc := site.issue + 1 } := by
    unfold Tau
    rw [loaderOutCore (by omega) (by omega)]
    simp [out, hV.2.2.2.1, hc, guardHolds, readReg, hReg, bind, Except.bind, pure,
      Except.pure, execLocalA_nil, execLocal, execBranch, Op.isLocal, Op.rule]
  exact ⟨_, (run_rtg hr).tail hBranch, rfl⟩

private theorem selectorLeaderNegation {l : Launch} {g : Nat} (i : Fin 10) :
    let s := biasTensorSelector i
    Seg kernel [] l g (s.branch - s.elect - 1) (s.elect + 1) [(s.result, .pred true)]
      s.branch [(s.result + 1, .pred false)] := by
  fin_cases i <;> dsimp [biasTensorSelector] <;> intro t ht <;> seg_fp ht using rfl

/-- After the full-warp selection of this physical lane, the guard falls through
to the contiguous local preparation for the selected tensor. -/
theorem biasSelectedTensorGate {l : Launch} {g : Nat} {s : TState} (i : Fin 10)
    (hs : At s ((biasTensorSelector i).elect+1) [((biasTensorSelector i).result,.pred true)]) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u ((biasTensorSelector i).branch+1) [] := by
  let site := biasTensorSelector i
  obtain ⟨v,hPath,hV⟩ := (selectorLeaderNegation (l := l) (g := g) i).apply hs
  have hRange : 174 ≤ site.elect ∧ site.elect < site.branch ∧
      site.branch < site.issue ∧ site.issue < 1901 := tensorSelectorRange i
  have hRight : site.elect+1+(site.branch-site.elect-1) = site.branch := by omega
  obtain ⟨hCore,_⟩ := loaderLinear (regs := []) (lo := site.elect+1)
    (n := site.branch-site.elect-1) (by omega) (by rw [hRight]; omega) hs.1 (by simp)
    (by fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl) hPath
  have hVPc : v.pc = site.branch := hV.1
  have hc : kernel.code[v.pc]? = some
      ⟨some (site.result+1, false),.bra (site.issue+1) false⟩ :=
    hVPc.symm ▸ selectorBranchCode i
  have hReg : v.regs (site.result+1) = some (.pred false) := hV.2.2.2.2.1
  have hTau : Tau kernel Assumptions.all l g v (skip v) := by
    unfold Tau
    rw [loaderOutCore (by omega) (by omega)]
    simp [out, hV.2.2.2.1, hc, guardHolds, readReg, hReg, bind, Except.bind, pure,
      Except.pure]
  have hNext : (skip v).pc = site.branch+1 := by simp [skip,hVPc]
  refine ⟨skip v,(run_rtg hCore).tail hTau, ?_⟩
  exact ⟨hNext,rfl,rfl,hV.2.2.2.1,trivial⟩

/-- All full-mask elections by the actual tensor issuer make that lane eligible
at another selected packet, independently of the elected site's iteration. -/
theorem biasSelectedElectionFrame {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (i : Fin 10)
    {g k j pc inst : Nat} {s u : TState} {e : Event}
    (hKnown : X.Elect (g,k) pc (2^32-1) inst (laneOf l g))
    (hTrace : X.get (g,j) = some e)
    (hs : At s (biasTensorSelector i).elect [])
    (hStep : EStep kernel Assumptions.all l g s e (some u)) :
    At u ((biasTensorSelector i).elect+1) [((biasTensorSelector i).result,.pred true)] ∧
      Execution.isShfl e = false := by
  let site := biasTensorSelector i
  have hc : kernel.code[s.pc]? = some ⟨none, selectorElect site⟩ :=
    hs.1.symm ▸ (show kernel.code[site.elect]? = _ from selectorElectCode i)
  obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source hStep
  obtain rfl := Option.some.inj (hc.symm.trans hCode)
  have he' : Fires s.pc (eventTmpl Assumptions.all l g s (.warp ⟨.elect,none,
      [some site.destination,some site.result],[],some (.imm (-1))⟩)) e (some u) := hFire
  obtain ⟨_,inst',leader,hEvent,hState⟩ := fires_elect he'
  have hFull : e = ⟨s.pc,.elect (2^32-1) inst' leader⟩ := by
    rcases fires_elect_mask (bits := BitVec.ofNat 64 (2^32-1)) rfl he' with
      ⟨_,_,hEq⟩ | ⟨_,hEq⟩
    · obtain ⟨_,rfl,rfl⟩ := Kind.elect.inj (congrArg Event.kind (hEvent.symm.trans hEq))
      exact hEq
    · cases congrArg Event.kind (hEvent.symm.trans hEq)
  have hThread := event_thread_lt hX hTrace
  have hSame : SameWarp l g g := ⟨⟨hThread,hThread,rfl⟩,rfl⟩
  have hActual : X.Elect (g,j) s.pc (2^32-1) inst' leader :=
    hTrace.trans (congrArg some hFull)
  have hLeader := hX.elect.deterministic hKnown hActual hSame
  have hResult : (laneOf l g == leader) = true := by simp [hLeader]
  refine ⟨?_,by rw [hFull]; rfl⟩
  rw [hState]
  exact ⟨congrArg (·+1) hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,
    by simp [site,setReg,next,hResult],trivial⟩

private theorem selectedEventHead {l : Launch} {X : Execution} {g index : Nat}
    {s : TState} {ending : Option TState}
    {op : Op} (hc : kernel.code[s.pc]? = some ⟨none,op⟩) (hLocal : op.isLocal = false)
    (hClean : s.fault = none)
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {mark : Event} (he : X.get (g,j) = some mark) (hIndex : index ≤ j) :
    ∃ e o, X.get (g,index) = some e ∧ EStep kernel Assumptions.all l g s e o ∧
      (∀ u, o = some u → Run kernel Assumptions.all l g u ((X.tr g).drop (index+1)) ending) ∧
      (o = none → j = index) := by
  have hLen : index < (X.tr g).length := lt_of_le_of_lt hIndex (len_of_get he)
  let e := (X.tr g)[index]
  have hGet : X.get (g,index) = some e := List.getElem?_eq_getElem hLen
  have hFront : (X.tr g).drop index = e :: (X.tr g).drop (index+1) :=
    List.drop_eq_getElem_cons hLen
  have hStops : Stops kernel Assumptions.all l g s :=
    ⟨_,out_event hClean hc rfl hLocal⟩
  rw [hFront] at hRun
  generalize hTailEq : (X.tr g).drop (index+1) = tail at hRun
  cases hRun with
  | step hLocal hEvent hRest =>
    have hSame := stop_unique hLocal .refl (stops_of_estep hEvent) hStops
    subst s
    refine ⟨e,_,hGet,hEvent,?_ ,by simp⟩
    intro u hu
    exact Option.some.inj hu ▸ hRest
  | last hLocal hEvent =>
    have hSame := stop_unique hLocal .refl (stops_of_estep hEvent) hStops
    subst s
    refine ⟨e,none,hGet,hEvent,by simp,fun _ => ?_⟩
    by_contra hNe
    apply (traceAfterObservedEvent he (by omega) : (X.tr g).drop (index+1) ≠ [])
    exact hTailEq

/-- The known tensor issuer follows the selected lane through any actual later
selection instruction of its warp. -/
theorem biasSelectedElectionRun {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (i : Fin 10)
    {g k index pc inst : Nat} {s : TState} {ending : Option TState}
    (hKnown : X.Elect (g,k) pc (2^32-1) inst (laneOf l g))
    (hs : At s (biasTensorSelector i).elect [])
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {mark : Event} (he : X.get (g,j) = some mark) (hBefore : index ≤ j)
    (hLater : (biasTensorSelector i).elect < mark.pc) :
    ∃ u, At u ((biasTensorSelector i).branch+1) [] ∧ index+1 ≤ j ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index+1)) ending ∧
      ((X.tr g).take (index+1)).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl := by
  let site := biasTensorSelector i
  have hc : kernel.code[s.pc]? = some ⟨none,selectorElect site⟩ :=
    hs.1.symm ▸ (show kernel.code[site.elect]? = _ from selectorElectCode i)
  obtain ⟨e,o,hGet,hStep,hAfter,hEnd⟩ :=
    selectedEventHead hc rfl hs.2.2.2.1 hRun he hBefore
  have hsPc : s.pc = site.elect := hs.1
  have hNext : index+1 ≤ j := by
    by_contra! hLast
    have hi : j = index := by omega
    rw [hi,hGet] at he
    obtain rfl := Option.some.inj he
    rw [estep_source_pc hStep,hsPc] at hLater
    exact Nat.lt_irrefl _ hLater
  cases o with
  | none =>
    have heq := hEnd rfl
    omega
  | some a =>
    obtain ⟨ha,hNonShuffle⟩ := biasSelectedElectionFrame hX i hKnown hGet hs hStep
    obtain ⟨u,hLocal,hU⟩ := biasSelectedTensorGate i ha
    have hTail := (hAfter a rfl).after_local_nonempty hLocal (traceAfterObservedEvent he hNext)
    refine ⟨u,hU,hNext,hTail,?_⟩
    have hLen := len_of_get hGet
    have hElt : (X.tr g)[index] = e :=
      Option.some.inj ((List.getElem?_eq_getElem hLen).symm.trans hGet)
    rw [List.take_add,List.drop_eq_getElem_cons hLen,hElt]
    simp [hNonShuffle]

/-- The four block stages of the recurring Bias corridor have one selector per half. -/
def warmBiasTensorSelector (stage half : Fin 2) : Fin 10 := ⟨4+2*stage.val+half.val,by
  have := stage.isLt
  have := half.isLt
  omega⟩

section
variable {l : Launch} {m : Mem0} {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    (stage half : Fin 2) {g k index pc inst : Nat} {s : TState} {ending : Option TState}
    (hKnown : X.Elect (g,k) pc (2^32-1) inst (laneOf l g)) (hs : At s 917 [(123,.pred false)])
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
include hX stage half hKnown hs hRun

set_option maxRecDepth 10000 in
/-- One full-mask elected lane issues the selected warm half during a reached traversal. -/
theorem warmSelectedBiasIssueBeforeTensor {j address targetPc : Nat} {spec : TensorCopy.Spec}
    (he : X.get (g,j) = some ⟨targetPc,.tensorIssue address spec⟩) (hBefore : index ≤ j)
    (hLater : (biasTensorSelector (warmBiasTensorSelector stage half)).issue ≤ targetPc) :
    ∃ issue ≤ j, ∃ a box,
      X.get (g,issue) = some
        ⟨(biasTensorSelector (warmBiasTensorSelector stage half)).issue,.tensorIssue a box⟩ ∧
      ((X.tr g).take issue).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl+32 := by
  let selector := warmBiasTensorSelector stage half
  let site := biasTensorSelector selector
  let event : Event := ⟨targetPc,.tensorIssue address spec⟩
  have hTarget : site.issue ≤ event.pc := hLater
  have hSafe : ∀ f, event.kind ≠ .ub f := by rintro _ ⟨⟩
  have hRange : 1144 ≤ site.elect ∧ site.elect < site.branch ∧ site.branch < site.issue ∧
      site.issue < 1348 := by fin_cases stage <;> fin_cases half <;> decide
  have hRoleCode (bound : Nat) : ((kernel.code.drop 917).take (1143-917)).all
      (fun ins => loaderPipelineCutOp 917 1143 bound [123] ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hRoleRank : (((kernel.code.drop 917).take (1143-917)).zipIdx 917).all
      (fun (ins,pc) => LoaderRankedInstr 1143 pc ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨r,pre,_,_,hr,hRoleRun,hrRank,hrBefore⟩ :=
    prefixRankedShuffleCut (start := 917) (stop := 1143) (F := [(123,.pred false)])
      (by decide) hRoleCode hRoleRank hs hRun he hBefore
      (.inl (show 1143 ≤ event.pc by omega)) hSafe
  have hR : r.pc = 1143 := hr.1
  have hc : kernel.code[r.pc]? = some ⟨some (123,false), .bra 1203 false⟩ :=
    hR.symm ▸ Flow.code_1143
  have hReg : r.regs 123 = some (.pred false) := hr.2.2.2.2.1
  have hTau : Tau kernel Assumptions.all l g r (skip r) := by
    unfold Tau
    rw [loaderOutCore (by omega) (by omega)]
    simp [out,hr.2.2.2.1,hc,guardHolds,readReg,hReg,bind,Except.bind,pure,Except.pure]
  have hAt : At (skip r) 1144 [] :=
    ⟨by simp [skip,hR],rfl,rfl,hr.2.2.2.1,trivial⟩
  have hAfter := hRoleRun.after_local_nonempty (.single hTau)
    (traceAfterObservedEvent he hrBefore)
  have hSelector (bound : Nat) : ((kernel.code.drop 1144).take (site.elect-1144)).all
      (fun ins => loaderPipelineCutOp 1144 site.elect bound [] ins.op) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hSelectorQuiet : ((kernel.code.drop 1144).take (site.elect-1144)).all
      (fun ins => !ins.op.isShfl) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hElect : ∃ ins, kernel.code[site.elect]? = some ins ∧ loaderVector ins.op = false :=
    ⟨_,selectorElectCode selector,rfl⟩
  obtain ⟨t,front,_,_,ht,htRun,htRank,htBefore⟩ := prefixQuietCut (F := []) (by omega)
    hSelector hSelectorQuiet hElect hAt hAfter he hrBefore
      (show site.elect ≤ event.pc by omega) hSafe
  obtain ⟨u,hu,huBefore,huRun,huRank⟩ := biasSelectedElectionRun hX selector hKnown ht htRun
    he htBefore (show site.elect < event.pc by omega)
  have hPrepare (bound : Nat) :
      ((kernel.code.drop (site.branch+1)).take (site.issue-(site.branch+1))).all
        (fun ins => loaderPipelineCutOp (site.branch+1) site.issue bound [] ins.op) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hPrepareQuiet :
      ((kernel.code.drop (site.branch+1)).take (site.issue-(site.branch+1))).all
        (fun ins => !ins.op.isShfl) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  let boxSite := inputSite site.input
  let op := Op.cpTensor false false 2535 boxSite.sharedOffset (.reg boxSite.mapReg)
    [.reg boxSite.colReg,.reg boxSite.rowReg,.reg 7169] boxSite.barrierReg boxSite.barrierOffset
    none .tile (some (.reg boxSite.policyReg))
  have hCode : kernel.code[site.issue]? = some ⟨none,op⟩ := inputSiteCode site.input
  obtain ⟨v,passed,_,_,hv,hvRun,hvRank,hvBefore⟩ := prefixQuietCut (F := []) (by omega)
    hPrepare hPrepareQuiet ⟨_,hCode,rfl⟩ hu huRun he huBefore hTarget
    hSafe
  let pos := index+pre.length+front.length+1+passed.length
  obtain ⟨actual,q,hGet,hStep,_,hLast⟩ := selectedEventHead (hv.1.symm ▸ hCode) rfl
    hv.2.2.2.1 hvRun he hvBefore
  have hPc : actual.pc = site.issue := (estep_source_pc hStep).trans hv.1
  have hCount : loaderShuffleTail 1143 917 = 32 := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hRank : ((X.tr g).take pos).countP Execution.isShfl =
      ((X.tr g).take index).countP Execution.isShfl+32 := by
    dsimp only [pos]
    rw [hvRank,huRank,htRank,hrRank,hCount]
  cases q with
  | none =>
    have hEnd : j = pos := hLast rfl
    have he' : X.get (g,pos) = some event := hEnd ▸ he
    have hPcEq := congrArg Event.pc (Option.some.inj (he'.symm.trans hGet))
    change targetPc = actual.pc at hPcEq
    have h := hPcEq.trans hPc
    exact ⟨pos,hvBefore,address,spec,h ▸ he',hRank⟩
  | some w =>
    obtain ⟨ins,hIns,_,hf⟩ := estep_event_source hStep
    have hD : kernel.code[v.pc]? = some ⟨none,op⟩ := hv.1.symm ▸ hCode
    obtain rfl := Option.some.inj (hD.symm.trans hIns)
    have hf' : Fires v.pc (eventTmpl Assumptions.all l g v op) actual (some w) := hf
    obtain ⟨a,spec',hActual,_,_⟩ := fires_cpTensor_issue hf'
    rw [hv.1] at hActual
    exact ⟨pos,hvBefore,a,spec',hGet.trans (congrArg some hActual),hRank⟩

/-- One full-mask elected lane issues the selected warm half during a reached traversal. -/
theorem warmSelectedBiasIssue {j address : Nat} {spec : TensorCopy.Spec}
    (he : X.get (g,j) = some
      ⟨(biasTensorSelector (warmBiasTensorSelector stage half)).issue,.tensorIssue address spec⟩)
    (hBefore : index ≤ j) :
    ∃ issue ≤ j, ∃ a box,
      X.get (g,issue) = some
        ⟨(biasTensorSelector (warmBiasTensorSelector stage half)).issue,.tensorIssue a box⟩ ∧
      ((X.tr g).take issue).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl+32 := by
  exact warmSelectedBiasIssueBeforeTensor hX stage half hKnown hs hRun he hBefore le_rfl
end

private theorem beforeTensorSelectionStep {l : Launch} {g : Nat} {s u : TState}
    {ev : Option Event} (i : Fin 10) (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hShape : RingShape s) (hBefore : BeforeTensorSelection i l g s)
    (hStep : WStep kernel Assumptions.all l g s ev u)
    (hNo : ∀ e ∈ ev.toList, ¬ tensorSelected i l g e) : BeforeTensorSelection i l g u := by
  intro hIn
  let site := biasTensorSelector i
  by_cases hFrom : selectorInterior site s.pc
  · obtain ⟨exit, hPath, hExit⟩ := hBefore hFrom
    rcases Relation.ReflTransGen.cases_head hPath with rfl | ⟨first, hTau, hRest⟩
    · have hDst : s.pc ≤ site.issue := hFrom.2
      change s.pc = site.issue + 1 at hExit
      omega
    · rcases hStep with ⟨rfl, hNext⟩ | ⟨e, rfl, hE⟩
      · obtain rfl := tau_det hTau hNext
        exact ⟨exit,hRest,hExit⟩
      · exact (not_tau_of_stops (stops_of_estep hE) hTau).elim
  have hSrc := followsSelector i hLo hHi hShape hIn hFrom hStep
  have hc : kernel.code[site.elect]? = some ⟨none, selectorElect site⟩ := selectorElectCode i
  have hPc : s.pc = site.elect := hSrc
  rw [← hPc] at hc
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have hCore : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore hLo (by omega)]
    exact (tau_core_not_event hc rfl hCore).elim
  · obtain ⟨ins, hCode, _, hFire⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hc.symm.trans hCode)
    have he' : Fires s.pc
      (eventTmpl Assumptions.all l g s (.warp ⟨.elect, none,
        [some site.destination, some site.result], [], some (.imm (-1))⟩)) e (some u) := hFire
    have hAll := fires_elect_mask (bits := BitVec.ofNat 64 (2 ^ 32 - 1)) rfl he'
    obtain ⟨_, inst, leader, hEvent, hU⟩ := fires_elect he'
    have hFull : e = ⟨site.elect, .elect (2 ^ 32 - 1) inst leader⟩ := by
      rcases hAll with ⟨inst', leader', hEq⟩ | ⟨f, hEq⟩
      · obtain ⟨_, rfl, rfl⟩ := Kind.elect.inj (congrArg Event.kind (hEvent.symm.trans hEq))
        rwa [hSrc] at hEq
      · cases congrArg Event.kind (hEvent.symm.trans hEq)
    have hNot : laneOf l g ≠ leader := by
      intro h
      exact hNo e (by simp) ⟨inst, h ▸ hFull⟩
    have hUShape := loaderPipelineStepShape hLo hHi hShape (.inr ⟨_,rfl,he⟩)
    have hClean : s.fault = none := by
      cases hf : s.fault
      · rfl
      · obtain ⟨tmp, hout, hZ⟩ := he
        simp only [out, hf, Out.ev.injEq] at hout
        subst tmp
        cases hZ.2
    apply skipUnselectedTensor i (hShape := hUShape)
    · rw [hU]
      change s.pc + 1 = site.elect + 1
      rw [hSrc]
    · simpa [hU, next, setReg] using hClean
    · change u = next (setReg (setReg s site.destination
        (.bits 32 (BitVec.ofNat 64 leader))) site.result
        (.pred (laneOf l g == leader))) at hU
      have hFalse : (laneOf l g == leader) = false := by simp [hNot]
      change u.regs site.result = some (.pred false)
      simp only [hU, next, setReg, Function.update_self, hFalse]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A real Bias tensor uses the selected lane of the full-warp election for its half. -/
theorem biasTensorActualElection (i : Fin 10) {g j address : Nat} {spec : TensorCopy.Spec}
    (he : X.get (g,j) = some ⟨(biasTensorSelector i).issue, .tensorIssue address spec⟩) :
    ∃ k < j, ∃ inst, X.Elect (g,k) (biasTensorSelector i).elect (2^32-1) inst (laneOf l g) := by
  let site := biasTensorSelector i
  have hRange : 677 ≤ site.issue ∧ site.issue ≤ 1383 := by fin_cases i <;> decide
  obtain ⟨warp, s, vs, _, hJ, hAt, hWalk, hGet⟩ := biasInstructionWalk hp hX he hRange
  have hR : 174 ≤ site.elect ∧ site.elect < site.branch ∧
      site.branch < site.issue ∧ site.issue < 1901 := tensorSelectorRange i
  have hStart : BeforeTensorSelection i l g s := by
    intro h
    have hl : site.elect < s.pc := h.1
    rw [hAt.1] at hl
    omega
  obtain ⟨k, hk, e, hElect, inst, hEq⟩ := loaderEventPrecededBy warp hWalk
    (by rw [hAt.1]; decide) (ringShapeOfAt hAt) hAt.2.2.2.2 hStart hGet hR.2.2.2
    (fun {t} hb hPc => by
      change t.pc = site.issue at hPc
      have hIn : selectorInterior site t.pc := ⟨by omega, hPc.le⟩
      obtain ⟨u, hPath, hu⟩ := hb hIn
      rcases Relation.ReflTransGen.cases_head hPath with rfl | ⟨first, hTau, _⟩
      · change t.pc = site.issue + 1 at hu
        omega
      have hCore : Tau kernel [] l g t first := by
        unfold Tau at hTau ⊢
        rwa [← loaderOutCore (by omega) (by omega)]
      have hc := inputSiteCode site.input
      dsimp only at hc
      change t.pc = (inputSite site.input).pc at hPc
      rw [← hPc] at hc
      exact tau_core_not_event hc rfl hCore)
    (fun hlo hhi hShape _ hBefore hStep hNo =>
      beforeTensorSelectionStep i hlo hhi hShape hBefore hStep hNo)
  exact ⟨5+k, by omega, inst, by
    rw [hEq, List.getElem?_drop] at hElect
    exact hElect⟩

/-- The real destination identifies the Bias stage and half in the decoded transfer table. -/
theorem biasTensorSelectorOfSubbox {e : EvId} {stage half : Fin 2} {spec : TensorCopy.Spec}
    (he : Thread.Loader.BiasSubbox p l X e stage half spec) :
    ∃ i : Fin 10, (biasTensorSelector i).stage = stage ∧ (biasTensorSelector i).half = half ∧
      X.get e = some ⟨(biasTensorSelector i).issue, .tensorIssue p.biasMapAddress spec⟩ := by
  obtain ⟨pc, he'⟩ := he.1
  obtain ⟨input, hPc⟩ := actualInputIssuePc hX he'
  subst pc
  obtain ⟨_, _, _, hDst, _, _⟩ := actualInputBoxAt hp hX input he'
  have hAddr := congrArg Loc.addr (hDst.symm.trans he.2.2.1)
  change l.sharedBase + (inputSite input).sharedOffset =
    l.sharedBase + (166912 + 32768 * stage.val + 16384 * half.val) at hAddr
  have hOffset := Nat.add_left_cancel hAddr
  have hAll : ∀ (input : Fin 14) (stage half : Fin 2),
      (inputSite input).sharedOffset = 166912 + 32768 * stage.val + 16384 * half.val →
      ∃ i : Fin 10, (biasTensorSelector i).input = input ∧
        (biasTensorSelector i).stage = stage ∧ (biasTensorSelector i).half = half := by decide
  obtain ⟨i, hInput, hStage, hHalf⟩ := hAll input stage half hOffset
  exact ⟨i,hStage,hHalf,by simpa only [BiasTensorSelector.issue,hInput] using he'⟩

/-- All actual Bias tensor halves in the same CTA are issued by one physical elected lane. -/
theorem biasTensorSameIssuer {e f : EvId} {se sf he hf : Fin 2} {a b : TensorCopy.Spec}
    (hFirst : Thread.Loader.BiasSubbox p l X e se he a)
    (hSecond : Thread.Loader.BiasSubbox p l X f sf hf b) (hCta : e.1 / l.block = f.1 / l.block)
    : e.1 = f.1 := by
  obtain ⟨i, _, _, hi⟩ := biasTensorSelectorOfSubbox hp hX hFirst
  obtain ⟨j, _, _, hj⟩ := biasTensorSelectorOfSubbox hp hX hSecond
  have hGate (i : Fin 10) :
      677 ≤ (biasTensorSelector i).issue ∧ (biasTensorSelector i).issue < 780 ∨
      1144 ≤ (biasTensorSelector i).issue ∧ (biasTensorSelector i).issue < 1203 ∨
      1359 ≤ (biasTensorSelector i).issue ∧ (biasTensorSelector i).issue < 1384 := by
    fin_cases i <;> decide
  have hA := biasInstructionWarp hp hX (g := e.1) (j := e.2) hi (hGate i)
  have hB := biasInstructionWarp hp hX (g := f.1) (j := f.2) hj (hGate j)
  obtain ⟨k, _, _, hk⟩ := biasTensorActualElection hp hX i (g := e.1) (j := e.2) hi
  obtain ⟨q, _, _, hq⟩ := biasTensorActualElection hp hX j (g := f.1) (j := f.2) hj
  have hw : SameWarp l e.1 f.1 :=
    ⟨⟨event_thread_lt hX hi, event_thread_lt hX hj, hCta⟩, hA.trans hB.symm⟩
  exact selected_elect_thread_unique (e := (e.1,k)) (f := (f.1,q)) hX.elect hk hq hw rfl rfl

/-- The actual Bias tensor issue belongs to the selected loader warp. -/
theorem biasTensorActorWarp {e : EvId} {stage half : Fin 2} {spec : TensorCopy.Spec}
    (he : Thread.Loader.BiasSubbox p l X e stage half spec) :
    Prologue.warpIndex l e.1 = 14 := by
  obtain ⟨i, _, _, hi⟩ := biasTensorSelectorOfSubbox hp hX he
  have hGate :
      677 ≤ (biasTensorSelector i).issue ∧ (biasTensorSelector i).issue < 780 ∨
      1144 ≤ (biasTensorSelector i).issue ∧ (biasTensorSelector i).issue < 1203 ∨
      1359 ≤ (biasTensorSelector i).issue ∧ (biasTensorSelector i).issue < 1384 := by
    fin_cases i <;> decide
  exact biasInstructionWarp hp hX (g := e.1) (j := e.2) hi hGate
end PTX.Kernels.TmlFa4Fwd.Loader
