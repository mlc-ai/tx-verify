-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryCredits
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.LoaderInputDescriptors
import Kernels.TmlFa4Fwd.Proof.LoaderDrainPoll
import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
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
import Kernels.TmlFa4Fwd.Flow.Code.Part008
import Kernels.TmlFa4Fwd.Flow.Code.Part010
import Kernels.TmlFa4Fwd.Flow.Code.Part011
import Kernels.TmlFa4Fwd.Flow.Code.Part028
import Kernels.TmlFa4Fwd.Flow.Code.Part029
import Lemmas.Flow.ElectActor
import Lemmas.Flow.EventCont
public import Lemmas.Kernel.ExitChain
import Kernels.TmlFa4Fwd.Proof.TerminalSite

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

private def queryInputIndex (stage plane : Fin 2) : Fin 14 :=
  ⟨4 * stage.val + plane.val, by have := stage.isLt; have := plane.isLt; omega⟩

private def queryPc (stage plane : Fin 2) : Nat := (inputSite (queryInputIndex stage plane)).pc

private def queryElectPc (stage plane : Fin 2) : Nat := ![![687, 694], ![738, 746]] stage plane

private def queryElectDst (stage plane : Fin 2) : Nat := ![![1893, 1895], ![1911, 1914]] stage plane

private def queryPred (stage plane : Fin 2) : Nat := ![![142, 144], ![154, 156]] stage plane

private inductive QueryGate
  | tensor (stage plane : Fin 2)
  | expectation (stage : Fin 2)
  | drain

local macro "query_gate_cases " gate:ident " using " close:tactic : tactic =>
  `(tactic| cases hGate : $gate:term with
    | tensor stage plane =>
      subst $gate
      fin_cases stage <;> fin_cases plane <;> $close
    | expectation stage =>
      subst $gate
      fin_cases stage <;> $close
    | drain =>
      subst $gate
      skip <;> $close)

local macro "query_early_gate_cases " gate:ident " excluding " early:ident " using "
    close:tactic : tactic =>
  `(tactic| cases hGate : $gate:term with
    | tensor stage plane =>
      subst $gate
      fin_cases stage <;> fin_cases plane <;> $close
    | expectation stage =>
      subst $gate
      fin_cases stage <;> $close
    | drain =>
      subst $gate
      exact ($early:term rfl).elim)

private def QueryGate.target : QueryGate → Nat
  | .tensor stage plane => queryPc stage plane
  | .expectation stage => ![686, 737] stage
  | .drain => 1900

private def QueryGate.electPc : QueryGate → Nat
  | .tensor stage plane => queryElectPc stage plane
  | .expectation stage => ![682, 733] stage
  | .drain => 1896

private def QueryGate.electDst : QueryGate → Nat
  | .tensor stage plane => queryElectDst stage plane
  | .expectation stage => ![1891, 1909] stage
  | .drain => 2306

private def QueryGate.pred : QueryGate → Nat
  | .tensor stage plane => queryPred stage plane
  | .expectation stage => ![140, 152] stage
  | .drain => 261

private def QueryGate.electOp (gate : QueryGate) : Op := .warp {
  kind := .elect
  dsts := [some gate.electDst, some gate.pred]
  srcs := []
  mask := some (.imm (-1)) }

private theorem QueryGate.electCode (gate : QueryGate) :
    kernel.code[gate.electPc]? = some ⟨none, gate.electOp⟩ := by
  cases gate with
  | tensor stage plane =>
    fin_cases stage <;> fin_cases plane
    · exact Flow.code_687
    · exact Flow.code_694
    · exact Flow.code_738
    · exact Flow.code_746
  | expectation stage =>
    fin_cases stage
    · exact Flow.code_682
    · exact Flow.code_733
  | drain => exact Flow.code_1896

private theorem QueryGate.negationCode (gate : QueryGate) :
    ∃ ins, kernel.code[gate.electPc + 1]? = some ins ∧ ins.op.isLocal = true := by
  cases gate with
  | tensor stage plane =>
    fin_cases stage <;> fin_cases plane
    · exact ⟨_, Flow.code_688, rfl⟩
    · exact ⟨_, Flow.code_695, rfl⟩
    · exact ⟨_, Flow.code_739, rfl⟩
    · exact ⟨_, Flow.code_747, rfl⟩
  | expectation stage =>
    fin_cases stage
    · exact ⟨_, Flow.code_683, rfl⟩
    · exact ⟨_, Flow.code_734, rfl⟩
  | drain => exact ⟨_, Flow.code_1897, rfl⟩

private theorem queryIssueSite {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {stage plane : Fin 2} {s : TensorCopy.Spec}
    (h : QuerySubbox p l X i stage plane s) :
    X.get i = some ⟨queryPc stage plane, .tensorIssue p.qMapAddress s⟩ := by
  obtain ⟨pos, he⟩ := h.1
  obtain ⟨j, rfl⟩ := actualInputIssuePc hX he
  have hDst := (actualInputBoxAt hp hX j he).2.2.2.1
  have hOfs := congrArg Loc.addr (hDst.symm.trans h.2.2.1)
  change l.sharedBase + (inputSite j).sharedOffset = Mma.qStart l stage + 16384 * plane.val at hOfs
  simp only [Mma.qStart, Nat.add_assoc, Nat.add_left_cancel_iff] at hOfs
  have hJ : j = queryInputIndex stage plane := by
    fin_cases stage <;> fin_cases plane <;> fin_cases j <;>
      first | rfl | simp [inputSite] at hOfs
  subst j
  exact he

private def dispatchFrame (l : Launch) (warp : Fin 2) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]

private theorem loaderWalkToEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {mark : Event}
    (he : X.get (g,j) = some mark) (hPc : 174 ≤ mark.pc ∧ mark.pc < 1901)
    (hHint : mark.pc ∉ registerHintSites) :
    ∃ (start : TState) (visits : List Visit) (warp : Fin 2),
      (14 + warp.val = warpIndex l g) ∧ start.pc = 174 ∧ RingShape start ∧
      Holds start.regs (dispatchFrame l warp) ∧ 5 ≤ j ∧
      Walk kernel Assumptions.all l g start ((X.tr g).drop 5) visits := by
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hHint
  change roleBodyPc (warpIndex l g) (mark.pc) at hRole
  have hWarp : 14 ≤ warpIndex l g := by
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hEq : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hWarp
  have hg := event_thread_lt hX he
  obtain ⟨start, _, hIndex, hStart, hRun⟩ := nonzeroCommonPrefixOfLateEvent hp hX hg
    (Nat.lt_of_lt_of_le (by decide : 0 < 14) hWarp) he
      (by omega)
  obtain ⟨vs, hWalk⟩ := Mma.walkFromRun hRun
  exact ⟨start, vs, warp, hEq, hStart.1, ringShapeOfAt hStart,
    ⟨hStart.2.2.2.2.2.1, hEq.symm ▸ hStart.2.2.2.2.1, trivial⟩, hIndex, hWalk⟩

private theorem floorAfterQuery (stage plane : Fin 2) (branch : Nat) :
    ((kernel.code.drop (queryPc stage plane + 1)).take (1901 - (queryPc stage plane + 1))).all
      (fun ins => loaderPipelineCutOp (queryPc stage plane + 1) 1901 branch [2535, 1062] ins.op) =
      true := by
  fin_cases stage <;> fin_cases plane <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem goesThroughLoaderCut {l : Launch} {g lo cut target : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (warp : Fin 2)
    {e : Event} {j : Nat} {F : List (Nat × Value)}
    (hFloor : 174 ≤ lo) (hCut : cut ≤ target) (hPc : e.pc = target)
    (hTarget : target < 1901)
    (hAfter : ∀ bound, ((kernel.code.drop (target+1)).take (1901-(target+1))).all
      (fun ins => loaderPipelineCutOp (target+1) 1901 bound [2535, 1062] ins.op) = true)
    (hReturns : ¬ Ends e) (hRegs : ∀ r ∈ [2535, 1062], r ∈ F.map Prod.fst)
    (hAudit : ((kernel.code.drop lo).take (cut - lo)).all
      (fun ins => loaderPipelineCutOp lo cut (target) (F.map Prod.fst) ins.op) = true)
    (hw : Walk kernel Assumptions.all l g s es vs) (hBound : lo ≤ s.pc ∧ s.pc ≤ cut)
    (hShape : RingShape s) (hFrame : Holds s.regs F) (hRoot : Holds s.regs (dispatchFrame l warp))
    (he : es[j]? = some e) :
    ∃ t pre tail visits k, es = pre ++ tail ∧ j = pre.length + k ∧
      t.pc = cut ∧ RingShape t ∧ Holds t.regs F ∧ Holds t.regs (dispatchFrame l warp) ∧
      Walk kernel Assumptions.all l g t tail visits ∧ tail[k]? = some e ∧
      ∀ v ∈ pre, v.pc < cut := by
  have hLimit : cut ≤ 1901 := by omega
  have hRootAudit : ((kernel.code.drop lo).take (cut - lo)).all
      (fun ins => loaderPipelineCutOp lo cut (target) [2535, 1062] ins.op) = true := by
    apply List.all_eq_true.mpr
    intro ins hins
    have h := List.all_eq_true.mp hAudit ins hins
    simp only [loaderPipelineCutOp, Bool.and_eq_true] at h ⊢
    exact ⟨List.all_eq_true.mpr (fun r hr => List.all_eq_true.mp h.1 r (hRegs r hr)), h.2⟩
  have advance {t u : TState} {ev : Option Event} {tail : List Event} {rest : List Visit}
      (hHere : lo ≤ t.pc ∧ t.pc < cut) (ht : RingShape t)
      (hF : Holds t.regs F) (hR : Holds t.regs (dispatchFrame l warp))
      (hStep : WStep kernel Assumptions.all l g t ev u)
      (hTail : Walk kernel Assumptions.all l g u tail rest) (hSeen : e ∈ tail) :
      (lo ≤ u.pc ∧ u.pc ≤ cut) ∧ RingShape u ∧ Holds u.regs F ∧
        Holds u.regs (dispatchFrame l warp) := by
    obtain ⟨hLow, hHigh, hU, hNew⟩ :=
      pipelineCutStep hFloor hLimit hHere hAudit hStep ht hF
    have hRoots : Holds u.regs (dispatchFrame l warp) :=
      (pipelineCutStep hFloor hLimit hHere hRootAudit hStep ht hR).2.2.2
    refine ⟨⟨hLow, hHigh.resolve_right ?_⟩, hU, hNew, hRoots⟩
    intro hEscape
    have hAll : ((kernel.code.drop 174).take (1901 - 174)).all
        (fun ins => loaderPipelineCutOp 174 1901 u.pc [2535, 1062] ins.op) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hNo : target + 1 ≤ u.pc ∧ u.pc ≤ 1901 := by
      have hFull : 174 ≤ t.pc ∧ t.pc < 1901 := ⟨hFloor.trans hHere.1, by omega⟩
      obtain ⟨_, hu, _, _⟩ := pipelineCutStep (F := dispatchFrame l warp)
        (by decide : 174 ≤ 174) (by decide : 1901 ≤ 1901) hFull hAll hStep ht hR
      exact ⟨by omega, hu.resolve_right (Nat.lt_irrefl _)⟩
    have hLow' : 174 ≤ target + 1 := by omega
    have hImpossible := (loaderWalkEventRange warp hLow' hNo hU hRoots
      hAfter hTail e hSeen).1
    omega
  induction hw generalizing j with
  | stop => simp at he
  | @tau t u es vs ht hw ih =>
    by_cases hHere : t.pc = cut
    · exact ⟨t, [], es, _, j, rfl, by simp, hHere, hShape, hFrame, hRoot, .tau ht hw, he, by simp⟩
    obtain ⟨hU, hs, hF, hR⟩ := advance ⟨hBound.1, by omega⟩ hShape hFrame hRoot
      (.inl ⟨rfl, ht⟩) hw (List.mem_of_getElem? he)
    exact ih hU hs hF hR he
  | @ev t u a es vs hStep hw ih =>
    by_cases hHere : t.pc = cut
    · exact ⟨t, [], a :: es, _, j, rfl, by simp, hHere, hShape, hFrame, hRoot,
        .ev hStep hw, he, by simp⟩
    cases j with
    | zero =>
      have hA : a = e := by simpa using Option.some.inj he
      have hp := estep_source_pc hStep
      rw [hA, hPc] at hp
      omega
    | succ j =>
      have hGet : es[j]? = some e := he
      obtain ⟨hU, hs, hF, hR⟩ := advance ⟨hBound.1, by omega⟩ hShape hFrame hRoot
        (.inr ⟨a, rfl, hStep⟩) hw (List.mem_of_getElem? hGet)
      obtain ⟨t, pre, tail, rest, k, hEs, hJ, hP, hS, hF, hR, hW, hGet, hBefore⟩ :=
        ih hU hs hF hR hGet
      refine ⟨t, a :: pre, tail, rest, k, by rw [hEs]; rfl, by simp [hJ, Nat.add_assoc,
        Nat.add_comm k 1], hP, hS, hF, hR, hW, hGet, ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [estep_source_pc hStep]; omega
      · exact hBefore v hv
  | @last t a hStep =>
    have hj : j = 0 := by have := (List.getElem?_eq_some_iff.mp he).1; simp at this; omega
    subst j
    have hA : a = e := Option.some.inj he
    obtain ⟨_, _, hFire⟩ := hStep
    exact (hReturns (hA ▸ fires_none_ends hFire)).elim

private theorem walkAfterExactTau {l : Launch} {g : Nat} {s t : TState} {es : List Event}
    {vs : List Visit} (hWalk : Walk kernel Assumptions.all l g s es vs) (hNonempty : es ≠ [])
    (hTau : Tau kernel Assumptions.all l g s t) :
    ∃ visits, Walk kernel Assumptions.all l g t es visits := by
  cases hWalk with
  | stop => exact (hNonempty rfl).elim
  | tau hActual hRest => exact ⟨_, tau_det hActual hTau ▸ hRest⟩
  | ev hActual _ => exact (not_tau_of_stops (stops_of_estep hActual) hTau).elim
  | last hActual => exact (not_tau_of_stops (stops_of_estep hActual) hTau).elim

private theorem roleTest {l : Launch} {g : Nat} (warp : Fin 2) :
    Seg kernel Assumptions.all l g 1 538 (dispatchFrame l warp) 539
      ((123, .pred (warp.val != 0)) :: dispatchFrame l warp) := by
  have hCore : Seg kernel [] l g 1 538 (dispatchFrame l warp) 539
      ((123, .pred (warp.val != 0)) :: dispatchFrame l warp) := by
    intro s hs
    fin_cases warp <;> (simp only [dispatchFrame] at hs ⊢; seg_fp hs using rfl)
  intro s hs
  obtain ⟨u, hu, hAt⟩ := hCore s hs
  exact ⟨u, (loaderLinear (regs := []) (by decide) (by decide) hs.1 (by simp) rfl hu).1, hAt⟩

private theorem roleGate {l : Launch} {g : Nat} {t : TState} (warp : Fin 2)
    (h : At t 676 ((123, .pred (warp.val != 0)) :: dispatchFrame l warp)) :
    Tau kernel Assumptions.all l g t (if warp.val = 0 then next t else { t with pc := 780 }) := by
  unfold Tau
  rw [loaderOutCore (by have := h.1; omega) (by have := h.1; omega)]
  fin_cases warp <;>
    simp [out, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, Flow.code_676, guardHolds,
      readReg, skip, next, bind, Except.bind, pure, Except.pure, execLocalA_nil, execLocal,
      execBranch, Op.isLocal, Op.rule]

private theorem gateNegation {l : Launch} {g : Nat} (warp : Fin 2) (gate : QueryGate)
    (flag negated : Bool) (hNegated : (!flag) = negated) :
    Seg kernel Assumptions.all l g 1 (gate.electPc + 1)
      ((gate.pred, .pred flag) :: dispatchFrame l warp) (gate.electPc + 2)
      ((gate.pred + 1, .pred negated) :: dispatchFrame l warp) := by
  have hCore : Seg kernel [] l g 1 (gate.electPc + 1)
      ((gate.pred, .pred flag) :: dispatchFrame l warp) (gate.electPc + 2)
      ((gate.pred + 1, .pred negated) :: dispatchFrame l warp) := by
    intro s hs
    cases gate with
    | tensor stage plane =>
      fin_cases stage <;> fin_cases plane <;>
        (simp only [QueryGate.electPc, QueryGate.pred, queryElectPc, queryPred, dispatchFrame]
          at hs ⊢; seg_fp hs using rw [← hNegated])
    | expectation stage =>
      fin_cases stage <;>
        (simp only [QueryGate.electPc, QueryGate.pred, dispatchFrame] at hs ⊢
         seg_fp hs using rw [← hNegated])
    | drain =>
      simp only [QueryGate.electPc, QueryGate.pred, dispatchFrame] at hs ⊢
      seg_fp hs using rw [← hNegated]
  intro s hs
  obtain ⟨u, hu, hAt⟩ := hCore s hs
  have hLower : 174 ≤ gate.electPc + 1 := by
    query_gate_cases gate using decide
  have hUpper : gate.electPc + 1 + 1 ≤ 1906 := by
    query_gate_cases gate using decide
  exact ⟨u, (loaderLinear (regs := []) hLower hUpper hs.1 (by simp) rfl hu).1, hAt⟩

private theorem electionGate {l : Launch} {g : Nat} {s : TState} (warp : Fin 2)
    (gate : QueryGate) (flag : Bool)
    (h : At s (gate.electPc + 2)
      ((gate.pred + 1, .pred (!flag)) :: dispatchFrame l warp)) :
    Tau kernel Assumptions.all l g s
      (if flag then next s else { s with pc := gate.target + 1 }) := by
  have hLo : 174 ≤ s.pc := by rw [h.1]; query_gate_cases gate using decide
  have hHi : s.pc < 1901 := by rw [h.1]; query_gate_cases gate using decide
  unfold Tau
  rw [loaderOutCore hLo (hHi.trans (by decide : 1901 < 1906))]
  have hPred : s.regs (gate.pred + 1) = some (.pred (!flag)) := h.2.2.2.2.1
  query_gate_cases gate using (
    first
    | change s.regs 262 = _ at hPred
    | change s.regs 141 = _ at hPred
    | change s.regs 153 = _ at hPred
    | change s.regs 143 = _ at hPred
    | change s.regs 145 = _ at hPred
    | change s.regs 155 = _ at hPred
    | change s.regs 157 = _ at hPred
    cases flag <;>
      simp [out, h.1, h.2.1, h.2.2.1, h.2.2.2.1, hPred, QueryGate.electPc, QueryGate.target,
        queryElectPc, queryPc, queryInputIndex, inputSite, Flow.code_689, Flow.code_696,
        Flow.code_740, Flow.code_684, Flow.code_735, Flow.code_748, Flow.code_1898,
        guardHolds, readReg,
        skip, next, bind, Except.bind,
        pure, Except.pure, execLocalA_nil, execLocal, execBranch, Op.isLocal, Op.rule])

private theorem queryElectionContinues {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (warp : Fin 2) (gate : QueryGate)
    (hs : s.pc = gate.electPc) (hShape : RingShape s)
    (hRoot : Holds s.regs (dispatchFrame l warp))
    {mark : Event} (hMark : mark.pc = gate.target) (hContinue : ¬ Ends mark)
    (hw : Walk kernel Assumptions.all l g s es vs) (hSeen : mark ∈ es) :
    ∃ inst leader u tail visits,
      es = ⟨gate.electPc, .elect (2 ^ 32 - 1) inst leader⟩ :: tail ∧
      At u (gate.electPc + 1)
        ((gate.pred, .pred (laneOf l g == leader)) :: dispatchFrame l warp) ∧
      Walk kernel Assumptions.all l g u tail visits ∧ mark ∈ tail := by
  have hLo : 174 ≤ s.pc := by rw [hs]; query_gate_cases gate using decide
  have hHi : s.pc < 1901 := by rw [hs]; query_gate_cases gate using decide
  have hBefore : gate.electPc < gate.target := by
    query_gate_cases gate using decide
  cases hw with
  | stop => cases hSeen
  | @tau s t _ _ hTau _ =>
    have hCore : Tau kernel [] l g s t := by
      unfold Tau at hTau ⊢
      rwa [← loaderOutCore hLo (hHi.trans (by decide : 1901 < 1906))]
    exact (tau_core_not_event (hs.symm ▸ gate.electCode) rfl hCore).elim
  | @ev s u ev es vs hStep hRest =>
    have hEv : ev.pc = gate.electPc := (estep_source_pc hStep).trans hs
    have hNe : ev ≠ mark := by intro h; rw [h, hMark] at hEv; omega
    have hTail := (List.mem_cons.mp hSeen).resolve_left (Ne.symm hNe)
    have hFrameAudit : ((kernel.code.drop 174).take (1901 - 174)).all
        (fun i => loaderPipelineCutOp 174 1901 u.pc [2535, 1062] i.op) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hNew := (pipelineCutStep (F := dispatchFrame l warp) (by decide) (by decide)
      ⟨hLo, hHi⟩ hFrameAudit (.inr ⟨ev, rfl, hStep⟩) hShape hRoot).2.2
    obtain ⟨ins, hc, _, hf⟩ := estep_event_source hStep
    have result : ∃ inst leader,
        ev = ⟨gate.electPc, .elect (2 ^ 32 - 1) inst leader⟩ ∧
        u.pc = gate.electPc + 1 ∧
        u.regs (gate.pred) = some (.pred (laneOf l g == leader)) := by
      rw [hs, gate.electCode] at hc
      obtain rfl := Option.some.inj hc
      change Fires s.pc (eventTmpl Assumptions.all l g s (.warp ⟨.elect, none,
        [some (gate.electDst), some (gate.pred)], [],
        some (.imm (-1))⟩)) ev (some u) at hf
      obtain ⟨mk, inst, leader, he, hu⟩ := fires_elect hf
      rcases fires_elect_mask (bits := BitVec.ofNat 64 (2 ^ 32 - 1)) rfl hf with
        ⟨inst', leader', he'⟩ | ⟨fault, hFault⟩
      · rw [hs] at he'
        obtain ⟨rfl, rfl, rfl⟩ := Kind.elect.inj (congrArg Event.kind (he.symm.trans he'))
        exact ⟨inst, leader, he', by rw [hu, ← hs]; rfl,
          by rw [hu]; simp [next, setReg]⟩
      · cases (congrArg Event.kind (he.symm.trans hFault))
    obtain ⟨inst, leader, he, hPc, hPred⟩ := result
    exact ⟨inst, leader, u, es, vs, by rw [he],
      pipelineAtCut hPc hNew.1 ⟨hPred, hNew.2⟩
        (walkWithContinuingEventClean hRest hTail hContinue) (gate.negationCode),
      hRest, hTail⟩
  | @last t ev hStep =>
    obtain rfl := List.mem_singleton.mp hSeen
    obtain ⟨_, _, hFire⟩ := hStep
    exact (hContinue (fires_none_ends hFire)).elim

private theorem QueryGate.bounds (gate : QueryGate) :
    174 ≤ gate.target ∧ gate.target < 1901 := by
  cases gate with
  | tensor stage plane => fin_cases stage <;> fin_cases plane <;> decide
  | expectation stage => fin_cases stage <;> decide
  | drain => decide

private theorem QueryGate.floor (gate : QueryGate) (branch : Nat) :
    ((kernel.code.drop (gate.target + 1)).take (1901 - (gate.target + 1))).all
      (fun ins => loaderPipelineCutOp (gate.target + 1) 1901 branch [2535, 1062] ins.op) =
      true := by
  cases gate with
  | tensor stage plane => exact floorAfterQuery stage plane branch
  | expectation stage => fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  | drain => rfl

private theorem loaderQueryGateLeader {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (gate : QueryGate) (hEarlyGate : gate ≠ .drain) {g j : Nat} {mark : Event}
    (he : X.get (g,j) = some mark) (hPcMark : mark.pc = gate.target) (hCont : ¬ Ends mark) :
    warpIndex l g = 14 ∧ ∃ index inst,
      X.Elect (g, index) gate.electPc (2 ^ 32 - 1) inst (laneOf l g) := by
  obtain ⟨start, visits, warp, hWarp, hPc, hShape, hFrame, hIndex, hWalk⟩ :=
    loaderWalkToEvent hp hX he (hPcMark.symm ▸ gate.bounds) (by
      rw [hPcMark]
      cases gate with
      | tensor stage plane => fin_cases stage <;> fin_cases plane <;> decide
      | expectation stage => fin_cases stage <;> decide
      | drain => exact (hEarlyGate rfl).elim)
  let F := dispatchFrame l warp
  have roots : ∀ r ∈ [2535, 1062], r ∈ F.map Prod.fst := fun _ h => h
  have hGet : ((X.tr g).drop 5)[j - 5]? = some mark := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  have hEarly : ((kernel.code.drop 174).take (538 - 174)).all
      (fun i => loaderPipelineCutOp 174 538 (gate.target) (F.map Prod.fst) i.op) =
      true := by
    query_early_gate_cases gate excluding hEarlyGate using
      (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨t, first, rem, vs, k, hRem, _, ht, hT, hR, _, hRest, hSeen, _⟩ :=
    goesThroughLoaderCut warp (by decide)
      (by query_early_gate_cases gate excluding hEarlyGate using decide)
      hPcMark gate.bounds.2 gate.floor hCont roots
      hEarly hWalk (by rw [hPc]; decide) hShape hFrame hFrame hGet
  have hMem := List.mem_of_getElem? hSeen
  have hAt : At t 538 F := pipelineAtCut ht hT hR
    (walkWithContinuingEventClean hRest hMem hCont) ⟨_, Flow.code_538, rfl⟩
  obtain ⟨u, hu, hU⟩ := roleTest (g := g) warp t hAt
  have hTau : Tau kernel Assumptions.all l g t u := tauStep_iff.mp (by simpa [run] using hu)
  obtain ⟨_, hNext⟩ := walkAfterExactTau hRest (List.ne_nil_of_mem hMem) hTau
  let G := (123, .pred (warp.val != 0)) :: F
  have hR' : Holds u.regs F := hU.2.2.2.2.2
  have hGateAudit : ((kernel.code.drop 539).take (676 - 539)).all
      (fun i => loaderPipelineCutOp 539 676 (gate.target) (G.map Prod.fst) i.op) =
      true := by
    query_early_gate_cases gate excluding hEarlyGate using
      (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨roleState, middle, rest, vs, k, hSplit, _, hGate, hS, hF, hR, hWalkGate, hSeen, _⟩ :=
    goesThroughLoaderCut (F := G) warp (by decide)
      (by query_early_gate_cases gate excluding hEarlyGate using decide)
      hPcMark gate.bounds.2 gate.floor hCont
      (fun _ h => List.mem_cons_of_mem _ h)
      hGateAudit hNext (by rw [hU.1]; decide)
      (ringShapeOfAt hU) hU.2.2.2.2 hR' hSeen
  have hMem := List.mem_of_getElem? hSeen
  have hAtGate : At roleState 676 G := pipelineAtCut hGate hS hF
    (walkWithContinuingEventClean hWalkGate hMem hCont) ⟨_, Flow.code_676, rfl⟩
  obtain ⟨_, hPastGate⟩ := walkAfterExactTau hWalkGate (List.ne_nil_of_mem hMem)
    (roleGate (g := g) warp hAtGate)
  have hIsFirst : warp.val = 0 := by
    by_contra hw
    simp only [ite_eq_right hw] at hPastGate
    have hAt : At { roleState with pc := 780 } 780 F := ⟨rfl, hAtGate.2.1,
      hAtGate.2.2.1, hAtGate.2.2.2.1, hR⟩
    have hAfter (branch : Nat) : ((kernel.code.drop 780).take (1901 - 780)).all
        (fun i => loaderPipelineCutOp 780 1901 branch [2535, 1062] i.op) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hBad := (loaderWalkEventRange warp (lower := 780) (by decide)
      (show 780 ≤ 780 ∧ 780 ≤ 1901 by decide)
      (ringShapeOfAt hAt) hR hAfter hPastGate mark hMem).1
    rw [hPcMark] at hBad
    have hLow : gate.target ≤ 753 := by
      query_early_gate_cases gate excluding hEarlyGate using decide
    omega
  simp only [ite_eq_left hIsFirst] at hPastGate
  have hAtNext : At (next roleState) 677 F := (hAtGate.mono hR).next
  have hElectAudit : ((kernel.code.drop 677).take (gate.electPc - 677)).all
      (fun i => loaderPipelineCutOp 677 (gate.electPc) (gate.target)
        (F.map Prod.fst) i.op) = true := by
    query_early_gate_cases gate excluding hEarlyGate using
      (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨v, before, tail, vs, k, hTail, _, hv, hS, hF, _, hW, hFound, _⟩ :=
    goesThroughLoaderCut warp (by decide)
      (by query_early_gate_cases gate excluding hEarlyGate using decide)
      hPcMark gate.bounds.2 gate.floor hCont roots
      hElectAudit hPastGate (by
        rw [hAtNext.1]
        query_early_gate_cases gate excluding hEarlyGate using decide)
      (ringShapeOfAt hAtNext) hAtNext.2.2.2.2 hAtNext.2.2.2.2 hSeen
  obtain ⟨inst, leader, state, after, vs, hTrace, hState, hAfter, hFound⟩ :=
    queryElectionContinues warp gate hv hS hF hPcMark hCont hW (List.mem_of_getElem? hFound)
  let flag := laneOf l g == leader
  obtain ⟨branch, hStep, hBranch⟩ :=
    gateNegation (g := g) warp gate flag (!flag) rfl state hState
  have hTau : Tau kernel Assumptions.all l g state branch :=
    tauStep_iff.mp (by simpa [run] using hStep)
  obtain ⟨_, hWalkBranch⟩ := walkAfterExactTau hAfter (List.ne_nil_of_mem hFound) hTau
  obtain ⟨_, hWalkEnd⟩ := walkAfterExactTau hWalkBranch (List.ne_nil_of_mem hFound)
    (electionGate (g := g) warp gate flag hBranch)
  have hLead : laneOf l g = leader := by
    by_contra hNo
    have hFlag : flag = false := by simp [flag, hNo]
    simp only [hFlag, Bool.false_eq_true, ↓reduceIte] at hWalkEnd
    have hAt : At { branch with pc := gate.target + 1 } (gate.target + 1) F :=
      ⟨rfl, hBranch.2.1, hBranch.2.2.1, hBranch.2.2.2.1, hBranch.2.2.2.2.2⟩
    have hBounds : 174 ≤ gate.target + 1 ∧ gate.target + 1 ≤ 1901 := by
      query_early_gate_cases gate excluding hEarlyGate using decide
    have hBad := (loaderWalkEventRange warp hBounds.1 ⟨le_rfl, hBounds.2⟩
      (ringShapeOfAt hAt) hAt.2.2.2.2 gate.floor hWalkEnd mark hFound).1
    rw [hPcMark] at hBad
    omega
  let election : Event := ⟨gate.electPc, .elect (2 ^ 32 - 1) inst leader⟩
  have hElection : election ∈ (X.tr g).drop 5 := by
    rw [hRem, hSplit, hTail, hTrace]
    simp [election]
  obtain ⟨index, hi⟩ := List.getElem?_of_mem (List.mem_of_mem_drop hElection)
  have hRole : warpIndex l g = 14 := by omega
  refine ⟨hRole, index, inst, ?_⟩
  rw [hLead]
  exact hi

private theorem drainRoleTest {l : Launch} {g : Nat} (warp : Fin 2) :
    Seg kernel Assumptions.all l g 1 1862 (dispatchFrame l warp) 1863
      ((258, .pred (warp.val != 0)) :: dispatchFrame l warp) := by
  have hCore : Seg kernel [] l g 1 1862 (dispatchFrame l warp) 1863
      ((258, .pred (warp.val != 0)) :: dispatchFrame l warp) := by
    intro s hs
    fin_cases warp <;> (simp only [dispatchFrame] at hs ⊢; seg_fp hs using rfl)
  intro s hs
  obtain ⟨u, hu, hAt⟩ := hCore s hs
  exact ⟨u, (loaderLinear (regs := []) (by decide) (by decide) hs.1 (by simp) rfl hu).1, hAt⟩

private theorem drainRoleBranch {l : Launch} {g : Nat} {s : TState} (warp : Fin 2)
    (ht : At s 1891 ((258, .pred (warp.val != 0)) :: dispatchFrame l warp)) :
    Tau kernel Assumptions.all l g s (if warp.val = 0 then next s else { s with pc := 1901 }) := by
  unfold Tau
  rw [loaderOutCore (by have := ht.1; omega) (by have := ht.1; omega)]
  fin_cases warp <;>
    simp [out, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, Flow.code_1891, guardHolds,
      readReg, skip, next, bind, Except.bind, pure, Except.pure, execLocalA_nil, execLocal,
      execBranch, Op.isLocal, Op.rule]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem drainQueryGateLeader {g j : Nat} {mark : Event} (he : X.get (g,j) = some mark)
    (hPcMark : mark.pc = 1900) (hCont : ¬ Ends mark) :
    warpIndex l g = 14 ∧ ∃ index inst, X.Elect (g,index) 1896 (2 ^ 32 - 1) inst (laneOf l g) := by
  obtain ⟨start, visits, warp, hWarp, hPc, hShape, hFrame, hIndex, hWalk⟩ :=
    loaderWalkToEvent hp hX he (by rw [hPcMark]; decide) (by rw [hPcMark]; decide)
  let F := dispatchFrame l warp
  let G := (258, .pred (warp.val != 0)) :: F
  let gate := QueryGate.drain
  have roots : ∀ r ∈ [2535, 1062], r ∈ F.map Prod.fst := fun _ h => h
  have hGet : ((X.tr g).drop 5)[j - 5]? = some mark := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  have hEarly : ((kernel.code.drop 174).take (1862 - 174)).all
      (fun i => loaderPipelineCutOp 174 1862 1900 (F.map Prod.fst) i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨t, _, _, _, _, hRem, _, ht, hT, hR, _, hRest, hSeen, _⟩ :=
    goesThroughLoaderCut warp (by decide) (by decide : 1862 ≤ 1900) hPcMark
      gate.bounds.2 gate.floor hCont roots hEarly hWalk (by rw [hPc]; decide)
      hShape hFrame hFrame hGet
  have hMem := List.mem_of_getElem? hSeen
  have hAt : At t 1862 F := pipelineAtCut ht hT hR
    (walkWithContinuingEventClean hRest hMem hCont) ⟨_, Flow.code_1862, rfl⟩
  obtain ⟨u, hu, hU⟩ := drainRoleTest (g := g) warp t hAt
  have hTau : Tau kernel Assumptions.all l g t u := tauStep_iff.mp (by simpa [run] using hu)
  obtain ⟨_, hNext⟩ := walkAfterExactTau hRest (List.ne_nil_of_mem hMem) hTau
  have hGateAudit : ((kernel.code.drop 1863).take (1891 - 1863)).all
      (fun i => loaderPipelineCutOp 1863 1891 1900 (G.map Prod.fst) i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨roleState, _, _, _, _, hSplit, _, hPcRole, hS, hF, hR, hWalkGate, hSeen, _⟩ :=
    goesThroughLoaderCut (F := G) warp (by decide) (by decide : 1891 ≤ 1900) hPcMark
      gate.bounds.2 gate.floor hCont (fun _ h => List.mem_cons_of_mem _ h)
      hGateAudit hNext (by rw [hU.1]; decide) (ringShapeOfAt hU) hU.2.2.2.2
      hU.2.2.2.2.2 hSeen
  have hMem := List.mem_of_getElem? hSeen
  have hAtGate : At roleState 1891 G := pipelineAtCut hPcRole hS hF
    (walkWithContinuingEventClean hWalkGate hMem hCont) ⟨_, Flow.code_1891, rfl⟩
  obtain ⟨_, hPastGate⟩ := walkAfterExactTau hWalkGate (List.ne_nil_of_mem hMem)
    (drainRoleBranch (g := g) warp hAtGate)
  have hIsFirst : warp.val = 0 := by
    by_contra hw
    simp only [ite_eq_right hw] at hPastGate
    have hAt : At { roleState with pc := 1901 } 1901 F := ⟨rfl, hAtGate.2.1,
      hAtGate.2.2.1, hAtGate.2.2.2.1, hR⟩
    have hBad := (loaderWalkEventRange warp (lower := 1901) (by decide)
      (show 1901 ≤ 1901 ∧ 1901 ≤ 1901 by decide)
      (ringShapeOfAt hAt) hR (by intro; rfl) hPastGate mark hMem).1
    omega
  simp only [ite_eq_left hIsFirst] at hPastGate
  have hAtNext : At (next roleState) 1892 F := (hAtGate.mono hR).next
  have hElectAudit : ((kernel.code.drop 1892).take (1896 - 1892)).all
      (fun i => loaderPipelineCutOp 1892 1896 1900 (F.map Prod.fst) i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨v, _, _, _, _, hTail, _, hv, hS, hF, _, hW, hFound, _⟩ :=
    goesThroughLoaderCut warp (by decide) (by decide : 1896 ≤ 1900) hPcMark
      gate.bounds.2 gate.floor hCont roots hElectAudit hPastGate (by rw [hAtNext.1]; decide)
      (ringShapeOfAt hAtNext) hAtNext.2.2.2.2 hAtNext.2.2.2.2 hSeen
  obtain ⟨inst, leader, state, after, _, hTrace, hState, hAfter, hFound⟩ :=
    queryElectionContinues warp gate hv hS hF hPcMark hCont hW (List.mem_of_getElem? hFound)
  let flag := laneOf l g == leader
  obtain ⟨branch, hStep, hBranch⟩ :=
    gateNegation (g := g) warp gate flag (!flag) rfl state hState
  have hTau : Tau kernel Assumptions.all l g state branch :=
    tauStep_iff.mp (by simpa [run] using hStep)
  obtain ⟨_, hWalkBranch⟩ := walkAfterExactTau hAfter (List.ne_nil_of_mem hFound) hTau
  obtain ⟨_, hWalkEnd⟩ := walkAfterExactTau hWalkBranch (List.ne_nil_of_mem hFound)
    (electionGate (g := g) warp gate flag hBranch)
  have hLead : laneOf l g = leader := by
    by_contra hNo
    have hFlag : flag = false := by simp [flag, hNo]
    simp only [hFlag, Bool.false_eq_true, ↓reduceIte] at hWalkEnd
    have hAt : At { branch with pc := 1901 } 1901 F :=
      ⟨rfl, hBranch.2.1, hBranch.2.2.1, hBranch.2.2.2.1, hBranch.2.2.2.2.2⟩
    have hBad := (loaderWalkEventRange warp (lower := 1901) (by decide)
      (show 1901 ≤ 1901 ∧ 1901 ≤ 1901 by decide)
      (ringShapeOfAt hAt) hAt.2.2.2.2 (by intro; rfl) hWalkEnd mark hFound).1
    omega
  let election : Event := ⟨1896, .elect (2 ^ 32 - 1) inst leader⟩
  have hElection : election ∈ (X.tr g).drop 5 := by
    rw [hRem, hSplit, hTail, hTrace]
    simp [election, gate, QueryGate.electPc]
  obtain ⟨index, hi⟩ := List.getElem?_of_mem (List.mem_of_mem_drop hElection)
  have hRole : warpIndex l g = 14 := by omega
  refine ⟨hRole, index, inst, ?_⟩
  rw [hLead]
  exact hi

private theorem queryIssuerElected {g j : Nat} {stage plane : Fin 2} {s : TensorCopy.Spec}
    (he : X.get (g, j) = some ⟨queryPc stage plane, .tensorIssue p.qMapAddress s⟩) :
    warpIndex l g = 14 ∧ ∃ index inst,
      X.Elect (g, index) (queryElectPc stage plane) (2 ^ 32 - 1) inst (laneOf l g) :=
  loaderQueryGateLeader hp hX (.tensor stage plane) (by intro h; cases h) he rfl (by simp [Ends])

/-- Each query subbox requires an earlier full-mask election in the producer warp. -/
theorem querySubboxElection {issue : EvId} {stage plane : Fin 2} {spec : TensorCopy.Spec}
    (hBox : QuerySubbox p l X issue stage plane spec) :
    warpIndex l issue.1 = 14 ∧ ∃ index site inst,
      (if stage = 0 then 682 else 733) ≤ site ∧
      X.Elect (issue.1,index) site (2^32-1) inst (laneOf l issue.1) := by
  obtain ⟨g,j⟩ := issue
  obtain ⟨hWarp,k,inst,he⟩ := queryIssuerElected hp hX (queryIssueSite hp hX hBox)
  have hFloor : (if stage = 0 then 682 else 733) ≤ queryElectPc stage plane := by
    fin_cases stage <;> fin_cases plane <;> decide
  exact ⟨hWarp,k,queryElectPc stage plane,inst,hFloor,he⟩

omit hp hX in
private theorem QueryGate.noHint (gate : QueryGate) : gate.target ∉ registerHintSites := by
  query_gate_cases gate using decide

omit hp hX in
private theorem QueryGate.targetCode (gate : QueryGate) :
    ∃ op, kernel.code[gate.target]? = some ⟨none, op⟩ ∧ op.isLocal = false := by
  cases gate with
  | tensor stage plane => exact ⟨_, inputSiteCode (queryInputIndex stage plane), rfl⟩
  | expectation stage =>
    fin_cases stage
    · exact ⟨_, Flow.code_686, rfl⟩
    · exact ⟨_, Flow.code_737, rfl⟩
  | drain => exact ⟨_, Flow.code_1900, rfl⟩

private theorem loaderWalkAfterGateEvent (gate : QueryGate) {g j : Nat} {mark : Event}
    (he : X.get (g, j) = some mark) (hPcMark : mark.pc = gate.target) (hCont : ¬ Ends mark) :
    ∃ (s : TState) (warp : Fin 2) (visits : List Visit), 14 + warp.val = warpIndex l g ∧
      s.pc = gate.target+1 ∧ RingShape s ∧ Holds s.regs (dispatchFrame l warp) ∧
      Walk kernel Assumptions.all l g s ((X.tr g).drop (j+1)) visits := by
  obtain ⟨start, visits, warp, hWarp, hPc, hShape, hFrame, hIndex, hWalk⟩ :=
    loaderWalkToEvent hp hX he (hPcMark.symm ▸ gate.bounds) (hPcMark.symm ▸ gate.noHint)
  let F := dispatchFrame l warp
  have roots : ∀ r ∈ [2535, 1062], r ∈ F.map Prod.fst := fun _ h => h
  have hGet : ((X.tr g).drop 5)[j - 5]? = some mark := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  have hAudit : ((kernel.code.drop 174).take (gate.target - 174)).all
      (fun i => loaderPipelineCutOp 174 (gate.target) (gate.target)
        (F.map Prod.fst) i.op) = true := by
    query_gate_cases gate using (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨u, pre, tail, vs, n, hSplit, hEq, hu, hS, hF, _, hTail, hMark, hBelow⟩ :=
    goesThroughLoaderCut warp (by decide) le_rfl hPcMark gate.bounds.2 gate.floor hCont roots
      hAudit hWalk (by rw [hPc]; query_gate_cases gate using decide) hShape hFrame hFrame hGet
  have hBounds : 174 ≤ gate.target ∧ gate.target < 1901 := by
    query_gate_cases gate using decide
  cases hTail with
  | stop => simp at hMark
  | @tau v w es vs ht _ =>
    have hs : Tau kernel [] l g u w := by
      unfold Tau at ht ⊢
      rw [← loaderOutCore (hu.symm ▸ hBounds.1)
        ((hu.symm ▸ hBounds.2).trans (by decide : 1901 < 1906))]
      exact ht
    obtain ⟨op, hc, hl⟩ := gate.targetCode
    exact (tau_core_not_event (by rwa [hu]) hl hs).elim
  | last step =>
    have hIndex := (List.getElem?_eq_some_iff.mp hMark).1
    simp only [List.length_singleton] at hIndex
    have hn : n = 0 := by omega
    subst n
    obtain rfl := Option.some.inj hMark
    obtain ⟨_, _, hFire⟩ := step
    exact (hCont (fires_none_ends hFire)).elim
  | @ev v w first es vs hStep hRest =>
    obtain ⟨ins, hc, _, hFire⟩ := estep_event_source hStep
    rw [hu] at hc
    have hAfter : w.pc = gate.target + 1 := by
      cases gate with
      | tensor stage plane =>
        have hCode := inputSiteCode (queryInputIndex stage plane)
        change kernel.code[queryPc stage plane]? = _ at hCode
        change kernel.code[queryPc stage plane]? = some ins at hc
        rw [hCode] at hc
        obtain rfl := Option.some.inj hc
        obtain ⟨_, _, _, hNext, _⟩ := fires_cpTensor_issue hFire
        rw [hNext]
        exact congrArg (· + 1) hu
      | expectation stage =>
        fin_cases stage
        · change kernel.code[686]? = some ins at hc
          rw [Flow.code_686] at hc
          obtain rfl := Option.some.inj hc
          rw [(fires_arrive_state hFire).1]
          exact congrArg (· + 1) hu
        · change kernel.code[737]? = some ins at hc
          rw [Flow.code_737] at hc
          obtain rfl := Option.some.inj hc
          rw [(fires_arrive_state hFire).1]
          exact congrArg (· + 1) hu
      | drain =>
        change kernel.code[1900]? = some ins at hc
        rw [Flow.code_1900] at hc
        obtain rfl := Option.some.inj hc
        rw [(fires_arrive_state hFire).1]
        exact congrArg (· + 1) hu
    have hFrames : ((kernel.code.drop 174).take (1901 - 174)).all
        (fun ins => loaderPipelineCutOp 174 1901 w.pc [2535, 1062] ins.op) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hFrame' := (pipelineCutStep (F := F) (by decide) (by decide)
      (hu.symm ▸ hBounds) hFrames (.inr ⟨first, rfl, hStep⟩) hS hF).2.2.2
    have hShape' : RingShape w := loaderPipelineStepShape
      (hu.symm ▸ hBounds.1) (hu.symm ▸ hBounds.2) hS (.inr ⟨first, rfl, hStep⟩)
    have hBounds' : gate.target + 1 ≤ w.pc ∧ w.pc ≤ 1901 := by omega
    have hRange := loaderWalkEventRange warp (by omega) hBounds' hShape' hFrame'
      gate.floor hRest
    have hZero (e : Event) (hp : e.pc = gate.target) (i : Nat)
        (hi : (first :: es)[i]? = some e) : i = 0 := by
      cases i with
      | zero => rfl
      | succ i =>
        have h := (hRange e (List.mem_of_getElem? (show es[i]? = some e from hi))).1
        omega
    have h0 := hZero mark hPcMark n hMark
    have hPos : j + 1 = 5 + (pre.length + 1) := by omega
    have hSuffix : (X.tr g).drop (j+1) = es := by
      rw [hPos, ← List.drop_drop, hSplit]
      simp [List.drop_append]
    exact ⟨w, _, _, hWarp, hAfter, hShape', hFrame', hSuffix ▸ hRest⟩

private theorem loaderGateOccurrenceOnce (gate : QueryGate) {g j k : Nat} {mark other : Event}
    (he : X.get (g, j) = some mark) (hf : X.get (g, k) = some other)
    (hPcMark : mark.pc = gate.target) (hPcOther : other.pc = gate.target) (hCont : ¬ Ends mark)
    (hOther : ¬ Ends other) : j = k := by
  have noLater {j k : Nat} {r e : Event}
      (hr : X.get (g,j) = some r) (he : X.get (g,k) = some e)
      (hR : r.pc = gate.target) (hE : e.pc = gate.target)
      (hCont : ¬ Ends r) (hLt : j < k) : False := by
    obtain ⟨s, warp, _, _, hPc, hS, hF, hw⟩ := loaderWalkAfterGateEvent hp hX gate hr hR hCont
    have hLater : ((X.tr g).drop (j+1))[k-(j+1)]? = some e := by
      rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
      exact he
    have hBounds := gate.bounds
    have hFloor := (loaderWalkEventRange warp (by omega) ⟨by omega, by omega⟩ hS hF gate.floor
      hw e (List.mem_of_getElem? hLater)).1
    omega
  rcases Nat.lt_trichotomy j k with hj | h | hk
  · exact (noLater he hf hPcMark hPcOther hCont hj).elim
  · exact h
  · exact (noLater hf he hPcOther hPcMark hOther hk).elim

private theorem queryOccurrenceOnce {g j k : Nat} {stage plane : Fin 2} {s t : TensorCopy.Spec}
    (he : X.get (g, j) = some ⟨queryPc stage plane, .tensorIssue p.qMapAddress s⟩)
    (hf : X.get (g, k) = some ⟨queryPc stage plane, .tensorIssue p.qMapAddress t⟩) : j = k :=
  loaderGateOccurrenceOnce hp hX (.tensor stage plane) he hf rfl rfl
    (by simp [Ends]) (by simp [Ends])

/-- Each query stage's physical plane has at most one actual issuer in a CTA. -/
theorem querySubboxUnique {i j : EvId} {stage plane : Fin 2} {s t : TensorCopy.Spec}
    (hCta : i.1 / l.block = j.1 / l.block) (hi : QuerySubbox p l X i stage plane s)
    (hj : QuerySubbox p l X j stage plane t) : i = j := by
  obtain ⟨g, a⟩ := i
  obtain ⟨h, b⟩ := j
  have he := queryIssueSite hp hX hi
  have hf := queryIssueSite hp hX hj
  obtain ⟨hg, ai, ak, ha⟩ := queryIssuerElected hp hX he
  obtain ⟨hh, bi, bk, hb⟩ := queryIssuerElected hp hX hf
  have hSame : SameWarp l g h :=
    ⟨⟨event_thread_lt hX he, event_thread_lt hX hf, hCta⟩, hg.trans hh.symm⟩
  have hThread := selected_elect_thread_unique hX.elect ha hb hSame rfl rfl
  change g = h at hThread
  subst h
  exact Prod.ext rfl (queryOccurrenceOnce hp hX he hf)

/-- Each of the first query stage's two planes has a single actual issuer in a CTA. -/
theorem querySubboxZeroUnique {i j : EvId} {plane : Fin 2} {s t : TensorCopy.Spec}
    (hCta : i.1 / l.block = j.1 / l.block) (hi : QuerySubbox p l X i 0 plane s)
    (hj : QuerySubbox p l X j 0 plane t) : i = j :=
  querySubboxUnique hp hX hCta hi hj

/-- The first query object has at most one expectation in a CTA, even in an unfinished trace. -/
theorem queryStageZeroExpectationUnique {cta : Nat} {i j : EvId}
    (hi : X.Arrive i (Thread.Output.queryObject l cta 0) 32768 1 true .cta)
    (hj : X.Arrive j (Thread.Output.queryObject l cta 0) 32768 1 true .cta) : i = j := by
  obtain ⟨g, a⟩ := i
  obtain ⟨h, b⟩ := j
  obtain ⟨site, he⟩ := hi
  obtain ⟨site', hf⟩ := hj
  have hSite : site = 686 := by simpa using actualQueryCreditSite hp hX (0 : Fin 2) he rfl
  have hSite' : site' = 686 := by simpa using actualQueryCreditSite hp hX (0 : Fin 2) hf rfl
  subst site site'
  have hCta := congrArg Loc.cta (loaderFixedArriveOffset hp hX he (by decide))
  have hCta' := congrArg Loc.cta (loaderFixedArriveOffset hp hX hf (by decide))
  change cta = g / l.block at hCta
  change cta = h / l.block at hCta'
  let gate := QueryGate.expectation (0 : Fin 2)
  obtain ⟨hg, i, u, hElect⟩ :=
    loaderQueryGateLeader hp hX gate (by dsimp [gate]; intro h; cases h) he rfl (by simp [Ends])
  obtain ⟨hh, j, v, hElect'⟩ :=
    loaderQueryGateLeader hp hX gate (by dsimp [gate]; intro h; cases h) hf rfl (by simp [Ends])
  have hWarp : SameWarp l g h := ⟨⟨event_thread_lt hX he, event_thread_lt hX hf,
    hCta.symm.trans hCta'⟩, hg.trans hh.symm⟩
  have hThread := selected_elect_thread_unique hX.elect hElect hElect' hWarp rfl rfl
  change g = h at hThread
  subst h
  exact Prod.ext rfl (loaderGateOccurrenceOnce hp hX gate he hf rfl rfl
    (by simp [Ends]) (by simp [Ends]))

omit hp hX in
/-- The second query expectation is issued by the loader at startup or while draining. -/
def StageOneExpectation (l : Launch) (X : Execution) (cta : Nat) (issue : EvId)
    (draining : Bool) : Prop :=
  X.get issue = some ⟨if draining then 1900 else 737,
    .arrive (Thread.Output.queryObject l cta 1) 32768 1 true .cta⟩

/-- Every actual expectation of the second query originates on one of its two paths. -/
theorem stageOneExpectationOfArrival {cta : Nat} {i : EvId}
    (h : X.Arrive i (Thread.Output.queryObject l cta 1) 32768 1 true .cta) :
    ∃ draining, StageOneExpectation l X cta i draining := by
  obtain ⟨site, he⟩ := h
  have hSites := actualQueryCreditSite hp hX (1 : Fin 2) he rfl
  have hCases : site = 737 ∨ site = 1900 := by simpa using hSites
  rcases hCases with rfl | rfl
  · exact ⟨false, he⟩
  · exact ⟨true, he⟩

private theorem stageOneExpectationLeader {cta g j : Nat} {draining : Bool}
    (he : StageOneExpectation l X cta (g,j) draining) :
    cta = g / l.block ∧ warpIndex l g = 14 ∧
      ∃ index pc inst, X.Elect (g,index) pc (2 ^ 32 - 1) inst (laneOf l g) := by
  cases draining
  · have him := loaderFixedArriveOffset hp hX he (pc := 737) (by decide)
    have hCta := congrArg Loc.cta him
    obtain ⟨hw, index, inst, hElect⟩ :=
      loaderQueryGateLeader hp hX (.expectation 1) (by intro h; cases h) he rfl (by simp [Ends])
    exact ⟨hCta, hw, index, _, inst, hElect⟩
  · have him := loaderFixedArriveOffset hp hX he (pc := 1900) (by decide)
    have hCta := congrArg Loc.cta him
    obtain ⟨hw, index, inst, hElect⟩ := drainQueryGateLeader hp hX he rfl (by simp [Ends])
    exact ⟨hCta, hw, index, _, inst, hElect⟩

/-- An actual expectation uses the second query object in its own CTA. -/
theorem stageOneExpectationOwner {cta : Nat} {issue : EvId} {draining : Bool}
    (h : StageOneExpectation l X cta issue draining) : cta = issue.1 / l.block := by
  obtain ⟨g, index⟩ := issue
  exact (stageOneExpectationLeader hp hX h).1

/-- Both second-query expectation paths in one CTA select the same physical issuer. -/
theorem stageOneExpectationSameIssuer {cta : Nat} {i j : EvId} {draining other : Bool}
    (hi : StageOneExpectation l X cta i draining) (hj : StageOneExpectation l X cta j other) :
    i.1 = j.1 := by
  obtain ⟨g, a⟩ := i
  obtain ⟨h, b⟩ := j
  obtain ⟨hCta, hWarp, x, _, _, hElec⟩ := stageOneExpectationLeader hp hX hi
  obtain ⟨hCta', hWarp', y, _, _, hElec'⟩ := stageOneExpectationLeader hp hX hj
  have hSame : SameWarp l g h := ⟨⟨event_thread_lt hX hi, event_thread_lt hX hj,
    hCta.symm.trans hCta'⟩, hWarp.trans hWarp'.symm⟩
  exact selected_elect_thread_unique (e := (g,x)) (f := (h,y))
    hX.elect hElec hElec' hSame rfl rfl

/-- The second query has at most one occurrence of each expectation path in its CTA. -/
theorem stageOneExpectationUnique {cta : Nat} {i j : EvId} {draining : Bool}
    (hi : StageOneExpectation l X cta i draining) (hj : StageOneExpectation l X cta j draining) :
    i = j := by
  obtain ⟨g, a⟩ := i
  obtain ⟨h, b⟩ := j
  have heq : g = h := stageOneExpectationSameIssuer hp hX hi hj
  subst h
  cases draining
  · exact Prod.ext rfl
      (loaderGateOccurrenceOnce hp hX (.expectation 1) hi hj rfl rfl
        (by simp [Ends]) (by simp [Ends]))
  · exact Prod.ext rfl (loaderGateOccurrenceOnce hp hX .drain hi hj rfl rfl
      (by simp [Ends]) (by simp [Ends]))

omit hp hX in
private theorem gateWalkRun {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {visits : List Visit} (hw : Walk kernel Assumptions.all l g s es visits) :
    ∃ result, Run kernel Assumptions.all l g s es result := by
  induction hw with
  | stop => exact ⟨some _, .nil _⟩
  | tau ht _ ih =>
    obtain ⟨_, hr⟩ := ih
    cases hr with
    | nil => exact ⟨some _, .nil _⟩
    | step hl he tail => exact ⟨_, .step (.head ht hl) he tail⟩
    | last hl he => exact ⟨none, .last (.head ht hl) he⟩
  | ev he _ ih =>
    obtain ⟨_, hr⟩ := ih
    exact ⟨_, .step .refl he hr⟩
  | last he => exact ⟨none, .last .refl he⟩

private theorem stageOneInitialBeforeDrain {cta g a b : Nat}
    (hA : StageOneExpectation l X cta (g,a) false) (hB : StageOneExpectation l X cta (g,b) true)
    : a < b := by
  by_contra! hOrder
  have hNe : a ≠ b := by
    intro h
    subst b
    have h := Option.some.inj (hA.symm.trans hB)
    have hh := congrArg Event.pc h
    change 737 = 1900 at hh
    omega
  have hPrev : b + 1 ≤ a := by omega
  obtain ⟨s, warp, _, _, hPc, hShape, hRegs, hWalk⟩ :=
    loaderWalkAfterGateEvent hp hX .drain hB rfl (by simp [Ends])
  let early : Event := ⟨737,
    .arrive (Thread.Output.queryObject l cta 1) 32768 1 true .cta⟩
  have hGet : ((X.tr g).drop (b+1))[a-(b+1)]? = some early := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hPrev]
    exact hA
  have hFloor := (loaderWalkEventRange warp (lower := 1901) (by decide)
    (show 1901 ≤ s.pc ∧ s.pc ≤ 1901 by exact ⟨hPc.symm.le, hPc.le⟩) hShape hRegs
    (QueryGate.floor .drain) hWalk early (List.mem_of_getElem? hGet)).1
  change 1901 ≤ 737 at hFloor
  omega

/-- When both second-query expectation paths are in the actual trace, the draining expectation
depends on the successful, phase-zero wait on the second query's empty object. -/
theorem stageOneDrainingExpectationAfterEmptyWait {cta : Nat} {initial draining : EvId}
    (hInitial : StageOneExpectation l X cta initial false)
    (hDrain : StageOneExpectation l X cta draining true) :
    ∃ wait e, X.get wait = some e ∧
      e.kind = .wait ⟨.shared, cta, l.sharedBase + 24⟩ 0 true true .cta ∧
      Resumes kernel X wait draining := by
  obtain ⟨g, a⟩ := initial
  obtain ⟨h, b⟩ := draining
  have hSame : g = h := stageOneExpectationSameIssuer hp hX hInitial hDrain
  subst h
  obtain ⟨hCta, _, _, _, _, _⟩ := stageOneExpectationLeader hp hX hDrain
  have hOrder := stageOneInitialBeforeDrain hp hX hInitial hDrain
  obtain ⟨s, warp, _, _, hPc, hShape, hFrame, hWalk⟩ :=
    loaderWalkAfterGateEvent hp hX (.expectation 1) hInitial rfl (by simp [Ends])
  let later : Event := ⟨1900,
    .arrive (Thread.Output.queryObject l cta 1) 32768 1 true .cta⟩
  let F := dispatchFrame l warp
  let G := (7192, b32 0) :: F
  let W := (2305, b32 (l.sharedBase + 24)) :: G
  have roots : ∀ r ∈ [2535, 1062], r ∈ F.map Prod.fst := fun _ h => h
  have hGet : ((X.tr g).drop (a+1))[b-(a+1)]? = some later := by
    rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
    exact hDrain
  have hLater : ¬ Ends later := by simp [Ends, later]
  have hBeforeMove : ((kernel.code.drop 738).take (1849 - 738)).all
      (fun i => loaderPipelineCutOp 738 1849 1900 (F.map Prod.fst) i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨t, early, tail0, _, _, hSplit, _, ht, hT, hF, _, hW, hSeen, _⟩ :=
    goesThroughLoaderCut warp (by decide) (by decide : 1849 ≤ 1900) rfl
      (by decide) (QueryGate.floor .drain) hLater roots hBeforeMove hWalk
      (by rw [hPc]; decide) hShape hFrame hFrame hGet
  have hMem := List.mem_of_getElem? hSeen
  have hAt : At t 1849 F := pipelineAtCut ht hT hF
    (walkWithContinuingEventClean hW hMem hLater) ⟨_, Flow.code_1849, rfl⟩
  have hMove : Seg kernel [] l g 1 1849 F 1850 G := by
    intro q hq
    simp only [G, F, dispatchFrame] at hq ⊢
    seg_fp hq using rfl
  obtain ⟨u, hMove, hu⟩ := hMove t hAt
  have hMove' := (loaderLinear (regs := []) (by decide) (by decide) hAt.1
    (by simp) rfl hMove).1
  have hTau := tauStep_iff.mp (by simpa [run] using hMove')
  obtain ⟨_, hAfter⟩ := walkAfterExactTau hW (List.ne_nil_of_mem hMem) hTau
  have hBeforeWait : ((kernel.code.drop 1850).take (1892 - 1850)).all
      (fun i => loaderPipelineCutOp 1850 1892 1900 (G.map Prod.fst) i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨v, middle, tail, _, _, hSplit', _, hv, hS, hF, _, hW, hSeen, _⟩ :=
    goesThroughLoaderCut (F := G) warp (by decide) (by decide : 1892 ≤ 1900) rfl
      (by decide) (QueryGate.floor .drain) hLater (fun _ h => List.mem_cons_of_mem _ h)
      hBeforeWait hAfter (by rw [hu.1]; decide) (ringShapeOfAt hu) hu.2.2.2.2
      hu.2.2.2.2.2 hSeen
  have hMem := List.mem_of_getElem? hSeen
  have hAt : At v 1892 G := pipelineAtCut hv hS hF
    (walkWithContinuingEventClean hW hMem hLater) ⟨_, Flow.code_1892, rfl⟩
  have hAddr : l.sharedBase + 24 < 2^32 := by have := hp.shared.2.1; omega
  have hAl : (l.sharedBase + 24) % 8 = 0 := by have := hp.shared.1; omega
  have hAdd : Seg kernel [] l g 1 1892 G 1893 W := by
    intro q hq
    simp only [W, G, F, dispatchFrame] at hq ⊢
    seg_fp hq using norm_bits
  obtain ⟨i, hAdd, hi⟩ := hAdd v hAt
  have hAdd' := (loaderLinear (regs := []) (by decide) (by decide) hAt.1
    (by simp) rfl hAdd).1
  have hTau := tauStep_iff.mp (by simpa [run] using hAdd')
  obtain ⟨_, hBody⟩ := walkAfterExactTau hW (List.ne_nil_of_mem hMem) hTau
  obtain ⟨_, hr⟩ := gateWalkRun hBody
  let site := drainWaitSite (3 : Fin 4)
  have hCode : LoaderWaitCode site := ⟨Flow.code_1893, Flow.code_1894, Flow.code_1895⟩
  obtain ⟨n, rest, hEs, hl⟩ := loaderWaitBeforeEvent site hCode (by decide)
    hAddr hAl (by decide : 0 < 2) (by
      intro pair hm
      change pair ∈ [(2305, b32 (l.sharedBase + 24)), (7192, b32 0),
        (2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;>
        simp only [site, drainWaitSite] <;> decide)
    (by simp [site, drainWaitSite, W]) (by simp [site, drainWaitSite, W, G])
    hi hr hMem (by change 1900 ≠ 1893; decide)
  let stop : Nat := a+1+early.length+middle.length+n
  have hSuf : (X.tr g).drop stop =
      (⟨1893, .wait ⟨.shared, g / l.block, l.sharedBase + 24⟩ 0 true true .cta⟩ : Event) ::
       rest := by
    unfold stop
    rw [show a+1+early.length+middle.length+n =
      (a+1)+(early.length+(middle.length+n)) by omega, ← List.drop_drop, hSplit]
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega),
      List.nil_append, Nat.add_sub_cancel_left]
    rw [hSplit', List.drop_append, List.drop_eq_nil_of_le (by omega),
      List.nil_append, Nat.add_sub_cancel_left, hEs]
    simp [site, drainWaitSite]
  have hGetWait : X.get (g,stop) =
      some ⟨1893, .wait ⟨.shared, g / l.block, l.sharedBase + 24⟩ 0 true true .cta⟩ := by
    have hh := congrArg (fun xs : List Event => xs[0]?) hSuf
    simpa only [Execution.get, List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using hh
  obtain ⟨pos, hAt⟩ := List.mem_iff_getElem?.mp hl
  have hg : X.get (g,stop+1+pos) = some later := by
    have hh := congrArg (fun xs : List Event => xs[1+pos]?) hSuf
    rw [List.getElem?_drop] at hh
    simpa only [Execution.get, Nat.add_assoc, Nat.add_comm 1 pos, Nat.succ_eq_add_one,
      List.getElem?_cons_succ, hAt] using hh
  have hB : (g,stop+1+pos) = (g,b) := stageOneExpectationUnique hp hX (draining := true) hg hDrain
  have hIndex : stop+1+pos = b := congrArg Prod.snd hB
  have hBefore : TraceBefore X (g,stop) (g,b) := ⟨rfl, by omega,
    (List.getElem?_eq_some_iff.mp (show X.get (g,b) = some later from hDrain)).1⟩
  obtain ⟨exitPc, hSpin⟩ := actualCanonicalPoll hX hGetWait
  refine ⟨(g,stop), _, hGetWait, ?_, hBefore, ?_⟩
  · rw [hCta]
  · simp only [hGetWait, Option.map_some, Kind.resume]
    exact ⟨_, exitPc, _, 0, true, .cta, hGetWait, hSpin, hBefore⟩

omit hp hX in
private theorem walkWithExitClean {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (he : (⟨9205, .exit⟩ : Event) ∈ es) : s.fault = none := by
  cases hf : s.fault
  · rfl
  cases hw with
  | stop => cases he
  | tau ht _ => simp [Tau, out, hf] at ht
  | ev hStep _ =>
    obtain ⟨tmpl, ho, hFire⟩ := hStep
    simp only [out, hf, Out.ev.injEq] at ho
    subst tmpl
    cases hFire.2
  | last hStep =>
    obtain rfl := List.mem_singleton.mp he
    obtain ⟨tmpl, ho, hFire⟩ := hStep
    simp only [out, hf, Out.ev.injEq] at ho
    subst tmpl
    exact Kind.noConfusion (congrArg Event.kind hFire.1)

omit hp hX in
private theorem loaderCutBeforeExit {l : Launch} {g lower cut : Nat} {s : TState}
    {F : List (Nat × Value)} {es : List Event} {vs : List Visit}
    (hLo : 174 ≤ lower) (hCut : cut ≤ 1901)
    (hAudit : ∀ branch, ((kernel.code.drop lower).take (cut-lower)).all
      (fun i => loaderPipelineCutOp lower cut branch (F.map Prod.fst) i.op) = true)
    (hw : Walk kernel Assumptions.all l g s es vs) (hBounds : lower ≤ s.pc ∧ s.pc ≤ cut)
    (hShape : RingShape s) (hFrame : Holds s.regs F)
    (hExit : (⟨9205, .exit⟩ : Event) ∈ es) :
    ∃ t pre tail visits, es = pre ++ tail ∧ t.pc = cut ∧ RingShape t ∧ Holds t.regs F ∧
      Walk kernel Assumptions.all l g t tail visits ∧ (⟨9205, .exit⟩ : Event) ∈ tail := by
  have advance {t u : TState} {ev : Option Event} (hBounds : lower ≤ t.pc ∧ t.pc < cut)
      (hShape : RingShape t) (hFrame : Holds t.regs F)
      (hs : WStep kernel Assumptions.all l g t ev u) :
      (lower ≤ u.pc ∧ u.pc ≤ cut) ∧ RingShape u ∧ Holds u.regs F := by
    obtain ⟨hLo, hHi, hShape, hFrame⟩ :=
      pipelineCutStep hLo hCut hBounds (hAudit u.pc) hs hShape hFrame
    exact ⟨⟨hLo, hHi.resolve_right (Nat.lt_irrefl _)⟩, hShape, hFrame⟩
  induction hw with
  | stop => cases hExit
  | @tau t u es vs hStep hRest ih =>
    by_cases ht : t.pc = cut
    · exact ⟨t, [], es, _, rfl, ht, hShape, hFrame, .tau hStep hRest, hExit⟩
    obtain ⟨hBounds, hShape, hFrame⟩ := advance ⟨hBounds.1, by omega⟩ hShape hFrame
      (.inl ⟨rfl, hStep⟩)
    exact ih hBounds hShape hFrame hExit
  | @ev t u e es vs hStep hRest ih =>
    by_cases ht : t.pc = cut
    · exact ⟨t, [], e :: es, _, rfl, ht, hShape, hFrame, .ev hStep hRest, hExit⟩
    have hRestExit : (⟨9205, .exit⟩ : Event) ∈ es := by
      rcases List.mem_cons.mp hExit with h | h
      · have hPc := estep_source_pc hStep
        rw [← h] at hPc
        change 9205 = t.pc at hPc
        omega
      · exact h
    obtain ⟨hBounds, hShape, hFrame⟩ := advance ⟨hBounds.1, by omega⟩ hShape hFrame
      (.inr ⟨e, rfl, hStep⟩)
    obtain ⟨v, pre, tail, rest, hES, hv, hShape, hFrame, hWalk, hSeen⟩ :=
      ih hBounds hShape hFrame hRestExit
    exact ⟨v, e :: pre, tail, rest, congrArg (e :: ·) hES, hv, hShape, hFrame, hWalk, hSeen⟩
  | @last t e hStep =>
    obtain rfl := List.mem_singleton.mp hExit
    have hPc := estep_source_pc hStep
    change 9205 = t.pc at hPc
    omega

/-- A second-query issuer that has exited ran the acquire on the returned query bank.
The active path resets its parity, and the issuing loader warp takes the query drain. -/
theorem queryReturnWaitBeforeOwnerExit {i : EvId} {plane : Fin 2} {spec : TensorCopy.Spec}
    (hBox : QuerySubbox p l X i 1 plane spec) (hExit : CtaExited l X (i.1 / l.block)) :
    ∃ wait finish, (∃ e, X.get wait = some e ∧
      e.kind = .wait ⟨.shared, i.1 / l.block, l.sharedBase + 24⟩ 0 true true .cta) ∧
      Resumes kernel X wait finish ∧ OwnerExit l X (i.1 / l.block) finish := by
  obtain ⟨g, j⟩ := i
  have he := queryIssueSite hp hX hBox
  have hw := (queryIssuerElected hp hX he).1
  obtain ⟨s, warp, _, hWarp, hs, hShape, hFrame, hWalk⟩ :=
    loaderWalkAfterGateEvent hp hX (.tensor 1 plane) he rfl (by simp [Ends])
  have hW0 : warp = 0 := Fin.ext (by omega)
  subst warp
  have hg := event_thread_lt hX he
  obtain ⟨exitPc, hLast⟩ := hExit g hg rfl
  let exitIndex := (X.tr g).length - 1
  have hGetExit : X.get (g, exitIndex) = some ⟨exitPc, .exit⟩ := by
    rwa [List.getLast?_eq_getElem?] at hLast
  have hExitPc := actualExitPc hX hGetExit
  subst exitPc
  have hAfter : j < exitIndex := by
    have hLen := (List.getElem?_eq_some_iff.mp he).1
    change j < (X.tr g).length at hLen
    have hNe : j ≠ exitIndex := by
      intro h
      rw [h, hGetExit] at he
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj he))
    dsimp [exitIndex] at hNe ⊢
    omega
  let e : Event := ⟨9205, .exit⟩
  have hE : e ∈ (X.tr g).drop (j+1) := by
    apply List.mem_of_getElem? (i := exitIndex - (j+1))
    rw [List.getElem?_drop, Nat.add_sub_of_le hAfter]
    exact hGetExit
  let F := dispatchFrame l (0 : Fin 2)
  let G := (7192, b32 0) :: F
  let H := (258, .pred false) :: G
  let W := (2305, b32 (l.sharedBase + 24)) :: G
  have beforeMove : ∀ bound, ((kernel.code.drop 746).take (1849 - 746)).all
      (fun i => loaderPipelineCutOp 746 1849 bound (F.map Prod.fst) i.op) = true := by
    intro bound
    set_option maxRecDepth 100000 in kernel_rfl
  have hBounds : 746 ≤ s.pc ∧ s.pc ≤ 1849 := by
    rw [hs]
    fin_cases plane <;> decide
  obtain ⟨atMove, early, tail, _, hSplit, hPc, hShape, hF, hWalk, hMem⟩ :=
    loaderCutBeforeExit (by decide) (by decide) beforeMove hWalk hBounds hShape hFrame hE
  have hAt := pipelineAtCut hPc hShape hF (walkWithExitClean hWalk hMem)
    ⟨_, Flow.code_1849, rfl⟩
  have moveParity : Seg kernel [] l g 1 1849 F 1850 G := by
    intro t ht
    simp only [F, G, dispatchFrame] at ht ⊢
    seg_fp ht using rfl
  obtain ⟨u, hu, hU⟩ := moveParity atMove hAt
  have hRun := (loaderLinear (regs := []) (by decide) (by decide) hAt.1 (by simp) rfl hu).1
  obtain ⟨_, hWalk⟩ := walkAfterExactTau hWalk (List.ne_nil_of_mem hMem)
    (tauStep_iff.mp (by simpa [run] using hRun))
  have beforeRole : ∀ bound, ((kernel.code.drop 1850).take (1862 - 1850)).all
      (fun i => loaderPipelineCutOp 1850 1862 bound (G.map Prod.fst) i.op) = true := by
    intro bound
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨atRole, middle, rest, _, hSplitRole, hPc, hShape, hG, hWalk, hMem⟩ :=
    loaderCutBeforeExit (by decide) (by decide) beforeRole hWalk (by rw [hU.1]; decide)
      (ringShapeOfAt hU) hU.2.2.2.2 hMem
  have hAt := pipelineAtCut hPc hShape hG (walkWithExitClean hWalk hMem)
    ⟨_, Flow.code_1862, rfl⟩
  have checkRole : Seg kernel [] l g 1 1862 G 1863 H := by
    intro t ht
    simp only [H, G, F, dispatchFrame, Fin.val_zero, Nat.add_zero] at ht ⊢
    seg_fp ht using rfl
  obtain ⟨v, hv, hV⟩ := checkRole atRole hAt
  have hRun := (loaderLinear (regs := []) (by decide) (by decide) hAt.1 (by simp) rfl hv).1
  obtain ⟨_, hWalk⟩ := walkAfterExactTau hWalk (List.ne_nil_of_mem hMem)
    (tauStep_iff.mp (by simpa [run] using hRun))
  have beforeBranch : ∀ bound, ((kernel.code.drop 1863).take (1891 - 1863)).all
      (fun i => loaderPipelineCutOp 1863 1891 bound (H.map Prod.fst) i.op) = true := by
    intro bound
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨branch, drains, suffix, _, hSplitDrains, hPc, hShape, hH, hWalk, hMem⟩ :=
    loaderCutBeforeExit (by decide) (by decide) beforeBranch hWalk (by rw [hV.1]; decide)
      (ringShapeOfAt hV) hV.2.2.2.2 hMem
  have hAt := pipelineAtCut hPc hShape hH (walkWithExitClean hWalk hMem)
    ⟨_, Flow.code_1891, rfl⟩
  have hBranch := drainRoleBranch (l := l) (g := g) (warp := 0)
    (hAt.mono ⟨hH.1, hH.2.2⟩)
  have hBranch : Tau kernel Assumptions.all l g branch (next branch) := hBranch
  obtain ⟨_, hWalk⟩ := walkAfterExactTau hWalk (List.ne_nil_of_mem hMem) hBranch
  have hAt : At (next branch) 1892 G := by
    exact (hAt.mono hH.2).next
  have hAddr : l.sharedBase + 24 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hAl : (l.sharedBase + 24) % 8 = 0 := by have := hp.shared.1; omega
  have addAddress : Seg kernel [] l g 1 1892 G 1893 W := by
    intro t ht
    simp only [W, G, F, dispatchFrame] at ht ⊢
    seg_fp ht using norm_bits
  obtain ⟨t, ht, hT⟩ := addAddress (next branch) hAt
  have hRun := (loaderLinear (regs := []) (by decide) (by decide) hAt.1 (by simp) rfl ht).1
  obtain ⟨_, hWalk⟩ := walkAfterExactTau hWalk (List.ne_nil_of_mem hMem)
    (tauStep_iff.mp (by simpa [run] using hRun))
  obtain ⟨_, hRun⟩ := gateWalkRun hWalk
  let site := drainWaitSite (3 : Fin 4)
  have hCode : LoaderWaitCode site := ⟨Flow.code_1893, Flow.code_1894, Flow.code_1895⟩
  obtain ⟨n, after, hSplitPoll, hExitAfter⟩ := loaderWaitBeforeEvent site hCode (by decide)
    hAddr hAl (by decide : 0 < 2) (by
      intro pair hm
      change pair ∈ [(2305, b32 (l.sharedBase + 24)), (7192, b32 0),
        (2535, b32 l.sharedBase), (1062, b32 14)] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> simp [site, drainWaitSite])
    (by simp [site, drainWaitSite, W]) (by simp [site, drainWaitSite, W, G])
    hT hRun hMem (by change 9205 ≠ 1893; decide)
  let events := List.replicate n
    (⟨1893, .wait ⟨.shared, g / l.block, l.sharedBase + 24⟩ 0 false true .cta⟩ : Event)
  let success : Event := ⟨1893, .wait ⟨.shared, g / l.block, l.sharedBase + 24⟩ 0 true true .cta⟩
  let pre := early ++ middle ++ drains ++ events
  have hTrace : (X.tr g).drop (j + 1) = pre ++ success :: after := by
    rw [hSplit, hSplitRole, hSplitDrains, hSplitPoll]
    simp [pre, events, success, site, drainWaitSite, List.append_assoc]
  let stop := j + 1 + pre.length
  have hTail : (X.tr g).drop stop = success :: after := by
    simp [stop, ← List.drop_drop, hTrace]
  have hGet : X.get (g, stop) = some success := by
    have h := congrArg (fun xs : List Event => xs[0]?) hTail
    simpa only [Execution.get, List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using h
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hExitAfter
  have hFinish : X.get (g, stop+1+k) = some e := by
    have h := congrArg (fun xs : List Event => xs[k.succ]?) hTail
    simp only [List.getElem?_drop, List.getElem?_cons_succ, hk] at h
    simpa only [Execution.get, Nat.add_assoc, Nat.succ_eq_add_one, Nat.add_comm k 1] using h
  obtain ⟨endPc, hCanon⟩ := actualCanonicalPoll hX hGet
  exact ⟨(g,stop), (g,stop+1+k), ⟨success, hGet, rfl⟩,
    Resumes.of_spin hGet hCanon rfl (by omega) (len_of_get hFinish), hg, rfl, 9205, hFinish⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
