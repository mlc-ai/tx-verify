-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryOperandsProgress
import Kernels.TmlFa4Fwd.Proof.ResultGeometry
import Kernels.TmlFa4Fwd.Flow.Code.Part010
import Kernels.TmlFa4Fwd.Flow.Code.Part011
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSecondQueryProgress
import Lemmas.Protocol.ElectCount
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
import Lemmas.Flow.ReturningPrefix
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue Epilogue

private def queryBoxSite (stage plane : Fin 2) : Fin 14 :=
  ⟨4*stage.val + plane.val, by have := stage.isLt; have := plane.isLt; omega⟩

private def queryBoxElect (stage plane : Fin 2) : Nat :=
  if stage = 0 then 687+7*plane.val else 738+8*plane.val

private def queryBoxElectDst (stage plane : Fin 2) : Nat :=
  if stage = 0 then 1893+2*plane.val else 1911+3*plane.val

private def queryBoxElectPred (stage plane : Fin 2) : Nat :=
  if stage = 0 then 142+2*plane.val else 154+2*plane.val

private def queryBoxLength (stage : Fin 2) : Nat := if stage = 0 then 7 else 8
private def queryBoxPrepLength (stage : Fin 2) : Nat := if stage = 0 then 3 else 4
private def queryBoxRow (stage : Fin 2) (row : Nat) : Nat := row + 128*stage.val

/-- The local register update shared by full-mask input elections. -/
def inputElectReturn (l : Launch) (g : Nat) (t : TState) (dst pred leader : Nat) : TState :=
  next (setReg (setReg t dst (b32 leader)) pred (.pred (laneOf l g == leader)))

/-- A checked loader election exposes the full-mask reply and its exact local update. -/
theorem inputElectOut {l : Launch} {g pc dst pred : Nat} {s : TState}
    (hPc : s.pc = pc) (hFault : s.fault = none) (hlo : 174 ≤ pc) (hhi : pc < 1906)
    (hCode : kernel.code[pc]? = some ⟨none,.warp {
      kind := .elect, ty := none, dsts := [some dst,some pred],
      srcs := [], mask := some (.imm (-1)) }⟩) :
    out kernel Assumptions.all l g s =
      .ev (.elect 4294967295 (inputElectReturn l g s dst pred)) := by
  rw [loaderOutCore (hPc.symm ▸ hlo) (hPc.symm ▸ hhi)]
  rw [out_event hFault (hPc.symm ▸ hCode) rfl rfl]
  have hMask : readBits l g s 32 (.imm (-1)) = .ok 4294967295#64 := rfl
  have hMember : electMember 4294967295 (laneOf l g) := PTX.electMember_full l g
  change Out.ev (electTmpl l g s (some dst) pred (.imm (-1))) = _
  simp only [electTmpl,hMask,show (4294967295#64).toNat = 4294967295 from rfl,hMember,↓reduceIte]
  rfl

private def queryBoxElectReturn (l : Launch) (g : Nat) (t : TState) (stage plane : Fin 2)
    (leader : Nat) : TState :=
  next (setReg (setReg t (queryBoxElectDst stage plane) (b32 leader))
    (queryBoxElectPred stage plane) (.pred (laneOf l g == leader)))

private theorem queryBoxElectOut {l : Launch} {g : Nat} {s : TState} (stage plane : Fin 2)
    (hPc : s.pc = queryBoxElect stage plane) (hFault : s.fault = none) :
    out kernel Assumptions.all l g s =
      .ev (.elect 4294967295 (queryBoxElectReturn l g s stage plane)) := by
  have hlo : 174 ≤ queryBoxElect stage plane := by fin_cases stage <;> fin_cases plane <;> decide
  have hhi : queryBoxElect stage plane < 1906 := by fin_cases stage <;> fin_cases plane <;> decide
  rw [loaderOutCore (hPc.symm ▸ hlo) (hPc.symm ▸ hhi)]
  have hCode : kernel.code[s.pc]? = some ⟨none,.warp {
      kind := .elect, ty := none,
      dsts := [some (queryBoxElectDst stage plane),some (queryBoxElectPred stage plane)],
      srcs := [], mask := some (.imm (-1)) }⟩ := by
    rw [hPc]
    fin_cases stage <;> fin_cases plane
    · exact Flow.code_687
    · exact Flow.code_694
    · exact Flow.code_738
    · exact Flow.code_746
  rw [out_event hFault hCode rfl rfl]
  have hMask : readBits l g s 32 (.imm (-1)) = .ok 4294967295#64 := rfl
  have hMember : electMember 4294967295 (laneOf l g) := PTX.electMember_full l g
  change Out.ev (electTmpl l g s (some (queryBoxElectDst stage plane))
    (queryBoxElectPred stage plane) (.imm (-1))) = _
  simp only [electTmpl,hMask,show (4294967295#64).toNat = 4294967295 from rfl,hMember,↓reduceIte]
  rfl

private theorem queryBoxElectedFrame {l : Launch} {g row head leader : Nat} {s : TState}
    (stage plane : Fin 2)
    (hs : At s (queryBoxElect stage plane) (queryPrimingOperands l row head)) :
    At (queryBoxElectReturn l g s stage plane leader) (queryBoxElect stage plane+1)
      ((queryBoxElectPred stage plane,.pred (laneOf l g == leader)) ::
        queryPrimingOperands l row head) := by
  refine ⟨by simp [queryBoxElectReturn,next,setReg,hs.1],
    hs.2.1,hs.2.2.1,hs.2.2.2.1,?_⟩
  have ht := hs.2.2.2.2
  rcases ht with ⟨hPtr,hBase,hRow,hHead,_⟩
  fin_cases stage <;> fin_cases plane <;>
    simp [Holds,queryPrimingOperands,queryBoxElectReturn,queryBoxElectPred,
      queryBoxElectDst,next,setReg,hPtr,hBase,hRow,hHead]

/-- A guarded input box either takes its local setup or skips to the next warp cursor. -/
theorem inputBoxChoice {l : Launch} {g pc pred endPc : Nat} {F : List (Nat × Value)}
    (takeBox : Bool) (hlo : 174 ≤ pc+1) (hhi : pc+3 ≤ 1906)
    (hNotCode : kernel.code[pc+1]? = some
      ⟨none,.int ⟨.not,.pred,false,[some (pred+1)],[.reg pred]⟩⟩)
    (hBranchCode : kernel.code[pc+2]? =
      some ⟨some (pred+1,false),.bra endPc false⟩)
    (hFrameFresh : ∀ pair ∈ F, pair.1 ≠ pred+1)
    {s : TState} (hs : At s (pc+1)
      ((pred,.pred takeBox) :: F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if takeBox then pc+3 else endPc) (F) := by
  have hNot : Seg kernel [] l g 1 (pc+1)
      ((pred,.pred takeBox) :: F) (pc+2)
      ((pred+1,.pred (!takeBox)) :: F) := by
    intro t ht
    let newReg := pred + 1
    have hPred : readPred l g t (.reg (pred)) = .ok takeBox := by
      simp [readPred,readReg,ht.2.2.2.2.1,bind,Except.bind,pure,Except.pure]
    have hFresh : ∀ pair ∈ (pred,.pred takeBox) :: F, pair.1 ≠ newReg := by
      intro pair hm
      rcases List.mem_cons.mp hm with rfl | hm
      · change pred ≠ pred + 1
        omega
      · exact hFrameFresh pair hm
    let u := next (setReg t newReg (.pred (!takeBox)))
    have hRun : run kernel [] l g 1 t = some u := by
      apply run_local hNotCode rfl ht
      rw [execLocalA_nil]
      change execInt l g t
        ⟨.not,.pred,false,[some newReg],[.reg (pred)]⟩ = _
      simp [execInt,DType.width,hPred,u,bind,Except.bind,pure,Except.pure]
    have hAt := ht.set (v := .pred (!takeBox)) hFresh
    exact ⟨u,hRun,hAt.mono ⟨hAt.2.2.2.2.1,hAt.2.2.2.2.2.2⟩⟩
  obtain ⟨v,hv,hV⟩ := hNot s hs
  obtain ⟨w,hw,hW⟩ := run_bra (K := kernel) (A := []) hBranchCode (!takeBox) hV hV.2.2.2.2.1
    (by simp)
  have hv' := (loaderLinear (l := l) (g := g) (regs := []) (n := 1) hlo (by omega)
    hs.1 (List.all_eq_true.mpr (fun _ _ => rfl)) rfl hv).1
  have hw' := (loaderLinear (l := l) (g := g) (regs := []) (n := 1) (by omega) (by omega)
    hV.1 (List.all_eq_true.mpr (fun _ _ => rfl)) rfl hw).1
  refine ⟨w,run_rtg (run_comp hv' hw'),?_⟩
  cases takeBox <;> simpa [Nat.add_assoc] using hW.mono hW.2.2.2.2.2

private theorem queryBoxChoice {l : Launch} {g row head : Nat} (stage plane : Fin 2)
    (takeBox : Bool) {s : TState}
    (hs : At s (queryBoxElect stage plane+1)
      ((queryBoxElectPred stage plane,.pred takeBox) :: queryPrimingOperands l row head)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if takeBox then queryBoxElect stage plane+3
        else queryBoxElect stage plane+queryBoxLength stage)
        (queryPrimingOperands l row head) := by
  apply inputBoxChoice takeBox ?_ ?_ ?_ ?_ ?_ hs
  · fin_cases stage <;> fin_cases plane <;> decide
  · fin_cases stage <;> fin_cases plane <;> decide
  · fin_cases stage <;> fin_cases plane
    · exact Flow.code_688
    · exact Flow.code_695
    · exact Flow.code_739
    · exact Flow.code_747
  · fin_cases stage <;> fin_cases plane
    · exact Flow.code_689
    · exact Flow.code_696
    · exact Flow.code_740
    · exact Flow.code_748
  · fin_cases stage <;> fin_cases plane <;> simp [queryPrimingOperands,queryBoxElectPred]

private theorem queryBoxIssueFrame {l : Launch} {g row head : Nat} (stage plane : Fin 2)
    (hRow : queryBoxRow stage row < 2^31)
    {s : TState} (hs : At s (queryBoxElect stage plane+1)
      ((queryBoxElectPred stage plane,.pred true) :: queryPrimingOperands l row head)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (inputSite (queryBoxSite stage plane)).pc
        (inputSiteFacts l (inputSite (queryBoxSite stage plane)) (64*plane.val)
          (queryBoxRow stage row) head l.sharedBase 0 ++
          queryPrimingOperands l row head) := by
  obtain ⟨v,hv,hV⟩ := queryBoxChoice (g := g) stage plane true hs
  have hPrep : Seg kernel [] l g (queryBoxPrepLength stage) (queryBoxElect stage plane+3)
      (queryPrimingOperands l row head)
      (inputSite (queryBoxSite stage plane)).pc
      (inputSiteFacts l (inputSite (queryBoxSite stage plane)) (64*plane.val)
          (queryBoxRow stage row) head l.sharedBase 0 ++
        queryPrimingOperands l row head) := by
    fin_cases stage <;> fin_cases plane <;> intro t ht <;>
      dsimp [queryBoxElect,queryPrimingOperands,queryBoxSite,inputSiteFacts,inputSite,inputParam,
        queryBoxPrepLength,queryBoxRow] at ht ⊢
    all_goals
      have hFit := hRow.trans (by decide : 2^31 < 2^32)
      dsimp [queryBoxRow] at hFit
      seg_fp ht using first | rfl | norm_bits [Nat.mod_eq_of_lt hFit]
  obtain ⟨u,hu,hU⟩ := hPrep v hV
  have hlo : 174 ≤ queryBoxElect stage plane+3 := by fin_cases stage <;> fin_cases plane <;> decide
  have hhi : queryBoxElect stage plane+3+queryBoxPrepLength stage ≤ 1906 := by
    fin_cases stage <;> fin_cases plane <;> decide
  have hA := (loaderLinear (regs := []) hlo hhi hV.1
    (List.all_eq_true.mpr fun _ _ => rfl)
    (by fin_cases stage <;> fin_cases plane <;> (set_option maxRecDepth 100000 in kernel_rfl)) hu).1
  exact ⟨u,hv.trans (run_rtg hA),hU⟩

set_option maxRecDepth 100000 in
private theorem afterBoxElectionCode (stage plane : Fin 2) :
    (kernel.code.drop (queryBoxElect stage plane+1)).all
      (fun i => Thread.staysPastEvent (queryBoxElect stage plane+1) i.op) = true := by
  fin_cases stage <;> fin_cases plane <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterBoxElectionSegments (stage plane : Fin 2) :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (queryBoxElect stage plane+1 ≤ seg.stop)
      | none => false) = true := by fin_cases stage <;> fin_cases plane <;> kernel_rfl

set_option maxRecDepth 3000 in
private theorem afterBoxElection {l : Launch} {g : Nat} (stage plane : Fin 2) {s t : TState}
    {events : List Event} (h : TraceReach kernel Assumptions.all l g s events t)
    (hs : queryBoxElect stage plane+1 ≤ s.pc) : queryBoxElect stage plane+1 ≤ t.pc := by
  induction h with
  | refl => exact hs
  | tau ht _ ih => exact ih (Thread.eventTailStepOfAudit (afterBoxElectionCode stage plane)
      (afterBoxElectionSegments stage plane) hs (.inl ⟨rfl,ht⟩))
  | event he _ ih => exact ih (Thread.eventTailStepOfAudit (afterBoxElectionCode stage plane)
      (afterBoxElectionSegments stage plane) hs (.inr ⟨_,rfl,he⟩))

/-- A reached loader election has no earlier occurrence if its return crosses a decoded floor. -/
theorem inputElectionFresh {l : Launch} {g pc dst pred : Nat} {s t : TState}
    (hOut : ∀ {u : TState}, u.pc = pc → u.fault = none →
      out kernel Assumptions.all l g u = .ev (.elect 4294967295 (inputElectReturn l g u dst pred)))
    (hPast : ∀ {u v : TState} {events : List Event},
      TraceReach kernel Assumptions.all l g u events v → pc+1 ≤ u.pc → pc+1 ≤ v.pc)
    {events : List Event} (h : TraceReach kernel Assumptions.all l g s events t)
    (ht : t.pc = pc) :
    ∀ mask inst leader, (⟨pc,.elect mask inst leader⟩ : Event) ∉ events := by
  induction h with
  | refl => simp
  | tau _ _ ih => exact ih ht
  | @event s v t es e he hs ih =>
    intro mask inst leader hm
    rcases List.mem_cons.mp hm with hEq | hTail
    · have hPc : s.pc = pc :=
        (estep_source_pc he).symm.trans (congrArg Event.pc hEq).symm
      cases hFault : s.fault with
      | none =>
        obtain ⟨tm,hSource,hFire⟩ := he
        rw [hOut hPc hFault,Out.ev.injEq] at hSource
        subst tm
        obtain ⟨_,lead,_,hRet⟩ := hFire
        have hV := congrArg TState.pc (Option.some.inj hRet)
        change v.pc = s.pc+1 at hV
        have hAfter := hPast hs (by omega)
        omega
      | some f =>
        obtain ⟨tm,hSource,hFire⟩ := he
        simp only [out,hFault,Out.ev.injEq] at hSource
        subst tm
        cases hFire.2
    · exact ih ht _ _ _ hTail

private theorem noEarlierBoxElection {l : Launch} {g : Nat} (stage plane : Fin 2) {s t : TState}
    {events : List Event} (h : TraceReach kernel Assumptions.all l g s events t)
    (ht : t.pc = queryBoxElect stage plane) :
    ∀ mask inst leader, (⟨queryBoxElect stage plane,.elect mask inst leader⟩ : Event) ∉ events := by
  induction h with
  | refl => simp
  | tau _ _ ih => exact ih ht
  | @event s v t es e he hs ih =>
    intro mask inst leader hm
    rcases List.mem_cons.mp hm with hEq | hTail
    · have hPc : s.pc = queryBoxElect stage plane :=
        (estep_source_pc he).symm.trans (congrArg Event.pc hEq).symm
      cases hFault : s.fault with
      | none =>
        obtain ⟨tm,hOut,hFire⟩ := he
        rw [queryBoxElectOut stage plane hPc hFault,Out.ev.injEq] at hOut
        subst tm
        obtain ⟨_,lead,_,hRet⟩ := hFire
        have hV := congrArg TState.pc (Option.some.inj hRet)
        change v.pc = s.pc+1 at hV
        have hAfter := afterBoxElection stage plane hs (by omega)
        omega
      | some f =>
        obtain ⟨tm,hOut,hFire⟩ := he
        simp only [out,hFault,Out.ev.injEq] at hOut
        subst tm
        cases hFire.2
    · exact ih ht _ _ _ hTail

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes col row head barrier policy election endPc : Nat} (hg : g < l.threads)
    (site : Fin 14) (hCol : col < 2^31) (hRow : row < 2^31) (hHead : head < 2^31)
    (hBar : barrier+(inputSite site).barrierOffset < 2^32) (hAlign : barrier%8 = 0)
    (hPolicy : policy < 2^64)
    (hBox : TensorDescriptor.BoxAligned (inputMap p (inputSite site))
      (inputCoordinate col row head)) (hEndPc : (inputSite site).pc+1 = endPc)
    {F : List (Nat × Value)} {G : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (leader : Fin 32) (done : SchedulerWarpReached l X g election G shuffles votes ends)
    (hIssueFrame : ∃ u,
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g leader))
        (done.state leader) u ∧
      At u (inputSite site).pc (inputSiteFacts l (inputSite site) col row head barrier policy ++ F))
    (hSkip : ∀ lane < 32, lane ≠ leader.val → ∃ u,
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) (done.state lane) u ∧
      At u endPc F)
include hp hMax hg site hCol hRow hHead hBar hAlign hPolicy hBox hEndPc leader done hIssueFrame
    hSkip

/-- The elected input issuer records its tensor command while every other lane follows the
local bypass. Both paths return to the same actual warp boundary. -/
theorem inputBoxIssueAfterElectionWithRank :
    (∃ issue, issue.1/l.block = g/l.block ∧ X.get issue =
      some ⟨(inputSite site).pc,.tensorIssue (inputMapAddress p (inputSite site))
        (inputSiteSpec p l issue.1 (inputSite site) col row head barrier)⟩ ∧
        ((X.tr issue.1).take issue.2).countP Execution.isShfl = shuffles) ∧
    Nonempty (SchedulerWarpReached l X g endPc (fun _ => F) shuffles votes ends) := by
  let thread := warpLane l g leader
  let j := done.pos leader
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  obtain ⟨u,hLocal,hU⟩ := hIssueFrame
  have hSame := (Step.sameWarp_lane hBlock hg leader.isLt).1
  obtain ⟨hIssue,hPast,hRest⟩ := loaderInputOfMaximal hp hMax site hSame.1.2.1 hCol hRow hHead
    hBar hAlign hPolicy hBox (hU.mono ((holds_append ..).mp hU.2.2.2.2).1)
    (done.recorded leader leader.isLt) (done.continuation leader leader.isLt)
    ((done.localSteps leader leader.isLt).trans hLocal)
    (done.positive leader leader.isLt) (done.bounded leader leader.isLt)
    (done.released leader leader.isLt)
  have hEnd := ((hU.mono ((holds_append ..).mp hU.2.2.2.2).2).next)
  rw [hEndPc] at hEnd
  have hEvery (lane : Nat) (hl : lane < 32) :
      ∃ pos before state,
        let th := warpLane l g lane
        0 < pos ∧ pos ≤ (X.tr th).length ∧ (pos = (X.tr th).length → Step.Released l X th) ∧
        Run kernel Assumptions.all l th {} ((X.tr th).take pos) (some before) ∧
        Run kernel Assumptions.all l th before ((X.tr th).drop pos) (ends lane) ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l th) before state ∧
        At state endPc
          F ∧
        ((X.tr th).take pos).countP Execution.isShfl = shuffles ∧
        ((X.tr th).take pos).countP isFullWarpVote = votes := by
    by_cases hLeader : lane = leader.val
    · subst lane
      have hs : ((X.tr thread).take (j+1)).countP Execution.isShfl = shuffles :=
        (countP_take_succ_false hIssue rfl).trans (done.ordinals.shfl leader leader.isLt)
      have hv : ((X.tr thread).take (j+1)).countP isFullWarpVote = votes :=
        (countP_take_succ_false hIssue rfl).trans (done.ordinals.vote leader leader.isLt)
      exact ⟨j+1,next u,next u,Nat.succ_pos j,len_of_get hIssue,
        releasedIfLast hIssue (by intro h; cases h),hPast,hRest,.refl,hEnd,hs,hv⟩
    · obtain ⟨w,hw,hW⟩ := hSkip lane hl hLeader
      exact ⟨done.pos lane,done.before lane,w,done.positive lane hl,done.bounded lane hl,
        done.released lane hl,done.recorded lane hl,done.continuation lane hl,
        (done.localSteps lane hl).trans hw,hW,done.ordinals.shfl lane hl,done.ordinals.vote lane hl⟩
  let _ : Inhabited TState := ⟨{}⟩
  choose! pos before state hPos hBound hRelease hPrefix hTail hStep hFrame hSh hV using hEvery
  exact ⟨⟨(thread,j),hSame.1.2.2.symm,hIssue,done.ordinals.shfl leader leader.isLt⟩,
    ⟨⟨⟨pos,before,state,⟨hSh,hV⟩,hTail,hStep,hFrame⟩,hPos,hBound,hRelease,hPrefix⟩⟩⟩

/-- The elected input issuer records its tensor command while every other lane follows the
local bypass. Both paths return to the same actual warp boundary. -/
theorem inputBoxIssueAfterElection :
    (∃ issue, issue.1/l.block = g/l.block ∧ X.TensorIssue issue (inputMapAddress p (inputSite site))
      (inputSiteSpec p l issue.1 (inputSite site) col row head barrier)) ∧
    Nonempty (SchedulerWarpReached l X g endPc (fun _ => F) shuffles votes ends) := by
  obtain ⟨⟨issue,owner,published,_⟩,after⟩ :=
    inputBoxIssueAfterElectionWithRank hp hMax hg site
      hCol hRow hHead hBar hAlign hPolicy hBox hEndPc leader done hIssueFrame hSkip
  exact ⟨⟨issue,owner,_,published⟩,after⟩
end

/-- Each selected query plane is issued by the fully participating warp's elected lane.
The returned checkpoint is the actual warp state immediately after that plane's issue. -/
private theorem queryBoxIssueOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes row head : Nat} (hg : g < l.threads)
    (stage plane : Fin 2) (hRow : queryBoxRow stage row < 2^31) (hHead : head < 2^31)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (queryBoxElect stage plane)
      (fun _ => queryPrimingOperands l row head) shuffles votes ends) :
    (∃ issue, issue.1/l.block = g/l.block ∧
      X.TensorIssue issue p.qMapAddress
        (inputSiteSpec p l issue.1 (inputSite (queryBoxSite stage plane))
          (64*plane.val) (queryBoxRow stage row) head l.sharedBase)) ∧
    Nonempty (SchedulerWarpReached l X g (queryBoxElect stage plane+queryBoxLength stage)
      (fun _ => queryPrimingOperands l row head) shuffles votes ends) := by
  let site := queryBoxSite stage plane
  let col := 64*plane.val
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hFirst (lane : Nat) (hl : lane < 32) (j : Nat) (hj : j < cur.pos lane)
      (mask inst leader : Nat) :
      ¬ X.Elect (warpLane l g lane,j) (queryBoxElect stage plane) mask inst leader := by
    intro he
    have hTrace := (cur.recorded lane hl).returning_reach.append
      (TraceReach.of_local (cur.localSteps lane hl))
    have hGet : ((X.tr (warpLane l g lane)).take (cur.pos lane))[j]? =
        some ⟨queryBoxElect stage plane,.elect mask inst leader⟩ := by
      rwa [List.getElem?_take_of_lt hj]
    exact noEarlierBoxElection stage plane hTrace (cur.checkpoint lane hl).1 mask inst leader
      (List.mem_append_left [] (List.mem_of_getElem? hGet))
  let post (lane : Nat) := queryBoxElectReturn l (warpLane l g lane) (cur.state lane) stage plane
  let G (lane leader : Nat) :=
    (queryBoxElectPred stage plane,.pred (lane == leader)) :: queryPrimingOperands l row head
  obtain ⟨leader,done,_⟩ := cur.consumeElection hp hMax hg post G hFirst
    (fun lane hl =>
      queryBoxElectOut stage plane (cur.checkpoint lane hl).1 (cur.checkpoint lane hl).2.2.2.1)
    (fun lane hl leader => by
      have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      have hF := queryBoxElectedFrame (g := warpLane l g lane) (leader := leader)
        stage plane (cur.checkpoint lane hl)
      rw [hLane] at hF
      exact hF)
  let thread := warpLane l g leader
  have ht := done.checkpoint leader leader.isLt
  have hAt : At (done.state leader) (queryBoxElect stage plane+1)
      ((queryBoxElectPred stage plane,.pred true) :: queryPrimingOperands l row head) := by
    simpa [G] using ht
  obtain ⟨u,hLocal,hU⟩ := queryBoxIssueFrame (g := thread) stage plane hRow hAt
  have hBox : TensorDescriptor.BoxAligned (inputMap p (inputSite site))
      (inputCoordinate col (queryBoxRow stage row) head) := by
    fin_cases stage <;> fin_cases plane <;>
      simp [TensorDescriptor.BoxAligned,inputMap,inputSite,site,queryBoxSite,col,
        Params.qMap,inputCoordinate,TensorDescriptor.Format.bytes]
  have hMap : inputMapAddress p (inputSite site) = p.qMapAddress := by
    fin_cases stage <;> fin_cases plane <;> rfl
  have hBar : l.sharedBase+(inputSite site).barrierOffset < 2^32 := by
    have := hp.shared.2.1
    fin_cases stage <;> fin_cases plane <;>
      simp [site,queryBoxSite,inputSite] <;> omega
  have hAlign : l.sharedBase%8 = 0 := by have := hp.shared.1; omega
  have hCol : col < 2^31 := by have := plane.isLt; dsimp [col]; omega
  have hEndPc : (inputSite site).pc+1 = queryBoxElect stage plane+queryBoxLength stage := by
    fin_cases stage <;> fin_cases plane <;> rfl
  obtain ⟨⟨issue,hCta,hGet⟩,hAfter⟩ := inputBoxIssueAfterElection hp hMax hg site
    hCol hRow hHead hBar hAlign (by decide : 0 < 2^64) hBox hEndPc leader done ⟨u,hLocal,hU⟩
    (fun lane hl hLeader => by
      have hAt : At (done.state lane) (queryBoxElect stage plane+1)
          ((queryBoxElectPred stage plane,.pred false) :: queryPrimingOperands l row head) := by
        simpa only [G,beq_eq_false_iff_ne.mpr hLeader] using done.checkpoint lane hl
      exact queryBoxChoice (g := warpLane l g lane) stage plane false hAt)
  exact ⟨⟨issue,hCta,hMap ▸ hGet⟩,hAfter⟩

/-- Actual loader warp cursor after both opening Q0 boxes. -/
def OpeningBiasReached (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  Nonempty (SchedulerWarpReached l X g 701 (fun _ => [(2535,b32 l.sharedBase)]) shuffles votes ends)

set_option maxRecDepth 100000 in
private theorem queryBoxesOfOperands {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch shuffles votes : Nat} (hg : g < l.threads) (hb : batch < p.batch) (stage : Fin 2)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {ends : Nat → Option TState}
    (start : SchedulerWarpReached l X g (queryBoxElect stage 0)
      (fun _ => [(2535,b32 l.sharedBase)]) shuffles votes ends)
    (hOperands : let coords := assignedCoordinates p batch (g / l.block)
      ∀ lane < 32, Holds (start.state lane).regs
        (queryPrimingOperands l (p.qOffset batch + 256 * coords.1) coords.2)) :
    Nonempty (SchedulerWarpReached l X g (queryBoxElect stage 1 + queryBoxLength stage)
      (fun _ => [(2535,b32 l.sharedBase)]) shuffles votes ends) ∧
    let coords := assignedCoordinates p batch (g/l.block)
    ∀ plane : Fin 2, ∃ issue spec,
      issue.1/l.block = g/l.block ∧ Thread.Loader.QuerySubbox p l X issue stage plane spec ∧
      spec = qInputSpec p (64*plane.val) (queryBoxRow stage (p.qOffset batch+256*coords.1)) coords.2
        ⟨.shared, g/l.block, Mma.qStart l stage+16384*plane.val⟩
        (Thread.Output.queryObject l (g/l.block) stage) false := by
  dsimp only
  let coords := assignedCoordinates p batch (g/l.block)
  let row := p.qOffset batch+256*coords.1
  have hBounds := assignedCoordinates_valid hp hLo hHi
  have hRow : queryBoxRow stage row < 2^31 := by
    have h := hp.packedRow_lt hb hBounds.1
    have := hp.shape.2.2.2.2.2
    have := stage.isLt
    dsimp [row,coords,queryBoxRow]
    omega
  have hHead := hBounds.2.trans hp.heads_signed
  obtain ⟨first⟩ := start.advanceLocal (pc' := queryBoxElect stage 0)
    (G := fun _ => queryPrimingOperands l row coords.2)
    (fun lane hl => ⟨_,.refl,(start.checkpoint lane hl).mono (hOperands lane hl)⟩)
  obtain ⟨left,⟨second⟩⟩ := queryBoxIssueOfMaximal hp hMax hg stage 0 hRow hHead first
  have hNext : queryBoxElect stage 0 + queryBoxLength stage = queryBoxElect stage 1 := by
    fin_cases stage <;> rfl
  obtain ⟨right,⟨done⟩⟩ := queryBoxIssueOfMaximal hp hMax hg stage 1 hRow hHead (hNext ▸ second)
  have hIssue (plane : Fin 2) : ∃ issue, issue.1/l.block = g/l.block ∧
      X.TensorIssue issue p.qMapAddress
        (inputSiteSpec p l issue.1 (inputSite (queryBoxSite stage plane))
          (64*plane.val) (queryBoxRow stage row) coords.2 l.sharedBase) := by
    fin_cases plane
    · exact left
    · exact right
  obtain ⟨doneBase⟩ := done.advanceLocal (G := fun _ => [(2535,b32 l.sharedBase)])
    (fun lane hl => ⟨_,.refl,(done.checkpoint lane hl).mono
      ⟨(done.checkpoint lane hl).2.2.2.2.2.1,trivial⟩⟩)
  refine ⟨⟨doneBase⟩,?_⟩
  intro plane
  obtain ⟨issue,hOwner,hEvent⟩ := hIssue plane
  let spec := inputSiteSpec p l issue.1 (inputSite (queryBoxSite stage plane))
    (64*plane.val) (queryBoxRow stage row) coords.2 l.sharedBase
  refine ⟨issue,spec,hOwner,⟨hEvent,?_,?_,?_,?_,?_,?_⟩,?_⟩
  all_goals first
    | rfl
    | fin_cases stage <;> fin_cases plane <;> rfl
    | fin_cases stage <;> fin_cases plane <;>
        simp [spec,inputSiteSpec,inputSite,queryBoxSite,inputMap,hOwner,Mma.qStart,
          qInputSpec,Thread.Output.queryObject,row,coords,queryBoxRow]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {g batch shuffles votes : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 14) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hSh : 10 + 7 * (batch / 31) + (if 31 * (batch / 31) < batch then 1 else 0) + 1 < shuffles)
include hp hMax writes hg hw hb hLo hHi hSh

/-- The active loader reaches the opening Bias boundary after both Q0 boxes. -/
theorem selectedOpeningBiasEntryOfMaximal {ends : Nat → Option TState}
    (cur : PrimingQueryBoxesReached l X g shuffles votes ends) :
    OpeningBiasReached l X g shuffles votes ends ∧
    let coords := assignedCoordinates p batch (g/l.block)
    ∀ plane : Fin 2, ∃ issue spec,
      issue.1/l.block = g/l.block ∧ Thread.Loader.QuerySubbox p l X issue 0 plane spec ∧
      spec = qInputSpec p (64*plane.val) (p.qOffset batch+256*coords.1) coords.2
        ⟨.shared, g/l.block, Mma.qStart l 0+16384*plane.val⟩
        (Thread.Output.queryObject l (g/l.block) 0) false := by
  obtain ⟨start⟩ := cur
  exact queryBoxesOfOperands hp hMax hg hb 0 hLo hHi start
    (selectedQueryBoxOperandsOfMaximal hp hMax writes hg hw hb hLo hHi
      (by decide) hSh start)

/-- The active loader issues the exact elected Q0 boxes for any selected request. -/
theorem selectedQueryBoxesOfMaximal {ends : Nat → Option TState}
    (cur : PrimingQueryBoxesReached l X g shuffles votes ends) :
    let coords := assignedCoordinates p batch (g/l.block)
    ∀ plane : Fin 2, ∃ issue spec,
      issue.1/l.block = g/l.block ∧ Thread.Loader.QuerySubbox p l X issue 0 plane spec ∧
      spec = qInputSpec p (64*plane.val) (p.qOffset batch+256*coords.1) coords.2
        ⟨.shared, g/l.block, Mma.qStart l 0+16384*plane.val⟩
        (Thread.Output.queryObject l (g/l.block) 0) false :=
  (selectedOpeningBiasEntryOfMaximal hp hMax writes hg hw hb hLo hHi hSh cur).2

omit hp hMax writes hg hw hb hLo hHi hSh in
/-- Actual loader cursor after both Q1 boxes, before checking the second Bias stage. -/
def OpeningSecondBiasReached (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  Nonempty (SchedulerWarpReached l X g 754 (fun _ => [(2535,b32 l.sharedBase)]) shuffles votes ends)

/-- The selected loader issues both Q1 boxes and reaches its second Bias entry. -/
theorem selectedSecondBiasEntryOfMaximal {ends : Nat → Option TState}
    (cur : OpeningSecondQueryBoxesReached l X g shuffles votes ends) :
    OpeningSecondBiasReached l X g shuffles votes ends ∧
    (let coords := assignedCoordinates p batch (g / l.block)
    ∀ plane : Fin 2, ∃ issue spec,
      issue.1 / l.block = g / l.block ∧ Thread.Loader.QuerySubbox p l X issue 1 plane spec ∧
      spec = qInputSpec p (64*plane.val) (p.qOffset batch + 256*coords.1 + 128) coords.2
        ⟨.shared, g/l.block, Mma.qStart l 1+16384*plane.val⟩
        (Thread.Output.queryObject l (g/l.block) 1) false) := by
  obtain ⟨start⟩ := cur
  exact queryBoxesOfOperands hp hMax hg hb 1 hLo hHi start
    (selectedOpeningQueryOperandsOfMaximal hp hMax writes hg hw hb hLo hHi
      (by decide) hSh start)

/-- The active loader issues the two opening Q1 boxes for its exact selected request. -/
theorem selectedSecondQueryBoxesOfMaximal {ends : Nat → Option TState}
    (cur : OpeningSecondQueryBoxesReached l X g shuffles votes ends) :
    let coords := assignedCoordinates p batch (g / l.block)
    ∀ plane : Fin 2, ∃ issue spec,
      issue.1 / l.block = g / l.block ∧ Thread.Loader.QuerySubbox p l X issue 1 plane spec ∧
      spec = qInputSpec p (64*plane.val) (p.qOffset batch + 256*coords.1 + 128) coords.2
        ⟨.shared, g/l.block, Mma.qStart l 1+16384*plane.val⟩
        (Thread.Output.queryObject l (g/l.block) 1) false :=
  (selectedSecondBiasEntryOfMaximal hp hMax writes hg hw hb hLo hHi hSh cur).2

end PTX.Kernels.TmlFa4Fwd.Loader
