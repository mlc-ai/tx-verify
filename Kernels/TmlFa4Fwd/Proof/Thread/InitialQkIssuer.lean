-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyOperandFrame
import Kernels.TmlFa4Fwd.Proof.MmaInitialValueCursor
import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut
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
import Lemmas.Flow.Tc

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

private def initialQkElect (stage : Fin 2) : Fin 20 := ⟨2 * stage.val,by have := stage.isLt; omega⟩

set_option maxRecDepth 100000 in
private theorem initialQkElectionReached {l : Launch} (stage : Fin 2) (frag : Fin 8)
    {g : Nat} {s : TState} {es : List Event} {vs : List Visit} {e : Event}
    (hs : At s 1908 [(1062,b32 12)]) (hw : Walk kernel Assumptions.all l g s es vs)
    (he : e ∈ es) (hPc : e.pc = qkPc (initialQkBlock stage) + frag.val) :
    ∃ u pre tail visits, es = pre ++ tail ∧ At u (electSite (initialQkElect stage)).pc [] ∧
      u.regs 1062 = some (b32 12) ∧ Walk kernel Assumptions.all l g u tail visits ∧
      e ∈ tail := by
  let locate (evt : Event) := if evt.pc = e.pc then some evt else none
  have hRange : 2140 ≤ e.pc ∧ e.pc < 2548 := by
    rw [hPc]
    fin_cases stage <;> fin_cases frag <;> decide
  have hSome : es.filterMap locate ≠ [] := by
    have hm : e ∈ es.filterMap locate := List.mem_filterMap.mpr ⟨e,he,by simp [locate]⟩
    exact fun hn => by rw [hn] at hm; cases hm
  obtain ⟨t,pre,rest,visits,hExit,ht,hSplit,hPre,hWalk⟩ :=
    requireReadyIntervalWith locate 0 (fun evt h => by
      have hHi : evt.pc < 2140 := h.2
      simp [locate,show evt.pc ≠ e.pc by omega])
      (by rw [hs.1]; decide) ⟨rfl,hs.2⟩ (by simp) (by simp) hw hSome
  have hRest : e ∈ rest := by
    rw [hSplit] at he
    apply (List.mem_append.mp he).resolve_left
    intro h
    have hBad := List.filterMap_eq_nil_iff.mp hPre e h
    simp [locate] at hBad
  have hSite : t.pc = 2140 ∨ t.pc = 2763 := by simpa [readyInterval] using hExit
  rcases hSite with hSite | hSite
  swap
  · have hProjection : rest.filterMap locate ≠ [] := by
      have hm : e ∈ rest.filterMap locate := List.mem_filterMap.mpr ⟨e,hRest,by simp [locate]⟩
      exact fun hn => by rw [hn] at hm; cases hm
    obtain ⟨u,skip,suffix,post,huExit,huAt,hSplit',hSkip,huW⟩ :=
      requireReadyIntervalWith locate 8 (fun evt h => by
        have hLo : 2548 ≤ evt.pc := h.1
        simp [locate,show evt.pc ≠ e.pc by omega])
        (by rw [hSite]; decide) ht (by simp) (by decide) hWalk hProjection
    have hU : u.pc = 3099 := by simpa [readyInterval] using huExit
    have hFound : e ∈ suffix := by
      rw [hSplit'] at hRest
      apply (List.mem_append.mp hRest).resolve_left
      intro h
      have hBad := List.filterMap_eq_nil_iff.mp hSkip e h
      simp [locate] at hBad
    have hPc' := mmaEpilogueExitEvents hU huAt.2.2.2.1 (.inl rfl) huAt.2.2.2.2.1 huW e hFound
    omega
  let site := (electSite (initialQkElect stage)).pc
  have hBounds : 2140 ≤ site ∧ site < e.pc := by
    rw [hPc]
    fin_cases stage <;> fin_cases frag <;> decide
  have hAudit : ((kernel.code.drop 2140).take (site-2140)).all
      (pvCutCode 2140 site [1062]) = true := by fin_cases stage <;> kernel_rfl
  have hShape : RoleShape t ∧ t.regs 1062 = some (b32 12) :=
    ⟨⟨ht.2.1.symm ▸ Nat.zero_le _,ht.2.2.1,fun _ => ht.2.1⟩,ht.2.2.2.2.1⟩
  obtain ⟨u,skip,suffix,post,hSplit',hu,hUShape,_,hUWalk,hUMem,_⟩ :=
    pvWalkCut (by decide) (show site < 2768 by omega) hAudit hWalk
      (by rw [hSite]; exact ⟨le_rfl,hBounds.1⟩) hShape ht.2.2.2.2 hRest hBounds.2.le
  have huAt : At u site [] :=
    ⟨hu,hUShape.1.2.2 (by omega),hUShape.1.2.1,
      normalBeforeLaterEvent hUWalk hUMem (by omega),trivial⟩
  exact ⟨u,pre++skip,suffix,post,by rw [hSplit,hSplit',List.append_assoc],
    huAt,hUShape.2,hUWalk,hUMem⟩

set_option maxRecDepth 100000 in
/-- A real initial QK instruction can only fire on the lane selected at its bank's election. -/
theorem initialQkIssueLeader {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) (frag : Fin 8) {g index d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat}
    (he : X.get (g,index) = some
      ⟨qkPc (initialQkBlock stage)+frag.val,.tc (.mma d op accum mask)⟩) :
    ∃ j inst leader, X.Elect (g,j) (2153+62*stage.val) (2^32-1) inst leader ∧
      laneOf l g = leader := by
  let block := initialQkBlock stage
  let issue := qkPc block+frag.val
  let e : Event := ⟨issue,.tc (.mma d op accum mask)⟩
  let vote := initialQkElect stage
  let site := (electSite vote).pc
  have hBounds : 2145 ≤ issue ∧ issue < 2768 ∧ 1907 ≤ site+1 ∧ site < issue := by
    fin_cases stage <;> fin_cases frag <;> decide
  obtain ⟨base,s,_,hBase,hs,hWalk⟩ := initialMmaTrace hp hX he hBounds.1 hBounds.2.1
  have hMem : e ∈ (X.tr g).drop (base+1) := by
    apply List.mem_of_getElem? (i := index-(base+1))
    rwa [List.getElem?_drop,Nat.add_sub_of_le hBase]
  obtain ⟨u,pre,tail,_,hSplit,hu,hRole,hUWalk,hUMem⟩ :=
    initialQkElectionReached stage frag (hs.mono ⟨hs.2.2.2.2.1,trivial⟩) hWalk hMem rfl
  have hOut := electTemplate (l := l) (g := g) vote hu
  have hPC : u.pc < e.pc := by rw [hu.1]; exact hBounds.2.2.2
  obtain ⟨v,_,rest,_,hTail,hFires,_,hvWalk,hVMem⟩ := pvWalkEvent hUWalk hOut hUMem hPC
  obtain ⟨inst,leader,rfl,hAfter⟩ := hFires
  obtain rfl := Option.some.inj hAfter
  let v := electState l g u vote leader
  have hResult : (electSite vote).result = none := by fin_cases stage <;> decide
  have hPred : (electSite vote).pred = qkGuard block := by fin_cases stage <;> decide
  have hv := electStateFrame (l := l) (g := g) vote hu leader (by simp) (by simp)
  rw [hPred] at hv
  have hvRole : v.regs 1062 = some (b32 12) := by
    have hNe : 1062 ≠ (electSite vote).pred := by fin_cases stage <;> decide
    simp [v,electState,hResult,next,setReg,hNe,hRole]
  have hShape : RoleShape v ∧ v.regs 1062 = some (b32 12) :=
    ⟨⟨hv.2.1.symm ▸ Nat.zero_le _,hv.2.2.1,fun _ => hv.2.1⟩,hvRole⟩
  let F : List (Nat × Value) := [(qkGuard block,.pred (laneOf l g == leader))]
  have hAudit : ((kernel.code.drop (site+1)).take (issue-(site+1))).all
      (pvCutCode (site+1) issue (F.map Prod.fst)) = true := by
    fin_cases stage <;> fin_cases frag <;> kernel_rfl
  obtain ⟨w,_,suffix,post,_,hw,hWShape,hWReg,hW,hWMem,_⟩ :=
    pvWalkCut (F := F) hBounds.2.2.1 hBounds.2.1 hAudit hvWalk
      (by rw [show v.pc = site+1 from hv.1]; omega) hShape hv.2.2.2.2 hVMem le_rfl
  obtain ⟨z,hStep⟩ := qkInitialStepAtCheckpoint stage frag hw hW hWMem
  have hLeader : laneOf l g = leader := by
    by_contra hNe
    have hGuard := hWReg.1
    change w.regs (qkGuard block) = some (.pred (laneOf l g == leader)) at hGuard
    rw [beq_eq_false_iff_ne.mpr hNe] at hGuard
    obtain ⟨tm,hEv,hFire⟩ := hStep
    by_cases hNormal : w.fault = none
    · have hCode := qkCode block frag
      have hw' : w.pc = qkPc block+frag.val := hw
      simp only [out,hNormal,hw',hCode,guardHolds,readReg,hGuard,pure,Except.pure,
        bind,Except.bind] at hEv
      cases hEv
    · obtain ⟨reason,hFault⟩ := Option.ne_none_iff_exists'.mp hNormal
      simp only [out,hFault,Out.ev.injEq] at hEv
      subst tm
      cases hFire.2
  have hEvent : X.Elect (g,base+1+pre.length) site (2^32-1) inst leader := by
    unfold Execution.Elect
    change (X.tr g)[base+1+pre.length]? = _
    rw [← List.getElem?_drop,hSplit,List.getElem?_append_right le_rfl,Nat.sub_self,hTail]
    rw [hu.1]
    rfl
  have hSite : site = 2153+62*stage.val := by fin_cases stage <;> decide
  exact ⟨_,inst,leader,hSite ▸ hEvent,hLeader⟩

private theorem initialQkIssueWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) (frag : Fin 8) {i : EvId} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat}
    (he : X.get i = some ⟨qkPc (initialQkBlock stage)+frag.val,.tc (.mma d op accum mask)⟩) :
    warpIndex l i.1 = 12 := by
  let pc := qkPc (initialQkBlock stage)+frag.val
  have hAudit : 173 < pc ∧ pc ∉ registerHintSites ∧ 2197 ≤ pc ∧ pc < 2768 := by
    fin_cases stage <;> fin_cases frag <;> decide
  have hRole := roleBodyPcOfEvent hp hX he hAudit.1 hAudit.2.1
  change roleBodyPc (warpIndex l i.1) pc at hRole
  have hBounds := hAudit.2.2
  rcases hRole with hReturn | hRole
  · omega
  · split_ifs at hRole <;> omega

/-- Two observed initial issues of one fragment in a CTA are the same event. -/
theorem initialQkIssueUnique {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) (frag : Fin 8) {i j : EvId} {d d' : Nat} {op op' : TcMma.OperandSpec}
    {accum accum' : Bool} {mask mask' : List Nat}
    (hi : X.get i = some ⟨qkPc (initialQkBlock stage)+frag.val,.tc (.mma d op accum mask)⟩)
    (hj : X.get j = some ⟨qkPc (initialQkBlock stage)+frag.val,.tc (.mma d' op' accum' mask')⟩)
    (hCta : i.1 / l.block = j.1 / l.block) : i = j := by
  obtain ⟨g,a⟩ := i
  obtain ⟨h,b⟩ := j
  have hWarp : SameWarp l g h := ⟨⟨event_thread_lt hX hi,event_thread_lt hX hj,hCta⟩,
    (initialQkIssueWarp hp hX stage frag hi).trans (initialQkIssueWarp hp hX stage frag hj).symm⟩
  obtain ⟨_,_,leader,hI,hILane⟩ := initialQkIssueLeader hp hX stage frag hi
  obtain ⟨_,_,leader',hJ,hJLane⟩ := initialQkIssueLeader hp hX stage frag hj
  have hLane := sameWarp_eq_of_lane_eq hWarp
    (hILane.trans ((sameLeader hX hWarp hI hJ).trans hJLane.symm))
  subst h
  have hIndex := initialQkIssueIndexUnique hp hX stage frag hi hj
  subst b
  rfl

end PTX.Kernels.TmlFa4Fwd.Thread
