-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasProgress
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

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame Prologue Epilogue

private def openingBiasSite (half : Fin 2) : Fin 14 := ⟨2+half.val,by have := half.isLt; omega⟩
private def openingBiasElect (half : Fin 2) : Nat := 712+8*half.val
private def openingBiasDst (half : Fin 2) : Nat := 1901+3*half.val
private def openingBiasPred (half : Fin 2) : Nat := 148+2*half.val
private def openingBiasCol (half : Fin 2) : Nat := 1152+64*half.val

private def openingBiasBoxFrame (l : Launch) (row head : Nat) : List (Nat × Value) :=
  (1114,b32 (l.sharedBase+320)) :: openingBiasOperands l row head

private theorem openingBiasBoxElectOut {l : Launch} {g : Nat} {s : TState} (half : Fin 2)
    (hPc : s.pc = openingBiasElect half) (hFault : s.fault = none) :
    out kernel Assumptions.all l g s = .ev (.elect 4294967295
      (inputElectReturn l g s (openingBiasDst half) (openingBiasPred half))) := by
  apply inputElectOut hPc hFault
  · fin_cases half <;> decide
  · fin_cases half <;> decide
  · fin_cases half
    · exact Flow.code_712
    · exact Flow.code_720

set_option maxRecDepth 15000 in
private theorem openingBiasElectionFloor {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (half : Fin 2)
    (h : TraceReach kernel Assumptions.all l g s events t) (hs : openingBiasElect half+1 ≤ s.pc) :
    openingBiasElect half+1 ≤ t.pc := by
  have hCode : (kernel.code.drop (openingBiasElect half+1)).all
      (fun i => Thread.staysPastEvent (openingBiasElect half+1) i.op) = true := by
    fin_cases half <;> kernel_rfl
  have hSegments : Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (openingBiasElect half+1 ≤ seg.stop)
      | none => false) = true := by fin_cases half <;> kernel_rfl
  induction h with
  | refl => exact hs
  | tau ht _ ih => exact ih (Thread.eventTailStepOfAudit hCode hSegments hs (.inl ⟨rfl,ht⟩))
  | event he _ ih => exact ih (Thread.eventTailStepOfAudit hCode hSegments hs (.inr ⟨_,rfl,he⟩))

private theorem openingBiasChoice {l : Launch} {g row head : Nat} (half : Fin 2)
    (takeBox : Bool) {s : TState}
    (hs : At s (openingBiasElect half+1)
      ((openingBiasPred half,.pred takeBox) :: openingBiasBoxFrame l row head)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if takeBox then openingBiasElect half+3 else openingBiasElect half+8)
        (openingBiasBoxFrame l row head) := by
  apply inputBoxChoice takeBox ?_ ?_ ?_ ?_ ?_ hs
  · fin_cases half <;> decide
  · fin_cases half <;> decide
  · fin_cases half
    · exact Flow.code_713
    · exact Flow.code_721
  · fin_cases half
    · exact Flow.code_714
    · exact Flow.code_722
  · fin_cases half <;> simp [openingBiasBoxFrame,openingBiasOperands,openingBiasPred]

private theorem openingBiasIssueFrame {l : Launch} {g row head : Nat} (half : Fin 2) {s : TState}
    (hs : At s (openingBiasElect half+1)
      ((openingBiasPred half,.pred true) :: openingBiasBoxFrame l row head)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (inputSite (openingBiasSite half)).pc
        (inputSiteFacts l (inputSite (openingBiasSite half)) (openingBiasCol half)
          row head (l.sharedBase+320) 0 ++ openingBiasBoxFrame l row head) := by
  obtain ⟨v,hv,hV⟩ := openingBiasChoice (g := g) half true hs
  have hPrep : Seg kernel [] l g 4 (openingBiasElect half+3)
      (openingBiasBoxFrame l row head) (inputSite (openingBiasSite half)).pc
      (inputSiteFacts l (inputSite (openingBiasSite half)) (openingBiasCol half) row head
        (l.sharedBase+320) 0 ++ openingBiasBoxFrame l row head) := by
    fin_cases half <;> intro t ht <;>
      dsimp [openingBiasElect,openingBiasBoxFrame,openingBiasOperands,openingBiasSite,
        openingBiasCol,inputSiteFacts,inputSite,inputParam] at ht ⊢
    all_goals seg_fp ht using rfl
  obtain ⟨u,hu,hU⟩ := hPrep v hV
  have hlo : 174 ≤ openingBiasElect half+3 := by fin_cases half <;> decide
  have hhi : openingBiasElect half+3+4 ≤ 1906 := by fin_cases half <;> decide
  have hRun := (loaderLinear (regs := []) hlo hhi hV.1
    (List.all_eq_true.mpr fun _ _ => rfl)
    (by fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)) hu).1
  exact ⟨u,hv.trans (run_rtg hRun),hU⟩

private theorem openingBiasBoxOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes row head : Nat} (hg : g < l.threads)
    (half : Fin 2) (hRow : row < 2^31) (hHead : head < 2^31)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (openingBiasElect half)
      (fun _ => openingBiasBoxFrame l row head) shuffles votes ends) :
    (∃ issue, issue.1/l.block = g/l.block ∧
      X.TensorIssue issue p.biasMapAddress
        (inputSiteSpec p l issue.1 (inputSite (openingBiasSite half))
          (openingBiasCol half) row head (l.sharedBase+320))) ∧
    Nonempty (SchedulerWarpReached l X g (openingBiasElect half+8)
      (fun _ => openingBiasBoxFrame l row head) shuffles votes ends) := by
  let post (lane : Nat) := inputElectReturn l (warpLane l g lane) (cur.state lane)
    (openingBiasDst half) (openingBiasPred half)
  let G (lane leader : Nat) :=
    (openingBiasPred half,.pred (lane == leader)) :: openingBiasBoxFrame l row head
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hFirst (lane : Nat) (hl : lane < 32) (j : Nat) (hj : j < cur.pos lane)
      (mask inst leader : Nat) :
      ¬ X.Elect (warpLane l g lane,j) (openingBiasElect half) mask inst leader := by
    intro he
    have hTrace := (cur.recorded lane hl).returning_reach.append
      (TraceReach.of_local (cur.localSteps lane hl))
    have hGet : ((X.tr (warpLane l g lane)).take (cur.pos lane))[j]? =
        some ⟨openingBiasElect half,.elect mask inst leader⟩ := by
      rwa [List.getElem?_take_of_lt hj]
    exact inputElectionFresh (openingBiasBoxElectOut half) (openingBiasElectionFloor half) hTrace
      (cur.checkpoint lane hl).1 mask inst leader
      (List.mem_append_left [] (List.mem_of_getElem? hGet))
  obtain ⟨leader,done,_⟩ := cur.consumeElection hp hMax hg post G hFirst
    (fun lane hl => openingBiasBoxElectOut half
      (cur.checkpoint lane hl).1 (cur.checkpoint lane hl).2.2.2.1)
    (fun lane hl leader => by
      have hs := cur.checkpoint lane hl
      have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      rcases hs.2.2.2.2 with ⟨hReady,hPtr,hBase,hRow,hHead,hResid,_⟩
      refine ⟨by simp [post,inputElectReturn,next,setReg,hs.1],
        hs.2.1,hs.2.2.1,hs.2.2.2.1,?_⟩
      fin_cases half <;>
        simp [G,Holds,openingBiasBoxFrame,openingBiasOperands,post,inputElectReturn,
          openingBiasPred,openingBiasDst,next,setReg,hLane,hReady,hPtr,hBase,hRow,hHead,hResid])
  let site := openingBiasSite half
  let col := openingBiasCol half
  have hCol : col < 2^31 := by fin_cases half <;> decide
  have hBar : l.sharedBase+320+(inputSite site).barrierOffset < 2^32 := by
    have := hp.shared.2.1
    fin_cases half <;> simp [site,openingBiasSite,inputSite] <;> omega
  have hAlign : (l.sharedBase+320)%8 = 0 := by have := hp.shared.1; omega
  have hBox : TensorDescriptor.BoxAligned (inputMap p (inputSite site))
      (inputCoordinate col row head) := by
    fin_cases half <;>
      simp [TensorDescriptor.BoxAligned,inputMap,inputSite,site,openingBiasSite,col,openingBiasCol,
        Params.biasMap,inputCoordinate,TensorDescriptor.Format.bytes]
  have hEndPc : (inputSite site).pc+1 = openingBiasElect half+8 := by fin_cases half <;> rfl
  have hMap : inputMapAddress p (inputSite site) = p.biasMapAddress := by fin_cases half <;> rfl
  obtain ⟨⟨issue,hCta,hGet⟩,hAfter⟩ := inputBoxIssueAfterElection hp hMax hg site
    hCol hRow hHead hBar hAlign (by decide : 0 < 2^64) hBox hEndPc leader done
    (openingBiasIssueFrame (g := warpLane l g leader) half (by
      simpa [G] using done.checkpoint leader leader.isLt))
    (fun lane hl hLeader => openingBiasChoice (g := warpLane l g lane) half false (by
      simpa only [G,beq_eq_false_iff_ne.mpr hLeader] using done.checkpoint lane hl))
  exact ⟨⟨issue,hCta,hMap ▸ hGet⟩,hAfter⟩

/-- Both opening Bias halves issue with the selected operands, reaching the second query cursor. -/
theorem openingBiasBoxesOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    {g batch shuffles votes : Nat} (hg : g < l.threads) (hw : warpIndex l g = 14)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSh : 10+7*(batch/31)+(if 31*(batch/31)<batch then 1 else 0)+1 < shuffles)
    {ends : Nat → Option TState} (hReached : OpeningBiasBoxesReached l X g shuffles votes ends) :
    OpeningSecondQueryReached l X g shuffles votes ends ∧
      let coords := assignedCoordinates p batch (g/l.block)
      ∀ half : Fin 2, ∃ issue, issue.1/l.block = g/l.block ∧
        X.TensorIssue issue p.biasMapAddress
          (biasInputSpec p (1152+64*half.val) (p.qOffset batch+256*coords.1) coords.2
            ⟨.shared,g/l.block,l.sharedBase+(166912+16384*half.val)⟩
            (Thread.Loader.biasReadyObject l (g/l.block) 0) false) := by
  obtain ⟨cur⟩ := hReached
  let coords := assignedCoordinates p batch (g/l.block)
  let row := p.qOffset batch+256*coords.1
  have hBounds := assignedCoordinates_valid hp hLo hHi
  have hRow : row < 2^31 := by
    have h := hp.packedRow_lt hb hBounds.1
    have := hp.shape.2.2.2.2.2
    dsimp [row,coords]
    omega
  have hHead := hBounds.2.trans hp.heads_signed
  have hOperands := selectedOpeningBiasOperandsOfMaximal hp hMax writes hg hw hb hLo hHi
    (by decide) hSh cur
  obtain ⟨first⟩ := cur.advanceLocal (pc' := 712)
    (G := fun _ => openingBiasBoxFrame l row coords.2)
    (fun lane hl => ⟨_,.refl,(cur.checkpoint lane hl).mono
      ⟨(cur.checkpoint lane hl).2.2.2.2.1,hOperands lane hl⟩⟩)
  obtain ⟨left,⟨second⟩⟩ := openingBiasBoxOfMaximal hp hMax hg 0 hRow hHead first
  obtain ⟨right,⟨done⟩⟩ := openingBiasBoxOfMaximal hp hMax hg 1 hRow hHead second
  have hDone := done.advanceLocal (G := fun _ => secondQueryBaseFrame l)
    (fun lane hl => ⟨_,.refl,(done.checkpoint lane hl).mono
      ⟨(done.checkpoint lane hl).2.2.2.2.2.2.1,trivial⟩⟩)
  refine ⟨hDone,?_⟩
  dsimp only
  intro half
  have hIssue : ∃ issue, issue.1/l.block = g/l.block ∧
      X.TensorIssue issue p.biasMapAddress
        (inputSiteSpec p l issue.1 (inputSite (openingBiasSite half))
        (openingBiasCol half) row coords.2 (l.sharedBase+320)) := by
    fin_cases half
    · exact left
    · exact right
  obtain ⟨issue,hCta,hGet⟩ := hIssue
  refine ⟨issue,hCta,?_⟩
  fin_cases half <;>
    simpa [inputSiteSpec,inputSite,inputMap,openingBiasSite,openingBiasCol,biasInputSpec,
      Thread.Loader.biasReadyObject,hCta,row,coords] using hGet

end PTX.Kernels.TmlFa4Fwd.Loader
