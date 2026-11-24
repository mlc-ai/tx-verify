-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSecondBiasProgress
import Kernels.TmlFa4Fwd.Flow.Code.Part011
import Kernels.TmlFa4Fwd.Flow.Code.Part012
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

private def secondBiasSite (half : Fin 2) : Fin 14 := ⟨6+half.val,by have := half.isLt; omega⟩
private def secondBiasElect (half : Fin 2) : Nat := 765+7*half.val
private def secondBiasDst (half : Fin 2) : Nat := 1921+2*half.val
private def secondBiasPred (half : Fin 2) : Nat := 160+2*half.val
private def secondBiasCol (half : Fin 2) : Nat := 1152+64*half.val

private def secondBiasBranchStart (half : Fin 2) : Nat := secondBiasElect half+half.val
private def secondBiasAfterBox (half : Fin 2) : Nat := 772+8*half.val

def secondBiasBoxFrame (l : Launch) (row head : Nat) : List (Nat × Value) :=
  [(7289,.ptr 64 false (.param (param 11)) 0),(2535,b32 l.sharedBase),
   (1115,b32 row),(7169,b32 head)]

private theorem secondBiasBoxElectOut {l : Launch} {g : Nat} {s : TState} (half : Fin 2)
    (hPc : s.pc = secondBiasElect half) (hFault : s.fault = none) :
    out kernel Assumptions.all l g s = .ev (.elect 4294967295
      (inputElectReturn l g s (secondBiasDst half) (secondBiasPred half))) := by
  apply inputElectOut hPc hFault
  · fin_cases half <;> decide
  · fin_cases half <;> decide
  · fin_cases half
    · exact Flow.code_765
    · exact Flow.code_772

set_option maxRecDepth 15000 in
private theorem secondBiasElectionFloor {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (half : Fin 2)
    (h : TraceReach kernel Assumptions.all l g s events t) (hs : secondBiasElect half+1 ≤ s.pc) :
    secondBiasElect half+1 ≤ t.pc := by
  have hCode : (kernel.code.drop (secondBiasElect half+1)).all
      (fun i => Thread.staysPastEvent (secondBiasElect half+1) i.op) = true := by
    fin_cases half <;> kernel_rfl
  have hSegments : Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (secondBiasElect half+1 ≤ seg.stop)
      | none => false) = true := by fin_cases half <;> kernel_rfl
  induction h with
  | refl => exact hs
  | tau ht _ ih => exact ih (Thread.eventTailStepOfAudit hCode hSegments hs (.inl ⟨rfl,ht⟩))
  | event he _ ih => exact ih (Thread.eventTailStepOfAudit hCode hSegments hs (.inr ⟨_,rfl,he⟩))

private theorem secondBiasChoice {l : Launch} {g row head : Nat} (half : Fin 2)
    (takeBox : Bool) {s : TState}
    (hs : At s (secondBiasElect half+1)
      ((secondBiasPred half,.pred takeBox) :: secondBiasBoxFrame l row head)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if takeBox then secondBiasBranchStart half+3 else secondBiasAfterBox half)
        (secondBiasBoxFrame l row head) := by
  have hReady : ∃ t, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t ∧
      At t (secondBiasBranchStart half+1)
        ((secondBiasPred half,.pred takeBox) :: secondBiasBoxFrame l row head) := by
    fin_cases half
    · exact ⟨s,.refl,hs⟩
    · have hSeg : Seg kernel [] l g 1 773
          ((secondBiasPred 1,.pred takeBox) :: secondBiasBoxFrame l row head)
          774 ((7177,b32 0) :: (secondBiasPred 1,.pred takeBox) ::
            secondBiasBoxFrame l row head) := by
        intro t ht
        dsimp [secondBiasPred,secondBiasBoxFrame] at *
        seg_fp ht using rfl
      obtain ⟨t,ht,hAt⟩ := hSeg s hs
      exact ⟨t,run_rtg ((loaderLinear (regs := []) (by decide) (by decide) hs.1
        (by simp) (by decide) ht).1),hAt.mono hAt.2.2.2.2.2⟩
  obtain ⟨t,ht,hT⟩ := hReady
  obtain ⟨w,hw,hAt⟩ := inputBoxChoice takeBox (pc := secondBiasBranchStart half)
    (endPc := secondBiasAfterBox half) (by fin_cases half <;> decide)
    (by fin_cases half <;> decide)
    (by
      fin_cases half
      · exact Flow.code_766
      · exact Flow.code_774)
    (by
      fin_cases half
      · exact Flow.code_767
      · exact Flow.code_775)
    (by fin_cases half <;> simp [secondBiasBoxFrame,secondBiasPred]) hT
  exact ⟨w,ht.trans hw,hAt⟩

private theorem secondBiasIssueFrame {l : Launch} {g row head : Nat} (half : Fin 2) {s : TState}
    (hs : At s (secondBiasElect half+1)
      ((secondBiasPred half,.pred true) :: secondBiasBoxFrame l row head)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (inputSite (secondBiasSite half)).pc
        (inputSiteFacts l (inputSite (secondBiasSite half)) (secondBiasCol half)
          row head l.sharedBase 0 ++ secondBiasBoxFrame l row head) := by
  obtain ⟨v,hv,hV⟩ := secondBiasChoice (g := g) half true hs
  have hPrep : Seg kernel [] l g 3 (secondBiasBranchStart half+3)
      (secondBiasBoxFrame l row head) (inputSite (secondBiasSite half)).pc
      (inputSiteFacts l (inputSite (secondBiasSite half)) (secondBiasCol half) row head
        l.sharedBase 0 ++ secondBiasBoxFrame l row head) := by
    fin_cases half <;> intro t ht <;>
      dsimp [secondBiasBranchStart,secondBiasElect,secondBiasBoxFrame,secondBiasSite,
        secondBiasCol,inputSiteFacts,inputSite,inputParam] at ht ⊢
    all_goals seg_fp ht using rfl
  obtain ⟨u,hu,hU⟩ := hPrep v hV
  have hlo : 174 ≤ secondBiasBranchStart half+3 := by fin_cases half <;> decide
  have hhi : secondBiasBranchStart half+3+3 ≤ 1906 := by fin_cases half <;> decide
  have hRun := (loaderLinear (regs := []) hlo hhi hV.1
    (List.all_eq_true.mpr fun _ _ => rfl)
    (by fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)) hu).1
  exact ⟨u,hv.trans (run_rtg hRun),hU⟩

private theorem secondBiasBoxOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes row head : Nat} (hg : g < l.threads)
    (half : Fin 2) (hRow : row < 2^31) (hHead : head < 2^31)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (secondBiasElect half)
      (fun _ => secondBiasBoxFrame l row head) shuffles votes ends) :
    (∃ issue, issue.1/l.block = g/l.block ∧
      X.TensorIssue issue p.biasMapAddress
        (inputSiteSpec p l issue.1 (inputSite (secondBiasSite half))
          (secondBiasCol half) row head l.sharedBase)) ∧
    Nonempty (SchedulerWarpReached l X g (secondBiasAfterBox half)
      (fun _ => secondBiasBoxFrame l row head) shuffles votes ends) := by
  let post (lane : Nat) := inputElectReturn l (warpLane l g lane) (cur.state lane)
    (secondBiasDst half) (secondBiasPred half)
  let G (lane leader : Nat) :=
    (secondBiasPred half,.pred (lane == leader)) :: secondBiasBoxFrame l row head
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hFirst (lane : Nat) (hl : lane < 32) (j : Nat) (hj : j < cur.pos lane)
      (mask inst leader : Nat) :
      ¬ X.Elect (warpLane l g lane,j) (secondBiasElect half) mask inst leader := by
    intro he
    have hTrace := (cur.recorded lane hl).returning_reach.append
      (TraceReach.of_local (cur.localSteps lane hl))
    have hGet : ((X.tr (warpLane l g lane)).take (cur.pos lane))[j]? =
        some ⟨secondBiasElect half,.elect mask inst leader⟩ := by
      rwa [List.getElem?_take_of_lt hj]
    exact inputElectionFresh (secondBiasBoxElectOut half) (secondBiasElectionFloor half) hTrace
      (cur.checkpoint lane hl).1 mask inst leader
      (List.mem_append_left [] (List.mem_of_getElem? hGet))
  obtain ⟨leader,done,_⟩ := cur.consumeElection hp hMax hg post G hFirst
    (fun lane hl => secondBiasBoxElectOut half
      (cur.checkpoint lane hl).1 (cur.checkpoint lane hl).2.2.2.1)
    (fun lane hl leader => by
      have hs := cur.checkpoint lane hl
      have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      rcases hs.2.2.2.2 with ⟨hPtr,hBase,hRow,hHead,_⟩
      refine ⟨by simp [post,inputElectReturn,next,setReg,hs.1],
        hs.2.1,hs.2.2.1,hs.2.2.2.1,?_⟩
      fin_cases half <;>
        simp [G,Holds,secondBiasBoxFrame,post,inputElectReturn,
          secondBiasPred,secondBiasDst,next,setReg,hLane,hPtr,hBase,hRow,hHead])
  let site := secondBiasSite half
  let col := secondBiasCol half
  have hCol : col < 2^31 := by fin_cases half <;> decide
  have hBar : l.sharedBase+(inputSite site).barrierOffset < 2^32 := by
    have := hp.shared.2.1
    fin_cases half <;> simp [site,secondBiasSite,inputSite] <;> omega
  have hAlign : l.sharedBase%8 = 0 := by have := hp.shared.1; omega
  have hBox : TensorDescriptor.BoxAligned (inputMap p (inputSite site))
      (inputCoordinate col row head) := by
    fin_cases half <;>
      simp [TensorDescriptor.BoxAligned,inputMap,inputSite,site,secondBiasSite,col,secondBiasCol,
        Params.biasMap,inputCoordinate,TensorDescriptor.Format.bytes]
  have hEndPc : (inputSite site).pc+1 = secondBiasAfterBox half := by fin_cases half <;> rfl
  have hMap : inputMapAddress p (inputSite site) = p.biasMapAddress := by fin_cases half <;> rfl
  obtain ⟨⟨issue,hCta,hGet⟩,hAfter⟩ := inputBoxIssueAfterElection hp hMax hg site
    hCol hRow hHead hBar hAlign (by decide : 0 < 2^64) hBox hEndPc leader done
    (secondBiasIssueFrame (g := warpLane l g leader) half (by
      simpa [G] using done.checkpoint leader leader.isLt))
    (fun lane hl hLeader => secondBiasChoice (g := warpLane l g lane) half false (by
      simpa only [G,beq_eq_false_iff_ne.mpr hLeader] using done.checkpoint lane hl))
  exact ⟨⟨issue,hCta,hMap ▸ hGet⟩,hAfter⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {g batch shuffles votes : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 14) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSh : 10+7*(batch/31)+(if 31*(batch/31)<batch then 1 else 0)+1 < shuffles)
include hp hMax writes hg hw hb hLo hHi hSh

/-- Both opening stage-one Bias halves issue before the warp reaches its value setup. -/
theorem openingSecondBiasBoxesAndTailOfMaximal {ends : Nat → Option TState}
    (hReached : OpeningSecondBiasBoxesReached l X g shuffles votes ends) :
    let coords := assignedCoordinates p batch (g/l.block)
    (∀ half : Fin 2, ∃ issue, issue.1/l.block = g/l.block ∧
      X.TensorIssue issue p.biasMapAddress
        (biasInputSpec p (1152+64*half.val) (p.qOffset batch+256*coords.1+128) coords.2
          ⟨.shared,g/l.block,l.sharedBase+(199680+16384*half.val)⟩
          (Thread.Loader.biasReadyObject l (g/l.block) 1) false)) ∧
    Nonempty (SchedulerWarpReached l X g 780 (fun _ =>
      secondBiasBoxFrame l (p.qOffset batch+256*coords.1+128) coords.2) shuffles votes ends) := by
  obtain ⟨cur⟩ := hReached
  let coords := assignedCoordinates p batch (g/l.block)
  let row := p.qOffset batch+256*coords.1
  have hBounds := assignedCoordinates_valid hp hLo hHi
  have hRow : row+128 < 2^31 := by
    have h := hp.packedRow_lt hb hBounds.1
    have := hp.shape.2.2.2.2.2
    dsimp [row,coords]
    omega
  have hHead := hBounds.2.trans hp.heads_signed
  have hOperands := selectedOpeningBiasOperandsOfMaximal hp hMax writes hg hw hb hLo hHi
    (show 764 < 765 by decide) hSh cur
  obtain ⟨first⟩ := cur.advanceLocal (pc' := 765)
    (G := fun _ => secondBiasBoxFrame l (row+128) coords.2)
    (fun lane hl => by
      have hAt := (cur.checkpoint lane hl).mono (hOperands lane hl)
      have hSeg : Seg kernel [] l (warpLane l g lane) 1 764
          (openingBiasOperands l row coords.2) 765 (secondBiasBoxFrame l (row+128) coords.2) := by
        intro t ht
        have hFit := hRow.trans (by decide : 2^31 < 2^32)
        dsimp [secondBiasBoxFrame,openingBiasOperands] at ht ⊢
        seg_fp ht using norm_bits [Nat.mod_eq_of_lt hFit]
      obtain ⟨t,ht,hT⟩ := hSeg _ hAt
      exact ⟨t,run_rtg ((loaderLinear (regs := []) (by decide) (by decide) hAt.1
        (by simp) (by decide) ht).1),hT⟩)
  obtain ⟨left,⟨second⟩⟩ := secondBiasBoxOfMaximal hp hMax hg 0 hRow hHead first
  obtain ⟨right,tail⟩ := secondBiasBoxOfMaximal hp hMax hg 1 hRow hHead second
  refine ⟨?_,tail⟩
  intro half
  have hIssue : ∃ issue, issue.1/l.block = g/l.block ∧
      X.TensorIssue issue p.biasMapAddress
        (inputSiteSpec p l issue.1 (inputSite (secondBiasSite half))
        (secondBiasCol half) (row+128) coords.2 l.sharedBase) := by
    fin_cases half
    · exact left
    · exact right
  obtain ⟨issue,hCta,hGet⟩ := hIssue
  refine ⟨issue,hCta,?_⟩
  fin_cases half <;>
    simpa [inputSiteSpec,inputSite,inputMap,secondBiasSite,secondBiasCol,biasInputSpec,
      Thread.Loader.biasReadyObject,hCta,row,coords] using hGet

/-- The selected loader issues both opening stage-one Bias halves with the exact request row. -/
theorem openingSecondBiasBoxesOfMaximal {ends : Nat → Option TState}
    (hReached : OpeningSecondBiasBoxesReached l X g shuffles votes ends) :
    let coords := assignedCoordinates p batch (g/l.block)
    ∀ half : Fin 2, ∃ issue, issue.1/l.block = g/l.block ∧
      X.TensorIssue issue p.biasMapAddress
        (biasInputSpec p (1152+64*half.val) (p.qOffset batch+256*coords.1+128) coords.2
          ⟨.shared,g/l.block,l.sharedBase+(199680+16384*half.val)⟩
          (Thread.Loader.biasReadyObject l (g/l.block) 1) false) :=
  (openingSecondBiasBoxesAndTailOfMaximal hp hMax writes hg hw hb hLo hHi hSh hReached).1

end PTX.Kernels.TmlFa4Fwd.Loader
