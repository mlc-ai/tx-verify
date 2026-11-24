-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryBoxProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPollProgress
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
import Kernels.TmlFa4Fwd.Flow.Code.Part011
import Lemmas.Flow.ReturningPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader

/-- The actual opening expectation of the lower Bias barrier. -/
def OpeningBiasExpectation (l : Launch) (X : Execution) (e : EvId) (cta : Nat) : Prop :=
  X.get e = some ⟨711,.arrive (biasReadyObject l cta 0) 32768 1 true .cta⟩

theorem OpeningBiasExpectation.arrive {l : Launch} {X : Execution} {e : EvId} {cta : Nat}
    (h : OpeningBiasExpectation l X e cta) :
    X.Arrive e (biasReadyObject l cta 0) 32768 1 true .cta :=
  ⟨_,h⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption PTX.MBarrier PTX.AsyncCopy
open Prologue Epilogue Thread.Loader

noncomputable section

private def openingBiasBaseFrame (l : Launch) : List (Nat × Value) := [(2535,b32 l.sharedBase)]

/-- Pointer registers after the opening Bias acquire. -/
def openingBiasCreditFrame (l : Launch) : List (Nat × Value) :=
  [(1114,b32 (l.sharedBase+320)),(2535,b32 l.sharedBase)]

private def openingBiasWaitSite : DrainWaitSite := ⟨704,9608,1897,1898⟩

private def openingBiasWaitFrame (l : Launch) : List (Nat × Value) :=
  [(1897,b32 (l.sharedBase+336)),(1898,b32 1),(1114,b32 (l.sharedBase+320))] ++
    openingBiasBaseFrame l

private theorem openingBiasWaitCode : LoaderWaitCode openingBiasWaitSite :=
  ⟨Flow.code_704,Flow.code_705,Flow.code_706⟩

private theorem openingBiasWaitLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (ht : At t 701 (openingBiasBaseFrame l)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 704 (openingBiasWaitFrame l) := by
  have hf : l.sharedBase+336 < 2^32 := by have := hp.shared.2.1; omega
  have hSmall : l.sharedBase+320 < 2^32 := by omega
  have hSeg : Seg kernel [] l g 3 701 (openingBiasBaseFrame l) 704 (openingBiasWaitFrame l) := by
    intro s hs
    dsimp [openingBiasWaitFrame,openingBiasBaseFrame] at *
    seg_fp hs using first | rfl | norm_bits [Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hSmall]
  obtain ⟨u,hu,hU⟩ := hSeg t ht
  have hLocal := (loaderLinear (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu).1
  exact ⟨u,run_rtg hLocal,hU⟩

private def openingBiasElectReturn (l : Launch) (g : Nat) (t : TState) (leader : Nat) : TState :=
  next (setReg (setReg t 1899 (b32 leader)) 146 (.pred (laneOf l g == leader)))

private theorem openingBiasElectOut {l : Launch} {g : Nat} {s : TState}
    (hPc : s.pc = 707) (hFault : s.fault = none) :
    out kernel Assumptions.all l g s = .ev (.elect 4294967295 (openingBiasElectReturn l g s)) := by
  rw [loaderOutCore (by rw [hPc]; decide) (by rw [hPc]; decide)]
  rw [out_event hFault (by rw [hPc]; exact Flow.code_707) rfl rfl]
  have hMask : readBits l g s 32 (.imm (-1)) = .ok 4294967295#64 := rfl
  have hMember : electMember 4294967295 (laneOf l g) := PTX.electMember_full l g
  change Out.ev (electTmpl l g s (some 1899) 146 (.imm (-1))) = _
  simp only [electTmpl,hMask,show (4294967295#64).toNat = 4294967295 from rfl,hMember,↓reduceIte]
  rfl

private theorem openingBiasElectFresh {l : Launch} {g : Nat} {s t : TState}
    {events : List Event} (h : TraceReach kernel Assumptions.all l g s events t) (ht : t.pc = 707) :
    ∀ mask inst leader, (⟨707,.elect mask inst leader⟩ : Event) ∉ events := by
  have hFloor {v w : TState} {es : List Event}
      (hRun : TraceReach kernel Assumptions.all l g v es w) (hv : 708 ≤ v.pc) :
      708 ≤ w.pc := by
    induction hRun with
    | refl => exact hv
    | tau hs _ ih =>
      exact ih (Thread.eventTailStepOfAudit (by decide +kernel) (by decide +kernel) hv
        (.inl ⟨rfl,hs⟩))
    | event he _ ih =>
      exact ih (Thread.eventTailStepOfAudit (by decide +kernel) (by decide +kernel) hv
        (.inr ⟨_,rfl,he⟩))
  induction h with
  | refl => simp
  | tau _ _ ih => exact ih ht
  | @event s v t es e he hs ih =>
    intro mask inst leader hm
    rcases List.mem_cons.mp hm with hEq | hTail
    · have hPc : s.pc = 707 := (estep_source_pc he).symm.trans (congrArg Event.pc hEq).symm
      cases hFault : s.fault with
      | none =>
        obtain ⟨tm,hOut,hFire⟩ := he
        rw [openingBiasElectOut hPc hFault,Out.ev.injEq] at hOut
        subst tm
        obtain ⟨_,lead,_,hRet⟩ := hFire
        have hV := congrArg TState.pc (Option.some.inj hRet)
        change v.pc = s.pc+1 at hV
        have hAfter := hFloor hs (by omega)
        omega
      | some f =>
        obtain ⟨tm,hOut,hFire⟩ := he
        simp only [out,hFault,Out.ev.injEq] at hOut
        subst tm
        cases hFire.2
    · exact ih ht _ _ _ hTail

private theorem openingBiasBranch {l : Launch} {g : Nat} {s : TState} (lead : Bool)
    (hs : At s 708 ((146,.pred lead) :: openingBiasCreditFrame l)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if lead then 710 else 712) (openingBiasCreditFrame l) := by
  let F := openingBiasCreditFrame l
  have hNot : Seg kernel [] l g 1 708 ((146,.pred lead) :: F) 709 ((147,.pred (!lead)) :: F) := by
    intro s hs
    let v := next (setReg s 147 (.pred (!lead)))
    have hFresh : ∀ pair ∈ (146,.pred lead) :: F, pair.1 ≠ 147 := by
      simp [F,openingBiasCreditFrame]
    have hAt := hs.set (v := .pred (!lead)) hFresh
    refine ⟨v,?_,hAt.mono ⟨hAt.2.2.2.2.1,hAt.2.2.2.2.2.2⟩⟩
    apply run_local Flow.code_708 rfl hs
    rw [execLocalA_nil]
    change execInt l g s ⟨.not,.pred,false,[some 147],[.reg 146]⟩ = _
    simp [execInt,DType.width,readPred,readReg,hs.2.2.2.2.1,v,
      bind,Except.bind,pure,Except.pure]
  obtain ⟨v,hv,hV⟩ := hNot s hs
  obtain ⟨w,hw,hW⟩ := run_bra (K := kernel) (A := []) Flow.code_709 (!lead) hV
    hV.2.2.2.2.1 (by simp)
  have hv' := (loaderLinear (regs := []) (by decide) (by decide) hs.1
    (by simp) (by decide) hv).1
  have hw' := (loaderLinear (regs := []) (by decide) (by decide) hV.1
    (by simp) (by decide) hw).1
  exact ⟨w,run_rtg (run_comp hv' hw'),by
    cases lead <;> exact hW.mono hW.2.2.2.2.2⟩

private theorem openingBiasExpectNext {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} (hs : At s 708 ((146,.pred true) :: openingBiasCreditFrame l)) :
    ∃ t u, t.pc = 711 ∧ At u 712 (openingBiasCreditFrame l) ∧
      Next kernel Assumptions.all l g s t
        (.arrive ((fun cta => biasReadyObject l cta 0) (g/l.block)) 32768 u 1 true .cta) := by
  let F := openingBiasCreditFrame l
  obtain ⟨w,hw,hW⟩ := openingBiasBranch (g := g) true hs
  have hLoad : Seg kernel [] l g 1 710 F 711 ((1900,b32 32768) :: F) := by
    intro z hz
    dsimp [F,openingBiasCreditFrame,openingBiasBaseFrame] at *
    seg_fp hz using rfl
  obtain ⟨t,ht,hT⟩ := hLoad w hW
  have ht' := (loaderLinear (regs := []) (by decide) (by decide) hW.1
    (by simp) (by decide) ht).1
  let loc := (fun cta => biasReadyObject l cta 0) (g/l.block)
  let u := next (mbarStateDest t (some 7584))
  have hOut : out kernel Assumptions.all l g t = .ev (.arrive loc 32768 u 1 true .cta) := by
    rw [loaderOutCore (by rw [hT.1]; decide) (by rw [hT.1]; decide)]
    rw [out_event hT.2.2.2.1 (by rw [hT.1]; exact Flow.code_711) rfl rfl]
    have hBase : l.sharedBase+320 < 2^32 := by have := hp.shared.2.1; omega
    have hAlign : (l.sharedBase+320)%8 = 0 := by have := hp.shared.1; omega
    have hEff : effAddr l g t .shared 1114 0 = .ok loc := by
      simpa [loc,biasReadyObject] using effAddr_b32_off
        (off := 0) hT.2.2.2.2.2.1 hBase
    have hLoc : mbarLoc l g t 1114 0 = .ok loc := by
      simp [mbarLoc,hEff,loc,biasReadyObject,hAlign,bind,Except.bind,pure,Except.pure]
    have hOne : readBits l g t 32 (.imm 1) = .ok 1#64 := rfl
    simp [eventTmpl,widenMbarScope,tmaTmpl,hLoc,readBits_b32 hT.2.2.2.2.1 (by decide),
      hOne,u,bind,Except.bind,pure,Except.pure,ofExec]
  have hU : At u 712 F := by
    refine ⟨by change t.pc+1 = 712; rw [hT.1],hT.2.1,hT.2.2.1,hT.2.2.2.1,?_⟩
    simp [Holds,F,openingBiasCreditFrame,u,mbarStateDest,next,
      hT.2.2.2.2.2.1,hT.2.2.2.2.2.2.1]
  exact ⟨t,u,hT.1,hU,hw.trans (run_rtg ht'),hOut⟩

/-- The expectation is recorded and both opening Bias boxes are ready to issue. -/
def OpeningBiasBoxesReached (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  Nonempty (SchedulerWarpReached l X g 712 (fun _ => openingBiasCreditFrame l) shuffles votes ends)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState} (hStart : OpeningBiasReached l X g shuffles votes ends)
    (hReady : ∀ lane < 32, OpeningBiasBlocked l X (warpLane l g lane) →
      let log := X.objects (biasEmptyObject l (g/l.block) 0)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0)
include hp hMax hg hStart hReady

/-- The warp acquires its opening Bias buffer and records its elected transaction expectation. -/
theorem openingBiasExpectedAtSiteOfMaximal :
    OpeningBiasBoxesReached l X g shuffles votes ends ∧
      ∃ issue, Thread.Loader.OpeningBiasExpectation l X issue (g/l.block) := by
  obtain ⟨start⟩ := hStart
  obtain ⟨cur⟩ := start.advanceLocal (pc' := 704) (G := fun _ => openingBiasWaitFrame l)
    (fun lane hl => openingBiasWaitLocal hp (g := warpLane l g lane) (start.checkpoint lane hl))
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hAddr : l.sharedBase+336 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+336)%8 = 0 := by have := hp.shared.1; omega
  obtain ⟨atElection⟩ := loaderWarpWaitOfReadyLast hMax hg hBlock openingBiasWaitCode
    (by decide) hAddr hAlign cur (fun _ _ => by simp [openingBiasWaitFrame,openingBiasWaitSite,
      openingBiasBaseFrame]) (fun _ _ => by simp [openingBiasWaitFrame,openingBiasWaitSite])
    (fun _ _ => by simp [openingBiasWaitFrame,openingBiasWaitSite])
    (fun lane hl {_ _} hRun hLocal hAt => hReady lane hl ⟨_,_,hRun,hLocal,hAt.1⟩)
  let post := fun lane => openingBiasElectReturn l (warpLane l g lane) (atElection.state lane)
  let frame := fun (lane leader : Nat) => (146,.pred (lane == leader)) :: openingBiasCreditFrame l
  have hFresh (lane : Nat) (hl : lane < 32) (j : Nat) (hj : j < atElection.pos lane)
      (mask inst leader : Nat) : ¬ X.Elect (warpLane l g lane,j) 707 mask inst leader := by
    intro he
    have hTrace := (atElection.recorded lane hl).returning_reach.append
      (TraceReach.of_local (atElection.localSteps lane hl))
    have hGet : ((X.tr (warpLane l g lane)).take (atElection.pos lane))[j]? =
        some ⟨707,.elect mask inst leader⟩ := by rwa [List.getElem?_take_of_lt hj]
    exact openingBiasElectFresh hTrace (atElection.checkpoint lane hl).1 mask inst leader
      (List.mem_append_left [] (List.mem_of_getElem? hGet))
  obtain ⟨leader,elected,_⟩ := atElection.consumeElection hp hMax hg post frame
    hFresh (fun lane hl => openingBiasElectOut (atElection.checkpoint lane hl).1
      (atElection.checkpoint lane hl).2.2.2.1) (fun lane hl leader => by
      have hAt := atElection.checkpoint lane hl
      have hLane : laneOf l (warpLane l g lane) = lane :=
        (Step.sameWarp_lane hBlock hg hl).2
      have hBase := hAt.2.2.2.2.2.2.2.1
      have hReadyBase := hAt.2.2.2.2.2.2.1
      exact ⟨by simp [post,openingBiasElectReturn,next,setReg,hAt.1,openingBiasWaitSite],
        hAt.2.1,hAt.2.2.1,hAt.2.2.2.1,by
          simp [Holds,frame,post,openingBiasElectReturn,next,setReg,
            openingBiasCreditFrame,hBase,hReadyBase,hLane]⟩)
  obtain ⟨hWarp,issue,he⟩ := expectationOfElectedWarp hp hMax hg
    (fun cta => biasReadyObject l cta 0)
    (site := 711) (F := fun _ => openingBiasCreditFrame l) elected leader
    (by
      apply openingBiasExpectNext hp (g := warpLane l g leader)
      simpa [frame,openingBiasWaitSite] using elected.checkpoint leader leader.isLt)
    (fun lane hl hLeader => by
      have hAt : At (elected.state lane) 708 ((146,.pred false) :: openingBiasCreditFrame l) := by
        simpa only [frame,openingBiasWaitSite,beq_eq_false_iff_ne.mpr hLeader] using
          elected.checkpoint lane hl
      exact openingBiasBranch (g := warpLane l g lane) false hAt)
  exact ⟨hWarp,issue,he⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
