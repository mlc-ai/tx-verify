-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Proof.LoaderTripCount
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
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Flow.Code.Part021

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.Assumption

/-- An actual later loader event forces the intervening audited stable checkpoint. -/
theorem observedBiasCut {l : Launch} {X : Execution} {g pos start stop : Nat}
    {s : TState} {ending : Option TState} {F : List (Nat × Value)}
    (hRange : 174 ≤ start ∧ start ≤ stop ∧ stop ≤ 1901)
    (hs : At s start F)
    (hAudit : ∀ branch, ((kernel.code.drop start).take (stop - start)).all
      (fun ins => loaderPipelineCutOp start stop branch (F.map Prod.fst) ins.op) = true)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    {j : Nat} {target : Event} (he : X.get (g,j) = some target)
    (hBefore : pos ≤ j) (hLate : stop ≤ target.pc) (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u index result, At u stop F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop index) result ∧ index ≤ j := by
  obtain ⟨u,passed,result,_,hAt,hRun,_,hIndex⟩ :=
    prefixStableCut hRange hAudit hs hr he hBefore hSafe
      (fun _ => 0) (fun _ => false) (.inl hLate) (by intros; rfl)
      (by intros; rfl) (by intros; simp)
  exact ⟨u,pos+passed.length,result,hAt,hRun,hIndex⟩

private def residueFlag (residue : Nat) : Bool :=
  decide (toSigned 32 (BitVec.ofNat 64 residue) < 0)

private theorem residualFlagCore (l : Launch) (g residue : Nat) (hResidue : residue < 2^32) :
    Seg kernel [] l g 1 803 [(1089,b32 residue)]
      804 [(164,.pred (residueFlag residue))] := by
  intro s hs
  seg_fp hs using
    simp only [truncBits_ofNat hResidue (by decide), compare, Option.getD_some,residueFlag,
      show toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 from rfl]

private theorem flagCore (l : Launch) (g trips : Nat) (rest : Bool) (hTrips : trips < 2^31) :
    Seg kernel [] l g 2 905 [(1088,b32 trips),(164,.pred rest)]
      907 [(7,.pred (decide (10 < trips) && rest))] := by
  have hCast : (10 : Int) < (trips : Int) ↔ 10 < trips := by omega
  have hTen : toSigned 32 (truncBits 32 (BitVec.ofInt 64 10)) = 10 := rfl
  intro s hs
  seg_fp hs using simp only [truncBits_ofNat (show trips < 2^32 by omega) (by decide), compare,
    Option.getD_some,int32Signed hTrips,hTen,gt_iff_lt,hCast]

private theorem bypassCore (l : Launch) (g : Nat) :
    Seg kernel [] l g 3 1355 [(1062,b32 14),(7,.pred false)] 1358 [(202,.pred true)] := by
  intro s hs
  seg_fp hs using rfl

private theorem noTailIssuesAfterBypass {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hp : 1384 ≤ s.pc)
    (hw : Walk kernel Assumptions.all l g s es vs) :
    ∀ e ∈ es, 1384 ≤ e.pc := by
  have hFloor : (kernel.code.drop 1384).all (fun i => Thread.staysPastEvent 1384 i.op) =
      true := by set_option maxRecDepth 100000 in kernel_rfl
  have hSegments : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (1384 ≤ seg.stop)
      | none => false) = true := by set_option maxRecDepth 100000 in kernel_rfl
  exact Thread.eventTailEvents hFloor hSegments hw hp

set_option maxRecDepth 100000 in
/-- The optional last Bias tensor pair requires both the residual lower-stage block
and the longer warm-trip case in the actual loader trace. -/
theorem biasTailGuardOfPrimingFrame {l : Launch} {X : Execution} {g pos j trips residue : Nat}
    {s : TState} {ending : Option TState} {target : Event}
    (hTrips : trips < 2^31) (hResidue : residue < 2^32)
    (hs : At s 488 [(1062,b32 14),(1088,b32 trips),(1089,b32 residue)])
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (he : X.get (g,j) = some target) (hBefore : pos ≤ j)
    (hTail : 1376 ≤ target.pc ∧ target.pc < 1384) (hSafe : ∀ f, target.kind ≠ .ub f) :
    10 < trips ∧ residue ≠ 0 := by
  have firstAudit : ∀ branch, ((kernel.code.drop 488).take (803 - 488)).all
      (fun ins => loaderPipelineCutOp 488 803 branch [1062,1088,1089] ins.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨t,tPos,_,ht,hRun,hT⟩ :=
    observedBiasCut (start := 488) (stop := 803) (by decide) hs firstAudit hr he hBefore
      (by omega) hSafe
  obtain ⟨u,hu,hU⟩ := (residualFlagCore l g residue hResidue).apply
    (ht.mono ⟨ht.2.2.2.2.2.2.1,trivial⟩)
  have ⟨huAll,huFrame⟩ := loaderLinear (regs := [1062,1088])
    (by decide) (by decide) ht.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu
  have huAt : At u 804 [(1062,b32 14),(1088,b32 trips),(164,.pred (residueFlag residue))] :=
    hU.mono ⟨(huFrame _ (by decide)).trans ht.2.2.2.2.1,
      (huFrame _ (by decide)).trans ht.2.2.2.2.2.1,hU.2.2.2.2.1,trivial⟩
  have hUrun := hRun.after_local_nonempty (run_rtg huAll) (traceAfterObservedEvent he hT)
  have secondAudit : ∀ branch, ((kernel.code.drop 804).take (905 - 804)).all
      (fun ins => loaderPipelineCutOp 804 905 branch [1062,1088,164] ins.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨v,vPos,_,hv,hRun,hV⟩ :=
    observedBiasCut (start := 804) (stop := 905) (by decide) huAt secondAudit hUrun
      he hT (by omega) hSafe
  let enabled := decide (10 < trips) && (residueFlag residue)
  obtain ⟨w,hw,hW⟩ := (flagCore l g trips (residueFlag residue) hTrips).apply (hv.mono hv.2.2.2.2.2)
  have ⟨hwAll,hwFrame⟩ := loaderLinear (regs := [1062])
    (by decide) (by decide) hv.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl hw
  have hwAt : At w 907 [(1062,b32 14),(7,.pred enabled)] :=
    hW.mono ⟨(hwFrame _ (by decide)).trans hv.2.2.2.2.1,hW.2.2.2.2.1,trivial⟩
  have hwRun := hRun.after_local_nonempty (run_rtg hwAll) (traceAfterObservedEvent he hV)
  suffices hTrue : enabled = true by
    obtain ⟨hEnough,hNegative⟩ := Bool.and_eq_true_iff.mp hTrue
    refine ⟨of_decide_eq_true hEnough,?_⟩
    intro he
    subst residue
    cases hNegative
  cases hEnabled : enabled
  · rw [hEnabled] at hwAt
    have thirdAudit : ∀ branch, ((kernel.code.drop 907).take (1355 - 907)).all
        (fun ins => loaderPipelineCutOp 907 1355 branch [1062,7] ins.op) = true := by
      intro branch
      set_option maxRecDepth 100000 in kernel_rfl
    obtain ⟨a,aPos,_,ha,haRun,hA⟩ :=
      observedBiasCut (start := 907) (stop := 1355) (by decide) hwAt thirdAudit hwRun
        he hV (by omega) hSafe
    obtain ⟨b,hb,hB⟩ := (bypassCore l g).apply ha
    have hbAll := (loaderLinear (regs := []) (by decide) (by decide) ha.1
      (by simp) (by set_option maxRecDepth 100000 in kernel_rfl) hb).1
    obtain ⟨c,hc,hC⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
      Flow.code_1358 true hB hB.2.2.2.2.1 (by simp)
    have hcAll := (loaderLinear (regs := []) (by decide) (by decide) hB.1 (by simp) rfl hc).1
    have hcRun := haRun.after_local_nonempty (run_rtg (run_comp hbAll hcAll))
      (traceAfterObservedEvent he hA)
    obtain ⟨_,hWalk⟩ := Mma.walkFromRun hcRun
    have hGet : ((X.tr g).drop aPos)[j-aPos]? = some target := by
      rwa [List.getElem?_drop,Nat.add_sub_of_le hA]
    have hFloor : 1384 ≤ c.pc := by exact hC.1.ge
    have hTooLate := noTailIssuesAfterBypass hFloor hWalk target (List.mem_of_getElem? hGet)
    omega
  · rfl

end PTX.Kernels.TmlFa4Fwd.Loader
