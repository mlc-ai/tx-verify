-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit
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
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseSource
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Lemmas.Flow.ElectActor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue

private theorem finalOutputWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {commit : EvId} {pc : Nat} {e : Kind} (hSite : pc = 2642 ∨ pc = 2646)
    (he : X.get commit = some ⟨pc, e⟩) : warpIndex l commit.1 = 12 := by
  obtain ⟨g, j⟩ := commit
  have he' : X.get (g,j) = some ⟨pc,e⟩ := he
  have hHint : pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he' (show 173 < pc by omega) hHint
  change roleBodyPc (warpIndex l g) pc at hRole
  unfold roleBodyPc at hRole
  rcases hRole with h | h
  · omega
  · split_ifs at h <;> omega

/-- The observed final stage-zero commit is an MMA-role event. -/
theorem FirstOutputCommit.issuerWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {commit : EvId} {spec : TcCommit.Spec} (h : FirstOutputCommit X commit spec) :
    warpIndex l commit.1 = 12 :=
  finalOutputWarp hp hX (.inl rfl) h

/-- The observed final stage-one commit is an MMA-role event. -/
theorem SecondOutputCommit.issuerWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner : EvId} {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X owner spec) :
    warpIndex l owner.1 = 12 :=
  finalOutputWarp hp hX (Or.inr rfl : (2646 : Nat) = 2642 ∨ 2646 = 2646) hCommit.decoded

/-- An actual final O1 commit and a K/V release in its CTA select the same lane. -/
theorem SecondOutputCommit.sameReleaseIssuer {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner : EvId} {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X owner spec)
    {g index : Nat} {form : Mma.ReleaseForm} {releaseSpec : TcCommit.Spec}
    (hRelease : Mma.ReleaseIssue X g index form releaseSpec) (hCta : owner.1/l.block = g/l.block) :
    owner.1 = g := by
  have hw : SameWarp l owner.1 g :=
    ⟨⟨event_thread_lt hX hCommit.decoded,event_thread_lt hX hRelease,hCta⟩,
      (hCommit.issuerWarp hp hX).trans (hRelease.issuerWarp hp hX).symm⟩
  obtain ⟨_,_,leader0,he0,hLane0⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.secondOutputCommitLeader hp hX hCommit.decoded
  obtain ⟨_,_,leader1,he1,hLane1⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.readyReleaseLeader hp hX (Mma.releaseIndex form) hRelease
  exact selected_elect_thread_unique hX.elect he0 he1 hw hLane0 hLane1

/-- The two actual final MMA commits of a CTA are issued by the same lane, with
the first output's commit preceding the second output's commit. -/
theorem finalOutputCommitsInOrder {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {first second : EvId} {s0 s1 : TcCommit.Spec} (hCta : SameCta l first.1 second.1)
    (hFirst : FirstOutputCommit X first s0) (hSecond : SecondOutputCommit X second s1) :
    TraceBefore X first second := by
  obtain ⟨g, j⟩ := first
  obtain ⟨h, k⟩ := second
  have h0 : X.get (g,j) = some ⟨2642, .tc (.commit s0)⟩ := hFirst
  have h1 : X.get (h,k) = some ⟨2646, .tc (.commit s1)⟩ := hSecond.decoded
  have hw0 := finalOutputWarp hp hX (Or.inl rfl : (2642 : Nat) = 2642 ∨ 2642 = 2646) h0
  have hw1 := finalOutputWarp hp hX (Or.inr rfl : (2646 : Nat) = 2642 ∨ 2646 = 2646) h1
  have hSame : SameWarp l g h := ⟨hCta, hw0.trans hw1.symm⟩
  obtain ⟨_, i0, leader0, he0, hl0⟩ := Mma.firstOutputCommitLeader hp hX h0
  obtain ⟨_, i1, leader1, he1, hl1⟩ := Mma.secondOutputCommitLeader hp hX h1
  have hLane : g = h := selected_elect_thread_unique hX.elect he0 he1 hSame hl0 hl1
  subst h
  have hCode : (kernel.code.drop 2646).all (fun i => staysPastEvent 2646 i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSegments : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (2646 ≤ seg.stop)
      | none => false) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hOrder := traceOrderOfPcFloor hX hCode hSegments h0 h1
    (show 2642 < 2646 by decide) (show 2646 ≤ 2646 by decide)
  exact ⟨rfl, hOrder, (List.getElem?_eq_some_iff.mp h1).1⟩

end PTX.Kernels.TmlFa4Fwd.Thread
