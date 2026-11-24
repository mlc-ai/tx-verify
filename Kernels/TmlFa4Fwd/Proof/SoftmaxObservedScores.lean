-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxScoreSource
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
import Kernels.TmlFa4Fwd.Proof.Thread.FirstScoreCommitObservation
import Lemmas.Flow.CommitTarget
import Lemmas.Execution.EventFrameSource
import Lemmas.Execution.ShapeExecution
import Lemmas.Flow.TcLdTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.TcMma PTX.Flow PTX.EventFrame PTX.Proof PTX.Assumption

/-- A recorded score load contains one word for each of the 32 decoded destinations. -/
theorem observedScoreLoadLength {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (round : Round) (q : Fin 4)
    {g j addr : Nat} {vals : List Value}
    (he : X.get (g, j) = some ⟨scorePc round q, .tc (.ld addr vals .s32x32b)⟩) :
    vals.length = 32 := by
  obtain ⟨_, hRun⟩ := hX.thr g (event_thread_lt hX he)
  obtain ⟨s, o, _, hStep⟩ := hRun.before_event he
  cases o with
  | none =>
    obtain ⟨_, _, hFire⟩ := hStep
    have hEnd := fires_none_ends hFire
    simp [Ends] at hEnd
  | some u =>
    have hPc : s.pc = scorePc round q := (estep_source_pc hStep).symm
    obtain ⟨ins, hInstr, _, hFire⟩ := estep_event_source hStep
    obtain ⟨ds, hLen, hCode⟩ := scoreCode round q
    rw [hPc, hCode] at hInstr
    obtain rfl := Option.some.inj hInstr
    exact (fires_tcLd_len (fun _ => by nofun) hFire rfl).trans hLen

set_option maxRecDepth 100000 in
private theorem firstScoreLoadFloor :
    (kernel.code.drop 3428).all (fun i => Thread.staysPastEvent 3428 i.op) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem firstScoreLoadFloorSegments :
    Assumptions.swExp2Sites.all (fun pc =>
      match cuteExp2.matchAt kernel pc with
      | some seg => decide (3428 ≤ seg.stop)
      | none => false) = true := by
  kernel_rfl

/-- The first phase-zero score wait in the actual trace precedes every observed first score load
on that lane. The proof does not use the loaded score values. -/
theorem firstObservedScoreWait {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {g j : Nat} {t : TState}
    (ht : At t 3425 [(2769, b32 (waitLoc l g stage 1).addr), (2770, b32 0)])
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ wait, X.get (g, wait) = some ⟨3425, .wait (waitLoc l g stage 1) 0 true true .cta⟩ ∧
      ∀ pos (q : Fin 4) vals addr, X.get (g, pos) = some
        ⟨scorePc .first q, .tc (.ld addr vals .s32x32b)⟩ → wait < pos := by
  obtain ⟨fails, _, hPoll, _, _⟩ := waitTraceAt hp stage 1 g 0 (by decide)
    (List.mem_cons_self) (List.mem_cons_of_mem _ List.mem_cons_self) (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · change 2769 ≠ 9751
        decide
      · obtain rfl := List.mem_singleton.mp hx
        decide) ht hr
  have hWait := firstScoreSuccessfulWait stage hPoll
  refine ⟨j + fails, hWait, fun pos q vals addr he => ?_⟩
  have hPc : 3428 ≤ scorePc .first q := by fin_cases q <;> decide
  exact Thread.traceOrderOfPcFloor hX firstScoreLoadFloor firstScoreLoadFloorSegments
    hWait he (by change 3425 < 3428; decide) hPc

private theorem initialScoreCommitCode (stage : Fin 2) :
    let site := Mma.commitSite (Mma.qkCommitSite (firstQkBlock stage))
    kernel.code[site.pc]? = some ⟨none, .tcCommit .one site.base (site.off : Int) none⟩ := by
  fin_cases stage
  · exact Flow.code_2208
  · exact Flow.code_2270

private theorem firstScoreCommitResolve {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {producer index : Nat} {s : TcCommit.Spec}
    (stage : Fin 2)
    (he : X.get (producer, index) = some
      ⟨(Mma.commitSite (Mma.qkCommitSite (firstQkBlock stage))).pc, .tc (.commit s)⟩) :
    ∃ loc bits, TcCommit.resolve l .one (producer / l.block) loc bits = some s := by
  obtain ⟨_, hRun⟩ := hX.thr producer (event_thread_lt hX he)
  obtain ⟨t, o, _, hStep⟩ := hRun.before_event he
  cases o with
  | none =>
    obtain ⟨_, _, hFire⟩ := hStep
    have hEnd := fires_none_ends hFire
    simp [Ends] at hEnd
  | some u =>
    have hp := (estep_source_pc hStep).symm
    obtain ⟨i, hc, _, hf⟩ := estep_event_source hStep
    rw [hp, initialScoreCommitCode stage] at hc
    obtain rfl := Option.some.inj hc
    exact tcCommit_resolves hf rfl

private theorem initialCommitCanonical {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {producer consumer : Nat} {stage : Fin 2}
    {spec : TcCommit.Spec} {loc : Loc} {bits : BitVec 16} {rank : Fin 16}
    (hResolve : TcCommit.resolve l .one (producer / l.block) loc bits = some spec)
    (hTarget : TcCommit.target spec rank = some (waitLoc l consumer stage 1)) :
    spec = Mma.commitSpec l producer (waitLoc l consumer stage 1).addr ∧ rank = 0 := by
  have hCluster (someCta : Nat) : l.clusterOfCta someCta = someCta := by
    simp only [Launch.oneDim_clusterOfCta hp.cluster.2.2, hp.cluster.1, Nat.div_one]
  have hSize : l.clusterSizeOf (producer / l.block) = 1 := by
    rw [Launch.oneDim_clusterSizeOf hp.cluster.2.2, hp.cluster.1]
  have hStart : l.clusterStart (l.clusterOfCta (producer / l.block)) = producer / l.block := by
    rw [hCluster, Launch.oneDim_clusterStart hp.cluster.2.2, hp.cluster.1, Nat.mul_one]
  unfold TcCommit.resolve at hResolve
  split_ifs at hResolve with h
  obtain rfl := (Option.some.inj hResolve).symm
  simp only [TcCommit.target, hSize, hStart] at hTarget
  split_ifs at hTarget with hr
  have hRank : rank = 0 := Fin.ext (by omega)
  subst rank
  have hMask : bits.toNat < 2 := by
    simpa only [hSize, Nat.pow_one] using h.2.2.2.2.2
  have hBits : bits = 1 := by
    apply BitVec.eq_of_toNat_eq
    change bits.toNat = 1
    simpa only [Fin.val_zero, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hMask] using hr.2
  have hCta := h.2.2.2.2.1
  rw [hCluster, hCluster] at hCta
  have hAddr := congrArg Loc.addr (Option.some.inj hTarget)
  have hLoc : loc = ⟨.shared, producer / l.block, (waitLoc l consumer stage 1).addr⟩ := by
    rcases loc with ⟨space, owner, addr⟩
    simp only [Loc.mk.injEq]
    exact ⟨h.2.2.1, hCta, hAddr⟩
  simp only [hLoc, hBits, hSize, hStart, Mma.commitSpec, and_true]

/-- The decoded opening issue and its actual observed notification recover the
canonical first QK phase used by the numerical score proof. -/
theorem firstQkPhaseOfOpeningObservation {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {producer consumer commit wait : Nat} {spec : TcCommit.Spec} {rank : Fin 16}
    (hCta : SameCta l producer consumer)
    (hCommit : X.get (producer,commit) =
      some ⟨(Mma.commitSite (Mma.qkCommitSite (firstQkBlock stage))).pc,.tc (.commit spec)⟩)
    (hWait : X.get (consumer,wait) = some
      ⟨3425,.wait (waitLoc l consumer stage 1) 0 true true .cta⟩)
    (hTarget : TcCommit.target spec rank = some (waitLoc l consumer stage 1))
    (hObserve : MBarrier.UpdateBeforeWait (X.objects (waitLoc l consumer stage 1))
      (.async (producer,commit) (.tcNotify rank)) (.thread (consumer,wait))) :
    FirstQkPhase l X stage producer consumer commit wait := by
  obtain ⟨loc,bits,hResolve⟩ := firstScoreCommitResolve hX stage hCommit
  obtain ⟨rfl,rfl⟩ := initialCommitCanonical hp hResolve hTarget
  exact ⟨hCta,hCommit,hWait,hObserve⟩

/-- The first score wait identifies its initial QK commit when steady commits are absent. -/
theorem firstObservedInitialScorePhaseOfNoSteadyCommits
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {g wait : Nat} (hWait : X.get (g, wait) =
      some ⟨3425, .wait (waitLoc l g stage 1) 0 true true .cta⟩)
    (hNoSteady : ∀ producer index spec pc, producer / l.block = g / l.block →
      X.get (producer, index) = some ⟨pc, .tc (.commit spec)⟩ →
      pc ∈ [2418,2519] → False) :
    ∃ producer commit, FirstQkPhase l X stage producer g commit wait := by
  obtain ⟨block, ⟨producer, index⟩, spec, rank, hCommit, hCta, hTarget, _, hObserve⟩ :=
    Thread.firstScoreWaitObservesCommit hp hX stage hWait
  have hSmall : block.val < 2 := by
    by_contra! hLarge
    apply hNoSteady producer index spec _ hCta.2.2 hCommit
    fin_cases block <;> first | contradiction | decide
  have hSite : (Mma.commitSite (Mma.qkCommitSite block)).pc ∈
      [2208, 2270, 2274, 2418, 2519, 2537, 2541, 2642, 2646] := by
    fin_cases block <;> decide
  have hAddr := congrArg Loc.addr
    (Mma.mmaFixedCommitExactAddress hp hX hCommit hSite hTarget)
  change l.sharedBase + (80 + 8 * stage.val) =
    l.sharedBase + Mma.fixedMmaCommitOffset (Mma.commitSite (Mma.qkCommitSite block)).pc at hAddr
  have hIdentified : block = firstQkBlock stage := by
    apply Fin.ext
    fin_cases block <;> simp [firstQkBlock, Mma.qkCommitSite, Mma.commitSite,
      Mma.fixedMmaCommitOffset] at hAddr hSmall ⊢ <;> omega
  subst block
  exact ⟨producer,index,firstQkPhaseOfOpeningObservation hp hX stage hCta
    hCommit hWait hTarget hObserve.2⟩

/-- An individual observed first score load reads its mathematical cell value directly
from the identified MMA result and the ordering of competing writers. -/
theorem firstObservedScoreWord {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {producer consumer issue commit wait read : Nat}
    (hPhase : FirstQkPhase l X stage producer consumer commit wait)
    (hBefore : issue < commit) (hAfter : wait < read)
    (q : Fin 4) (word : Fin 32) {vals : List Value} {value : ℝ}
    (he : X.get (consumer, read) = some
      ⟨scorePc .first q, .tc (.ld (scoreAddress l consumer stage q) vals .s32x32b)⟩)
    (hResult : Result l Assumptions.all X (producer, issue)
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val)
      (.float .f32 value))
    (hOther : ∀ other, TmemWrite l X other
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val) →
      other = (producer, issue) ∨ WriteBefore l X other (producer, issue) ∨
        ReadBefore l X .ld (consumer, read) other)
    (hLive : SourceLive l X (producer, issue) (consumer, read)
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val)) :
    vals[word.val]? = some (.float .f32 value) := by
  let addr := scoreAddress l consumer stage q
  let cell := tcDataCell l consumer .s32x32b addr word.val
  have hLen := observedScoreLoadLength hX .first q he
  have hLoad : X.TLd (consumer, read) addr vals .s32x32b := ⟨_, he⟩
  have hCell : LoadCell l X (consumer, read) word.val cell :=
    ⟨addr, vals, .s32x32b, hLoad, hLen.symm ▸ word.isLt, rfl⟩
  have hRead := firstScoreReadSource hX hPhase hBefore q word he hAfter hResult hOther hLive
  obtain ⟨v, hv, hContains⟩ :=
    hX.tcRead.1 _ _ _ _ _ _ _ _ hLoad hCell hRead (.inl hResult)
  rcases hContains with ⟨_, rfl⟩ | ⟨hBad, _⟩
  · exact hv
  · cases hBad

end PTX.Kernels.TmlFa4Fwd.Softmax
