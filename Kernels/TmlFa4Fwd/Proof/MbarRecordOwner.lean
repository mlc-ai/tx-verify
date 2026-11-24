-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MbarHistoryStart
public import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
public import Kernels.TmlFa4Fwd.Proof.GlobalWrites
public import Lemmas.Flow.TensorIssue
public import Lemmas.Flow.WaitAcquire

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof AsyncCopy
open Prologue

noncomputable section

private def localArriveOp : Op → Bool
  | .mbarArrive _ _ _ _ c _ _ _ => !c
  | _ => true

private theorem localArriveCode : kernel.code.all (fun i => localArriveOp i.op) = true := by
  decide +kernel

private theorem arrivalOwner {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {loc : Loc}
    {pc tx n : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get i = some ⟨pc, .arrive loc tx n rel sc⟩) : loc.cta = i.1 / l.block := by
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨t, ins, _, _, hCode, hf⟩
  · cases hBad
  obtain ⟨base, off, txOp, count, cluster, scope, dest, hOp, _⟩ := fires_arrive_flags hf rfl
  have hLocal := List.all_eq_true.mp localArriveCode _ (List.mem_of_getElem? hCode)
  have hCluster : cluster = false := by simpa [localArriveOp, hOp] using hLocal
  subst cluster
  rw [hOp] at hf
  have hWide : (Assumptions.all.any (·.clusterScopeMbar t.pc)) = false := rfl
  simp only [eventTmpl, tmaTmpl, hWide, widenMbarScope, Bool.false_eq_true, ↓reduceIte,
    bind, Except.bind, pure, Except.pure] at hf
  cases hl : mbarLoc l i.1 t base off with
  | error f => simp [hl, ofExec, Fires] at hf
  | ok addr =>
    cases hTx : readBits l i.1 t 32 txOp with
    | error f => simp [hl, hTx, ofExec, Fires] at hf
    | ok tx =>
      cases hN : readBits l i.1 t 32 count with
      | error f => simp [hl, hTx, hN, ofExec, Fires] at hf
      | ok k =>
        simp only [hl, hTx, hN, ofExec, Fires, Event.mk.injEq, Kind.arrive.injEq] at hf
        rw [hf.1.2.1]
        exact (mbarLoc_local hl).2

private def localTensorOp : Op → Bool
  | .cpTensor false _ _ _ _ _ _ _ none _ _ => true
  | op => !tensorOp op

private theorem localTensorCode : kernel.code.all (fun i => localTensorOp i.op) = true := by
  decide +kernel

private theorem tensorOwner {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {pc address : Nat}
    {s : TensorCopy.Spec} (he : X.get i = some ⟨pc, .tensorIssue address s⟩) :
    s.mbar.cta = i.1 / l.block := by
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hBad
  have hOp : tensorOp ins.op = true := by
    cases h : tensorOp ins.op
    · exact (fires_notTensor (eventTmpl_notTensor h) hf address s rfl).elim
    · rfl
  have hLoc := List.all_eq_true.mp localTensorCode _ (List.mem_of_getElem? hc)
  cases hi : ins.op <;> simp only [hi, tensorOp, Bool.false_eq_true] at hOp
  case cpTensor ca grp dst off map cs mb moff mc mode policy =>
    cases ca <;> cases mc <;> simp [hi, localTensorOp, tensorOp] at hLoc
    rw [hi] at hf
    have hm := fires_cpTensor_issue_loc hf rfl
    exact (mbarLoc_local hm).2

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

theorem actualCommitTargetOwner {i : EvId} {s : TcCommit.Spec} {loc : Loc} {rank : Fin 16}
    (hi : X.Commit i s) (ht : TcCommit.target s rank = some loc) : loc.cta = i.1 / l.block := by
  obtain ⟨_, hs⟩ := singleCommitResolved hX hi
  unfold TcCommit.resolve at hs
  split at hs
  swap
  · cases hs
  have hSize : l.clusterSizeOf (i.1 / l.block) = 1 := by
    rw [Launch.oneDim_clusterSizeOf hp.cluster.2.2, hp.cluster.1]
  have hBase : l.clusterStart (l.clusterOfCta (i.1 / l.block)) = i.1 / l.block := by
    rw [Launch.oneDim_clusterStart hp.cluster.2.2, Launch.oneDim_clusterOfCta hp.cluster.2.2,
      hp.cluster.1]
    simp
  have hResolved := (Option.some.inj hs).symm
  have hSize' : s.clusterSize = 1 := (congrArg TcCommit.Spec.clusterSize hResolved).trans hSize
  have hBase' : s.clusterBase = i.1 / l.block :=
    (congrArg TcCommit.Spec.clusterBase hResolved).trans hBase
  unfold TcCommit.target at ht
  split at ht
  · obtain rfl := (Option.some.inj ht).symm
    rename_i hRank
    have hZero : rank.val = 0 := by rw [hSize'] at hRank; omega
    dsimp only
    rw [hBase', hZero, Nat.add_zero]
  · cases ht

omit hp hX in
private theorem waitOwner {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {loc : Loc}
    {pc q : Nat} {ok acquire : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨pc, .wait loc q ok acquire scope⟩) : loc.cta = i.1 / l.block := by
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, _, _, _, _, hf⟩
  · cases hBad
  · exact (fires_wait_local hf rfl).2

/-- Every performed mbarrier action of the frozen kernel names an object in its issuer's CTA. -/
theorem mbarRecordOwner {loc : Loc} {r : MBarrier.Record Ref} (hr : r ∈ X.objects loc) :
    loc.cta = r.id.issuer.1 / l.block := by
  cases record_source hX.tma.2.2.1 hr with
  | init hi he _ =>
    rw [hi]
    obtain ⟨site, _, _, _, hLoc, _⟩ := actualInitializer hp hX (event_thread_lt hX he) he
    rw [hLoc]
    rfl
  | inval _ he _ => exact (noMbarInval hX ⟨_, he⟩).elim
  | arrive hi he _ =>
    rw [hi]
    exact arrivalOwner hX he
  | wait hi he _ =>
    rw [hi]
    exact waitOwner hX he
  | increment _ he _ => exact (Loader.noIncrementingCopyArrival hX ⟨_, he⟩).elim
  | tensor hi he hm _ =>
    rw [hi, ← hm]
    exact tensorOwner hX he
  | arriveOn hi he hm _ _ =>
    rw [hi, ← hm]
    exact (Loader.actualAsyncArrival hX he).2.2.2
  | bulk _ he hc _ _ =>
    rw [(actualCopyShape hX ⟨_, he⟩).completion] at hc
    cases hc
  | commit hi he ht _ =>
    rw [hi]
    exact actualCommitTargetOwner hp hX ⟨_, he⟩ ht
  | clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim

/-- A decoded initializer supplies the first record and publishes to every actual user. -/
theorem initializedObjectHistory {cta : Nat} (site : Fin 34) {i : EvId}
    (hInit : X.MbInit i (initObject l cta site) (initSite site).count) :
    PairTmaRing.InitFirst X (initObject l cta site) (initSite site).count ∧
      ∀ r ∈ X.objects (initObject l cta site), ObjectPublished l X (initObject l cta site) r :=
  initFirstOfOwnedRecords hp hX site hInit (fun _ hr _ => (mbarRecordOwner hp hX hr).symm)

/-- Every active audited object is initialized and each of its records has publication evidence. -/
theorem activeObjectHistory {cta : Nat} (site : Fin 34) {r : MBarrier.Record Ref}
    (hr : r ∈ X.objects (initObject l cta site)) :
    PairTmaRing.InitFirst X (initObject l cta site) (initSite site).count ∧
      ∀ u ∈ X.objects (initObject l cta site), ObjectPublished l X (initObject l cta site) u := by
  obtain ⟨i, hi⟩ := initializerOfOwnedRecord hp hX site hr (mbarRecordOwner hp hX hr).symm
  exact initializedObjectHistory hp hX site hi

/-- Every object operand, including an as yet undelivered arrival, names a location in the
issuer's CTA. A non-initializing use occurs after that CTA's startup rendezvous. -/
theorem actualMbarOperand {i : EvId} {loc : Loc} (hUse : X.UsesMbar i loc) :
    loc.cta = i.1 / l.block ∧ ∃ e, X.get i = some e ∧
      ((∃ count, X.MbInit i loc count) ∨ 173 < e.pc) := by
  have late {e : Event} (he : X.get i = some e) (hObj : ObjectKind e.kind)
      (hNon : ∀ loc count, e.kind ≠ .mbInit loc count) (hCta : loc.cta = i.1 / l.block) :
      loc.cta = i.1 / l.block ∧ ∃ e, X.get i = some e ∧
        ((∃ count, X.MbInit i loc count) ∨ 173 < e.pc) :=
    ⟨hCta, e, he, .inr (mbarUseIsLate hX he hObj hNon)⟩
  rcases hUse with ⟨_, _, _, _, _, he⟩ | ⟨_, hCopy, hCompletion⟩ | ⟨_, _, he⟩ |
    ⟨s, rank, hCommit, hTarget⟩ | ⟨_, _, _, _, _, he⟩ | hInval |
    ⟨_, s, ⟨_, he⟩, rfl⟩ | ⟨_, _, _, hClc, _, _⟩ | ⟨count, _, he⟩
  · exact late he trivial (by simp) (arrivalOwner hX he)
  · rw [(actualCopyShape hX hCopy).completion] at hCompletion
    cases hCompletion
  · exact late he trivial (by simp) (Loader.actualAsyncArrival hX he).2.2.2
  · obtain ⟨_, he⟩ := hCommit
    exact late he trivial (by simp) (actualCommitTargetOwner hp hX ⟨_, he⟩ hTarget)
  · exact late he trivial (by simp) (waitOwner hX he)
  · exact (noMbarInval hX hInval).elim
  · exact late he trivial (by simp) (tensorOwner hX he)
  · exact (noClcIssue hX hClc).elim
  · obtain ⟨_, _, _, _, hLoc, _⟩ := actualInitializer hp hX (event_thread_lt hX he) he
    exact ⟨by rw [hLoc]; rfl, _, he, .inl ⟨count, _, he⟩⟩

/-- Closure of operand addresses suffices for the operand-side publication safety check,
independently of whether any asynchronous operation has been performed. -/
theorem noUninitializedMbarOfAddresses
    (hAddresses : ∀ i loc, X.UsesMbar i loc →
      ∃ site : Fin 34, loc = initObject l (i.1 / l.block) site) :
    ¬ MbarUninit l X := by
  rintro ⟨i, loc, hUse, hNon, hBad⟩
  obtain ⟨_, e, he, ⟨count, hi⟩ | hLate⟩ := actualMbarOperand hp hX hUse
  · exact hNon count hi
  · obtain ⟨site, rfl⟩ := hAddresses i loc hUse
    obtain ⟨init, hInit, hPublished⟩ :=
      initPublishedAfterCommon hp hX (event_thread_lt hX he) he hLate site
    exact hBad ⟨init, _, hInit, hPublished⟩

end
end PTX.Kernels.TmlFa4Fwd
