-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryInputOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.InputCredits
public import Kernels.TmlFa4Fwd.Proof.MmaReadyHistory
public import Kernels.TmlFa4Fwd.Proof.LoaderRingMbarAddress
public import Kernels.TmlFa4Fwd.Proof.MmaGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy PTX.MBarrier Prologue
open Thread.Output (queryObject)
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- An actual successful acquire contributes the clean wait record to its query object. -/
theorem queryPollRecord {wait : EvId} {stage : Fin 2} {e : Event} {parity : Nat}
    (he : X.get wait = some e)
    (hk : e.kind = .wait (queryObject l (wait.1 / l.block) stage) parity true true .cta) :
    let log := X.objects (queryObject l (wait.1 / l.block) stage)
    ∃ (j : Nat) (r : Record Ref), log[j]? = some r ∧ r.id = .thread wait ∧
      r.action = .pollParity parity true ∧ r.fault = none ∧ r.reply.waited = some true := by
  obtain ⟨pc, kind⟩ := e
  change kind = _ at hk
  subst kind
  exact actualPollRecordClean hp hX he

omit hp hX in
/-- An actual query subbox identifies its plane, its Q descriptor and its shared destination. -/
def QuerySubbox (p : Params) (l : Launch) (X : Execution) (i : EvId)
    (stage plane : Fin 2) (s : TensorCopy.Spec) : Prop :=
  X.TensorIssue i p.qMapAddress s ∧
    s.mbar = queryObject l (i.1 / l.block) stage ∧
    s.sharedBase = ⟨.shared, i.1 / l.block, Mma.qStart l stage + 16384 * plane.val⟩ ∧
    (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) = ⟨2, p.qMap⟩ ∧
    s.rows = none ∧ s.clusterAddress = false ∧ s.group = .one

/-- A tensor transfer credited to a query barrier is one of that stage's two Q planes. -/
theorem querySubboxOfBarrier {i : EvId} {s : TensorCopy.Spec} {address cta : Nat} (stage : Fin 2)
    (hi : X.TensorIssue i address s) (hs : s.mbar = queryObject l cta stage) :
    i.1 / l.block = cta ∧ ∃ plane, QuerySubbox p l X i stage plane s := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨site, rfl⟩ := actualInputIssuePc hX he
  obtain ⟨ha, hd, hr, hDst, hCluster, hGroup⟩ := actualInputBoxAt hp hX site he
  have hMbar := loaderTensorOffset hp hX site he
  have hCta : i.1 / l.block = cta := congrArg Loc.cta (hMbar.symm.trans hs)
  have hOffset := congrArg Loc.addr (hMbar.symm.trans hs)
  change l.sharedBase + (inputBarrierBase site + (inputSite site).barrierOffset) =
    l.sharedBase + 8 * stage.val at hOffset
  have hStage : inputBarrierBase site + (inputSite site).barrierOffset = 8 * stage.val :=
    Nat.add_left_cancel hOffset
  have hex : ∃ plane : Fin 2, (inputSite site).bias = false ∧
      (inputSite site).sharedOffset = 3072 + 32768 * stage.val + 16384 * plane.val := by
    fin_cases stage <;> fin_cases site <;>
      first | exact ⟨0, rfl, rfl⟩ | exact ⟨1, rfl, rfl⟩ |
        (simp [inputBarrierBase, inputSite] at hStage)
  obtain ⟨plane, hBias, hBase⟩ := hex
  rw [inputMapAddress, hBias] at ha
  change address = p.qMapAddress at ha
  subst address
  rw [inputMap, hBias] at hd
  refine ⟨hCta, plane, ⟨_, he⟩, hCta.symm ▸ hs, ?_, hd, hr, hCluster, hGroup⟩
  rw [hDst, hBase]
  simp [Mma.qStart, Nat.add_assoc]

/-- An issued query subbox belongs to an active tile when its scheduling offsets are preserved. -/
theorem QuerySubbox.active (hProtected : Epilogue.DrainCuQProtected p X) {i : EvId}
    {stage plane : Fin 2} {s : TensorCopy.Spec} (hBox : QuerySubbox p l X i stage plane s) :
    i.1 / l.block < tilePrefix p p.batch * p.heads := by
  obtain ⟨g,j⟩ := i
  obtain ⟨site, he⟩ := hBox.1
  obtain ⟨s, rfl⟩ := actualInputIssuePc hX he
  have hBand : ∀ n : Fin 14, 297 < (inputSite n).pc ∧ (inputSite n).pc < 1862 ∧
      (inputSite n).pc ∉ registerHintSites := by decide
  have hs := hBand s
  have hRole := roleBodyPcOfEvent hp hX he (by change 173 < (inputSite s).pc; omega) hs.2.2
  change roleBodyPc (warpIndex l g) (inputSite s).pc at hRole
  have hw : 14 ≤ warpIndex l g := by
    obtain ⟨hLo, hHi, _⟩ := hs
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  exact loaderOwnPrefixEventRequiresActiveTile hp hX hw hProtected he hs.1 hs.2.1

/-- A successful query expectation contributes one arrival and both subboxes' bytes. -/
theorem queryOrdinaryCredit {i : EvId} {cta tx count : Nat} {release : Bool} {scope : MbarScope}
    (stage : Fin 2) (h : X.Arrive i (queryObject l cta stage) tx count release scope) :
    tx = 32768 ∧ count = 1 ∧ release = true ∧ scope = .cta := by
  obtain ⟨pc, he⟩ := h
  have hSite := actualQueryCreditSite hp hX stage he
    (rfl : (queryObject l cta stage).addr = l.sharedBase + 8 * stage.val)
  have hMember : pc = 686 ∨ pc = 737 ∨ pc = 1900 := by fin_cases stage <;> simp_all
  rcases hMember with rfl | rfl | rfl <;> exact actualLoaderCredit hX he (by decide)

private theorem queryNotAsyncArrive {cta : Nat} (stage : Fin 2) {i : EvId} {noinc : Bool}
    (h : X.AsyncArrive i (queryObject l cta stage) noinc) : False := by
  obtain ⟨pc, he⟩ := h
  obtain ⟨⟨site, rfl⟩, rfl, _, _⟩ := actualAsyncArrival hX he
  have hSite : copyCommitPc site + 1 ∈ [674, 904, 1137, 1342, 1602, 1735] := by
    fin_cases site <;> decide
  obtain ⟨off, hOff, hLoc⟩ := loaderAsyncAddress hp hX he hSite
  have hAddr : l.sharedBase + 8 * stage.val = l.sharedBase + off := congrArg Loc.addr hLoc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
  have := stage.isLt
  omega

private theorem queryNotCommit {cta : Nat} (stage : Fin 2) {i : EvId} {s : TcCommit.Spec}
    {rank : Fin 16} (h : X.Commit i s)
    (ht : TcCommit.target s rank = some (queryObject l cta stage)) : False := by
  obtain ⟨pc, he⟩ := h
  rcases inCommitSites hX he with hf | hr
  · obtain ⟨off, hOff, hLoc⟩ := Mma.mmaFixedCommitAddress hp hX he hf ht
    have hAddr : l.sharedBase + 8 * stage.val = l.sharedBase + off := congrArg Loc.addr hLoc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
    have := stage.isLt
    omega
  · obtain ⟨slot, hLoc⟩ := Mma.mmaRingCommitAddress hp hX he hr ht
    have hAddr : l.sharedBase + 8 * stage.val = l.sharedBase + (8 * slot.val + 56) :=
      congrArg Loc.addr hLoc
    have := stage.isLt
    omega
end

/-- A query barrier's record comes from initialization, a poll, expectation or a Q box. -/
inductive QueryRecord (p : Params) (l : Launch) (X : Execution)
    (cta : Nat) (stage : Fin 2) (r : Record Ref) : Prop
  | init (h : ∃ c, r.action = .init c)
  | poll (h : ∃ parity ok, r.action = .pollParity parity ok)
  | expect (issue : EvId) (id : r.id = .thread issue)
      (credit : X.Arrive issue (queryObject l cta stage) 32768 1 true .cta)
      (action : r.action = .arrive 1 32768)
  | notify (issue : EvId) (plane : Fin 2) (s : TensorCopy.Spec)
      (id : r.id = .async issue (.notify .load))
      (owner : issue.1 / l.block = cta) (box : QuerySubbox p l X issue stage plane s)
      (action : r.action = .completeTx 16384)

/-- All query-barrier records have their actual kernel source and transaction size. -/
theorem queryRecord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (queryObject l cta stage)) : QueryRecord p l X cta stage r := by
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ h => exact .init ⟨_, h⟩
  | wait _ _ h => exact .poll ⟨_, _, h⟩
  | inval _ he _ => exact (noMbarInval hX ⟨_, he⟩).elim
  | arrive hid he ha =>
    have hCredit := queryOrdinaryCredit hp hX stage ⟨_, he⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hCredit
    exact .expect _ hid ⟨_, he⟩ ha
  | increment _ he _ => exact (queryNotAsyncArrive hp hX stage ⟨_, he⟩).elim
  | tensor hid he hm ha =>
    obtain ⟨hc, plane, hBox⟩ := querySubboxOfBarrier hp hX stage ⟨_, he⟩ hm
    exact .notify _ plane _ hid hc hBox (ha.trans (congrArg Action.completeTx
      (actualTensorInputTxBytes hp hX hBox.1)))
  | arriveOn _ he hm _ _ =>
    exact (queryNotAsyncArrive hp hX stage ⟨_, by simpa only [hm] using he⟩).elim
  | bulk _ he hCompletion _ _ =>
    rw [(actualCopyShape hX ⟨_, he⟩).completion] at hCompletion
    cases hCompletion
  | commit _ he ht _ => exact (queryNotCommit hp hX stage ⟨_, he⟩ ht).elim
  | clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
