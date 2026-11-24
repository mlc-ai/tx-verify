-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryCredits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy PTX.MBarrier PTX.Kernels.TmlFa4Fwd.Loader

/-- The transaction barrier where the two Bias subboxes publish one stage. -/
def biasReadyObject (l : Launch) (owner : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, owner, l.sharedBase + (320 + 8 * stage.val)⟩

/-- The Bias-empty object which gates reuse of the corresponding stage's storage. -/
def biasEmptyObject (l : Launch) (owner : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, owner, l.sharedBase + (336 + 8 * stage.val)⟩

/-- An actual Bias subbox identifies its half and its stage's shared destination. -/
def BiasSubbox (p : Params) (l : Launch) (X : Execution) (i : EvId)
    (stage half : Fin 2) (s : TensorCopy.Spec) : Prop :=
  X.TensorIssue i p.biasMapAddress s ∧
    s.mbar = biasReadyObject l (i.1 / l.block) stage ∧
    s.sharedBase = ⟨.shared, i.1 / l.block,
      l.sharedBase + (166912 + 32768 * stage.val + 16384 * half.val)⟩ ∧
    (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) = ⟨2, p.biasMap⟩ ∧
    s.rows = none ∧ s.clusterAddress = false ∧ s.group = .one

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A real tensor load targeting a Bias-ready object is one of that stage's two halves. -/
theorem biasSubboxOfBarrier {i : EvId} {s : TensorCopy.Spec} {address cta : Nat} (stage : Fin 2)
    (hi : X.TensorIssue i address s) (hs : s.mbar = biasReadyObject l cta stage) :
    i.1 / l.block = cta ∧ ∃ half, BiasSubbox p l X i stage half s := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨site, rfl⟩ := actualInputIssuePc hX he
  obtain ⟨ha, hd, hr, hDst, hCluster, hGroup⟩ := actualInputBoxAt hp hX site he
  have hMbar := loaderTensorOffset hp hX site he
  have hCta : i.1 / l.block = cta := congrArg Loc.cta (hMbar.symm.trans hs)
  have hOffset := congrArg Loc.addr (hMbar.symm.trans hs)
  change l.sharedBase + (inputBarrierBase site + (inputSite site).barrierOffset) =
    l.sharedBase + (320 + 8 * stage.val) at hOffset
  have hStage := Nat.add_left_cancel hOffset
  have hHalf : ∃ half : Fin 2, (inputSite site).bias = true ∧
      (inputSite site).sharedOffset = 166912 + 32768 * stage.val + 16384 * half.val := by
    fin_cases stage <;> fin_cases site <;>
      first | exact ⟨0, rfl, rfl⟩ | exact ⟨1, rfl, rfl⟩ |
        (simp [inputBarrierBase, inputSite] at hStage)
  obtain ⟨half, hBias, hBase⟩ := hHalf
  rw [inputMapAddress, hBias] at ha
  change address = p.biasMapAddress at ha
  subst address
  rw [inputMap, hBias] at hd
  exact ⟨hCta, half, ⟨_, he⟩, hCta.symm ▸ hs, by rw [hDst, hBase], hd, hr, hCluster, hGroup⟩

/-- Every actual tensor input is a Q plane or a Bias half at its owner's ready object. -/
theorem tensorInputSubbox {i : EvId} {s : TensorCopy.Spec} {address : Nat}
    (hi : X.TensorIssue i address s) :
    (∃ stage plane, QuerySubbox p l X i stage plane s) ∨
      ∃ stage half, BiasSubbox p l X i stage half s := by
  obtain ⟨pc, he⟩ := hi
  obtain ⟨site, rfl⟩ := actualInputIssuePc hX he
  have hLoc := loaderTensorOffset hp hX site he
  have hDispatch : ∀ site : Fin 14,
      (∃ stage : Fin 2, inputBarrierBase site + (inputSite site).barrierOffset = 8 * stage.val) ∨
        (∃ stage : Fin 2,
          inputBarrierBase site + (inputSite site).barrierOffset = 320 + 8 * stage.val) := by
    decide
  rcases hDispatch site with ⟨stage, hStage⟩ | ⟨stage, hStage⟩
  · exact .inl ⟨stage, (querySubboxOfBarrier hp hX stage ⟨_, he⟩
      (by rw [hLoc, hStage]; rfl)).2⟩
  · exact .inr ⟨stage, (biasSubboxOfBarrier hp hX stage ⟨_, he⟩
      (by rw [hLoc, hStage]; rfl)).2⟩

/-- Each arrival to a Bias-ready object contributes one arrival and two subboxes' bytes. -/
theorem biasOrdinaryCredit {i : EvId} {cta tx count : Nat} {release : Bool} {scope : MbarScope}
    (stage : Fin 2) (h : X.Arrive i (biasReadyObject l cta stage) tx count release scope) :
    tx = 32768 ∧ count = 1 ∧ release = true ∧ scope = .cta := by
  obtain ⟨pc, he⟩ := h
  have hSite := actualBiasCreditSite hp hX stage he rfl
  have hMember : pc ∈ [686, 711, 737, 763, 1153, 1182, 1368, 1900] := by
    fin_cases stage <;> simp at hSite ⊢ <;> omega
  exact actualLoaderCredit hX he hMember

private theorem biasNotAsyncArrive {cta : Nat} (stage : Fin 2) {i : EvId} {noinc : Bool}
    (h : X.AsyncArrive i (biasReadyObject l cta stage) noinc) : False := by
  obtain ⟨pc, he⟩ := h
  obtain ⟨⟨site, rfl⟩, rfl, _, _⟩ := actualAsyncArrival hX he
  have hSite : copyCommitPc site + 1 ∈ [674, 904, 1137, 1342, 1602, 1735] := by
    fin_cases site <;> decide
  obtain ⟨off, hOff, hLoc⟩ := loaderAsyncAddress hp hX he hSite
  have hAddr : l.sharedBase + (320 + 8 * stage.val) = l.sharedBase + off := congrArg Loc.addr hLoc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
  have := stage.isLt
  omega

private theorem biasNotCommit {cta : Nat} (stage : Fin 2) {i : EvId} {s : TcCommit.Spec}
    {rank : Fin 16} (h : X.Commit i s)
    (ht : TcCommit.target s rank = some (biasReadyObject l cta stage)) :
    False := by
  obtain ⟨pc, he⟩ := h
  rcases inCommitSites hX he with hf | hr
  · obtain ⟨off, hOff, hLoc⟩ := Mma.mmaFixedCommitAddress hp hX he hf ht
    have hAddr : l.sharedBase + (320 + 8 * stage.val) = l.sharedBase + off := congrArg Loc.addr hLoc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
    have := stage.isLt
    omega
  · obtain ⟨slot, hLoc⟩ := Mma.mmaRingCommitAddress hp hX he hr ht
    have hAddr : l.sharedBase + (320 + 8 * stage.val) = l.sharedBase + (8 * slot.val + 56) :=
      congrArg Loc.addr hLoc
    have := stage.isLt
    have := slot.isLt
    omega
end

/-- Bias-ready records are tied to the actual initializer, polls, expectations and tensor boxes. -/
inductive BiasReadyRecord (p : Params) (l : Launch) (X : Execution)
    (cta : Nat) (stage : Fin 2) (r : Record Ref) : Prop
  | init (h : ∃ c, r.action = .init c)
  | poll (h : ∃ parity ok, r.action = .pollParity parity ok)
  | expect (issue : EvId) (id : r.id = .thread issue)
      (credit : X.Arrive issue (biasReadyObject l cta stage) 32768 1 true .cta)
      (action : r.action = .arrive 1 32768)
  | notify (issue : EvId) (half : Fin 2) (s : TensorCopy.Spec)
      (id : r.id = .async issue (.notify .load))
      (owner : issue.1 / l.block = cta) (box : BiasSubbox p l X issue stage half s)
      (action : r.action = .completeTx 16384)

/-- Classify every record on an actual Bias-ready object's checked history. -/
theorem biasReadyRecord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (biasReadyObject l cta stage)) : BiasReadyRecord p l X cta stage r := by
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ h => exact .init ⟨_, h⟩
  | wait _ _ h => exact .poll ⟨_, _, h⟩
  | inval _ he _ => exact (noMbarInval hX ⟨_, he⟩).elim
  | arrive hid he ha =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := biasOrdinaryCredit hp hX stage ⟨_, he⟩
    exact .expect _ hid ⟨_, he⟩ ha
  | increment _ he _ => exact (biasNotAsyncArrive hp hX stage ⟨_, he⟩).elim
  | tensor hid he hm ha =>
    obtain ⟨hc, half, hBox⟩ := biasSubboxOfBarrier hp hX stage ⟨_, he⟩ hm
    exact .notify _ half _ hid hc hBox (ha.trans (congrArg Action.completeTx
      (actualTensorInputTxBytes hp hX hBox.1)))
  | arriveOn _ he hm _ _ =>
    exact (biasNotAsyncArrive hp hX stage ⟨_, by simpa only [hm] using he⟩).elim
  | bulk _ he hCompletion _ _ =>
    rw [(actualCopyShape hX ⟨_, he⟩).completion] at hCompletion
    cases hCompletion
  | commit _ he ht _ => exact (biasNotCommit hp hX stage ⟨_, he⟩ ht).elim
  | clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
