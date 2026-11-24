-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstBiasGeometry
public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasCredits
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasFirstVisit
import Lemmas.Protocol.PollPhase
import Kernels.TmlFa4Fwd.Proof.MmaReadyHistory

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.AsyncCopy PTX.MBarrier Softmax Thread.Scores Thread.Loader

noncomputable section

/-- The completed Bias box generation observed by this first-visit lane. -/
def FirstBiasAcquirePhase (l : Launch) (X : Execution) (g wait : Nat) (stage : Fin 2)
    (phase : Nat) : Prop :=
  let log := X.objects (waitLoc l g stage 2)
  ∃ j r, log[j]? = some r ∧ r.id = .thread (g, wait) ∧ observedAt log j = some phase

/-- An actual parity-zero acquire supplies its clean completed phase in the object trace. -/
theorem firstBiasAcquirePhase {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait : Nat} {stage : Fin 2}
    (hWait : FirstBiasAcquire l X g wait stage) :
    ∃ phase, phase % 2 = 0 ∧ FirstBiasAcquirePhase l X g wait stage phase := by
  obtain ⟨j, r, hr, hid, ha, _, hWait⟩ := hWait.pollRecord hp hX
  obtain ⟨s, n, _, ha', hParity, hCompleted⟩ :=
    (X.objects_checked hX (waitLoc l g stage 2)).okPoll hr hWait
  obtain rfl : n = 0 := (Action.pollParity.inj (ha'.symm.trans ha)).1
  have hPos : 0 < s.phase := by omega
  refine ⟨s.phase - 1, by omega, j, r, hr, hid, ?_⟩
  simp [observedAt, hr, hCompleted, hPos]

/-- The actual loader notification contributed its credit to the given Bias phase. -/
def BiasNotifyPhase (l : Launch) (X : Execution) (g : Nat) (stage : Fin 2)
    (phase : Nat) (tensor : EvId) : Prop :=
  let log := X.objects (waitLoc l g stage 2)
  ∃ j r, log[j]? = some r ∧ r.id = .async tensor (.notify .load) ∧
    r.fault = none ∧ phaseAt log j = some phase

/-- The successful first Bias poll observes the actual tensor notification in its phase. -/
theorem firstBiasObservesNotification {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait phase : Nat} {stage : Fin 2} {tensor : EvId}
    (hWait : FirstBiasAcquire l X g wait stage)
    (hSeen : FirstBiasAcquirePhase l X g wait stage phase)
    (hNotify : BiasNotifyPhase l X g stage phase tensor) :
    AsyncObserved X tensor (.notify .load) (g, wait) true .cta := by
  let loc := waitLoc l g stage 2
  let log := X.objects loc
  obtain ⟨i, note, hi, hNote, hClean, hPhaseNote⟩ := hNotify
  obtain ⟨j, poll, hj, hPoll, hPhaseWait⟩ := hSeen
  have hc (rec : Record Ref) (h : rec ∈ log) :=
    ((hX.tma.2.2.1 loc).2.1 rec h).1
  have hAction : ∃ n, note.action = .completeTx n := by
    have hSource := record_source hX.tma.2.2.1 (List.mem_of_getElem? hi)
    cases hSource <;> first
      | exact ⟨_, ‹note.action = .completeTx _›⟩
      | grind
  obtain ⟨n, hn⟩ := hAction
  have hObject := hc note (List.mem_of_getElem? hi)
  rw [hNote, hn] at hObject
  obtain ⟨j', poll', hj', hPoll', _, hPollClean, hSuccess⟩ := hWait.pollRecord hp hX
  have hEq := ObjectInit.checked_record_index_eq (X.objects_checked hX loc)
    hj' hj (hPoll'.trans hPoll.symm)
  subst j'
  obtain rfl := Option.some.inj (hj'.symm.trans hj)
  have hNo := objects_noInval hX.tma.2.2.1 (fun e _ => noMbarInval hX (i := e)) loc
  have hOrder := MbarRing.Slot.updateBeforeWait_of_phase (X.objects_checked hX loc) hNo
    hi hClean hj hPollClean hSuccess hPhaseNote hPhaseWait
  rw [hNote, hPoll] at hOrder
  exact hWait.observes hX hObject hOrder

/-- An observed Bias tensor box selects its exact CTA, half, and launched Bias descriptor. -/
structure AcquiredBiasBox (p : Params) (l : Launch) (X : Execution) (stage : Fin 2)
    (g wait : Nat) (tensor : EvId) (half : Fin 2) (o : TensorCopy.Observation) : Prop where
  observed : AsyncObserved X tensor (.notify .load) (g, wait) true .cta
  completion : X.tensor tensor = some o
  issue : X.TensorIssue tensor p.biasMapAddress o.spec
  owner : tensor.1 / l.block = g / l.block
  target : o.spec.mbar = waitLoc l g stage 2
  destination : o.spec.sharedBase = ⟨.shared, g / l.block, biasBoxStart l stage half.val⟩
  descriptor : (⟨o.spec.outer, o.spec.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
    ⟨2, p.biasMap⟩
  rows : o.spec.rows = none
  cluster : o.spec.clusterAddress = false
  group : o.spec.group = .one

/-- The acquired observation retains the abstract issued Bias subbox. -/
theorem AcquiredBiasBox.subbox {p : Params} {l : Launch} {X : Execution}
    {stage half : Fin 2} {g wait : Nat} {tensor : EvId} {o : TensorCopy.Observation}
    (h : AcquiredBiasBox p l X stage g wait tensor half o) :
    BiasSubbox p l X tensor stage half o.spec := by
  refine ⟨h.issue, ?_, ?_, h.descriptor, h.rows, h.cluster, h.group⟩
  · rw [h.owner]
    exact h.target
  · rw [h.owner]
    simpa only [biasBoxStart, Nat.add_assoc] using h.destination

/-- The actual Bias acquire and notification determine one of the legal physical Bias halves. -/
theorem acquiredBiasBoxOfNotification {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait phase : Nat} {stage : Fin 2} {tensor : EvId}
    (hWait : FirstBiasAcquire l X g wait stage)
    (hSeen : FirstBiasAcquirePhase l X g wait stage phase)
    (hNotify : BiasNotifyPhase l X g stage phase tensor) :
    ∃ half o, AcquiredBiasBox p l X stage g wait tensor half o := by
  have hObs := firstBiasObservesNotification hp hX hWait hSeen hNotify
  obtain ⟨o, addr, ho, hIssue, _, hWaited⟩ := hObs.tensor
  have hMbar := hWait.target hWaited.1
  obtain ⟨hOwner, half, hIssue, _, hDst, hDesc, hRows, hCluster, hGroup⟩ :=
    biasSubboxOfBarrier hp hX stage hIssue hMbar
  rw [hOwner] at hDst
  refine ⟨half, o, hObs, ho, hIssue, hOwner, hMbar, ?_, hDesc, hRows, hCluster, hGroup⟩
  simpa only [biasBoxStart, Nat.add_assoc] using hDst

/-- The completed phase of the successful first Bias acquire contains two distinct actual
tensor notifications, each observed by that lane. -/
theorem firstBiasAcquiredPair {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait phase : Nat} {stage : Fin 2} (hWait : FirstBiasAcquire l X g wait stage)
    (hPhase : FirstBiasAcquirePhase l X g wait stage phase) :
    ∃ a b, a ≠ b ∧ BiasNotifyPhase l X g stage phase a ∧ BiasNotifyPhase l X g stage phase b ∧
      (∃ half o, AcquiredBiasBox p l X stage g wait a half o) ∧
      (∃ half o, AcquiredBiasBox p l X stage g wait b half o) := by
  let loc := waitLoc l g stage 2
  obtain ⟨j, r, hj, hid, hObserved⟩ := hPhase
  have hPhase : FirstBiasAcquirePhase l X g wait stage phase := ⟨j, r, hj, hid, hObserved⟩
  obtain ⟨k, poll, hk, hPoll, _, _, hSuccess⟩ := hWait.pollRecord hp hX
  have hIndex := ObjectInit.checked_record_index_eq (X.objects_checked hX loc)
    hk hj (hPoll.trans hid.symm)
  subst k
  obtain rfl := Option.some.inj (hk.symm.trans hj)
  obtain ⟨a, b, hNe, hA, hB⟩ := biasReadyObservedBoxes hp hX stage hj hSuccess hObserved
  exact ⟨a, b, hNe, hA.2, hB.2, acquiredBiasBoxOfNotification hp hX hWait hPhase hA.2,
    acquiredBiasBoxOfNotification hp hX hWait hPhase hB.2⟩

/-- Once a decoded observed box's runtime coordinates have been replayed, it supplies the
source witness consumed by the first Bias load trace. -/
theorem AcquiredBiasBox.firstBiasBox {p : Params} {l : Launch} {X : Execution}
    {stage half : Fin 2} {g wait col row head : Nat} {tensor : EvId} {o : TensorCopy.Observation}
    (hBox : AcquiredBiasBox p l X stage g wait tensor half o)
    (hOrigin : (⟨o.spec.outer, o.spec.origin⟩ : (n : Nat) × (Fin (n + 1) → Int)) =
      ⟨2, inputCoordinate col row head⟩) :
    FirstBiasBox p l X stage g wait col row head half tensor := by
  rcases hBox with ⟨hObs, he, _, hOwner, target, base, dm, hr, hCluster, hGroup⟩
  refine ⟨hOwner, hObs, o, waitLoc l g stage 2, false, he, ?_⟩
  rcases o with ⟨⟨⟨outer, desc, origin, shared, rows⟩, mb, cluster, group⟩, effects⟩
  simp only [Sigma.mk.injEq] at dm
  obtain ⟨rfl, hd⟩ := dm
  obtain rfl := eq_of_heq hd
  simp only [Sigma.mk.injEq] at hOrigin
  obtain rfl := eq_of_heq hOrigin.2
  simp only at target base hr hCluster hGroup
  subst shared mb rows cluster group
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
