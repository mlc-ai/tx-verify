-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionSource
public import Kernels.TmlFa4Fwd.Proof.GlobalWrites
public import Kernels.TmlFa4Fwd.Proof.StaticSafety
public import Lemmas.Protocol.MbarOneShot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX AsyncCopy MBarrier

noncomputable section

/-- The correction group's 128 lanes, with the position of this stage's ready arrival. -/
def readyArrival (l : Launch) (g : Nat) (pos : Nat → Nat) (lane : Nat) : Ref × Nat :=
  (.thread ((g / l.block) * l.block + 256 + lane, pos lane), 0)

def readyArrivals (l : Launch) (g : Nat) (pos : Nat → Nat) : List (Ref × Nat) :=
  (List.range 128).map (readyArrival l g pos)

private theorem readyArrivals_bytes (l : Launch) (g : Nat) (pos : Nat → Nat) :
    ((readyArrivals l g pos).map Prod.snd).sum = 0 := by
  simp [readyArrivals, readyArrival, List.map_map, Function.comp_def]

/-- The trace facts needed at a ready barrier. The only producers are correction lanes;
the MMA and loader complete on their own barriers. -/
structure OutputReadySources (l : Launch) (X : Execution) (g : Nat) (stage : Fin 2)
    (pos : Nat → Nat) : Prop where
  initialized : PairTmaRing.InitFirst X (readyLoc l g stage) 128
  arrival : ∀ i pc tx count rel scope, X.get i = some
      ⟨pc, .arrive (readyLoc l g stage) tx count rel scope⟩ →
      ∃ lane < 128, .thread i = (readyArrival l g pos lane).1 ∧ tx = 0 ∧ count = 1
  arrivalKind : ∀ lane < 128, ∀ ev,
    X.get ((g / l.block) * l.block + 256 + lane, pos lane) = some ev →
    ev.kind = .arrive (readyLoc l g stage) 0 1 true .cta
  poll : ∀ i pc parity ok acq scope, X.get i = some
      ⟨pc, .wait (readyLoc l g stage) parity ok acq scope⟩ → parity = 0
  tensor : ∀ i address s, X.TensorIssue i address s → s.mbar ≠ readyLoc l g stage
  copyArrive : ∀ i noinc, ¬ X.AsyncArrive i (readyLoc l g stage) noinc
  commit : ∀ i s rank, X.Commit i s → TcCommit.target s rank ≠ some (readyLoc l g stage)

/-- The ready object has one phase of 128 generic arrivals. This derives the object ledger
from source events of the same consistent execution. -/
theorem outputReadyHistory {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} {stage : Fin 2} {pos : Nat → Nat} (hSrc : OutputReadySources l X g stage pos) :
    MbarOneShot.Hist X (readyLoc l g stage) (readyArrivals l g pos) [] where
  count := by simp only [readyArrivals, List.length_map, List.length_range]; decide
  bytes := by rw [readyArrivals_bytes]; exact Nat.zero_le _
  sizes := by simp [readyArrivals_bytes]
  nodup := by simp
  arrivals_nodup := by
    simp only [readyArrivals, List.map_map]
    apply List.nodup_range.map
    intro a b h
    simp only [Function.comp_apply, readyArrival, Ref.thread.injEq, Prod.mk.injEq] at h
    omega
  records r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha =>
      obtain ⟨r₀, _, ha₀, _, hUnique⟩ := hSrc.initialized r hr
      obtain rfl := hUnique r hr ⟨_, ha⟩
      exact .inl (by simpa only [readyArrivals, List.length_map, List.length_range] using ha₀)
    | inval _ he _ => exact (noMbarInval hX ⟨_, he⟩).elim
    | arrive hid he ha =>
      obtain ⟨lane, hl, hi, rfl, rfl⟩ := hSrc.arrival _ _ _ _ _ _ he
      exact .inr (.inl ⟨readyArrival l g pos lane, List.mem_map.mpr
        ⟨lane, List.mem_range.mpr hl, rfl⟩, hid.trans hi, ha⟩)
    | wait hid he ha =>
      obtain rfl := hSrc.poll _ _ _ _ _ _ he
      exact .inr (.inr (.inr ⟨_, _, hid, ha⟩))
    | tensor _ he hm _ => exact (hSrc.tensor _ _ _ ⟨_, he⟩ hm).elim
    | increment _ he _ => exact (hSrc.copyArrive _ false ⟨_, he⟩).elim
    | arriveOn _ he hm _ _ => exact (hSrc.copyArrive _ _ ⟨_, hm ▸ he⟩).elim
    | bulk _ he hc _ _ =>
      have hs := (actualCopyShape hX ⟨_, he⟩).completion
      rw [hs] at hc
      cases hc
    | commit _ he hTarget _ => exact (hSrc.commit _ _ _ ⟨_, he⟩ hTarget).elim
    | clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim
  arrive_record r hr a ha hid := by
    obtain ⟨lane, hLane, rfl⟩ := List.mem_map.mp ha
    have hl := List.mem_range.mp hLane
    have hAct := ((hX.tma.2.2.1 (readyLoc l g stage)).2.1 r hr).1
    rw [hid] at hAct
    change objectAction X X.async (readyLoc l g stage)
      (.thread ((g / l.block) * l.block + 256 + lane, pos lane)) = some r.action at hAct
    cases he : X.get ((g / l.block) * l.block + 256 + lane, pos lane) with
    | none => simp [objectAction, he] at hAct
    | some ev =>
      have hk := hSrc.arrivalKind lane hl ev he
      obtain ⟨pc, kind⟩ := ev
      change kind = _ at hk
      subst kind
      simpa [objectAction, he, readyArrival, eq_comm] using hAct
  init_first := by simpa only [readyArrivals, List.length_map, List.length_range] using
    hSrc.initialized
  copy_mbar := by simp
  no_inval := fun _ => noMbarInval hX

/-- A warp-13 ready wait acquires the concrete arrival of each correction lane. -/
theorem readyWaitObserves {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {stage : Fin 2} {pos : Nat → Nat} (hSrc : OutputReadySources l X g stage pos)
    (hWait : X.get (g, j) = some ⟨pollPc stage, .wait (readyLoc l g stage) 0 true true .cta⟩)
    {lane : Nat} (hl : lane < 128) :
    WaitObserves X (readyArrival l g pos lane).1 (g, j) (readyLoc l g stage) true .cta := by
  have hMem : readyArrival l g pos lane ∈ readyArrivals l g pos :=
    List.mem_map.mpr ⟨lane, List.mem_range.mpr hl, rfl⟩
  exact ⟨⟨_, _, hWait⟩, (outputReadyHistory hX hSrc).observes_arrive hX hMem hWait⟩

/-- The selected ready phase makes an earlier correction write visible to its O store. -/
theorem readyPublishesOutput {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait issue : Nat} {stage : Fin 2} {pos : Nat → Nat}
    (hSrc : OutputReadySources l X g stage pos)
    {lane written fence : Nat} (hl : lane < 128)
    (hWait : X.get (g, wait) =
      some ⟨pollPc stage, .wait (readyLoc l g stage) 0 true true .cta⟩)
    {address : Nat} {spec : TensorStore.Spec}
    (hIssue : X.TensorStoreIssue (g, issue) address spec) (hOrder : wait < issue)
    (hBefore : written < fence) (hAfter : fence ≤ pos lane)
    (hFence : X.get ((g / l.block) * l.block + 256 + lane, fence) =
      some ⟨Correction.outputFencePc stage, .fenceProxy (.async (some (.shared .cta))) none⟩)
    (hArrive : X.get ((g / l.block) * l.block + 256 + lane, pos lane) =
      some ⟨Correction.outputFencePc stage + 2,
        .arrive (readyLoc l ((g / l.block) * l.block + 256 + lane) stage) 0 1 true .cta⟩) :
    let writer := (g / l.block) * l.block + 256 + lane
    Staging.Publish l X (writer, written) (writer, fence) (writer, pos lane)
      (g, wait) (g, issue) (readyLoc l writer stage) := by
  intro writer
  obtain ⟨pc, he⟩ := hIssue
  have hW := PTX.Proof.event_thread_lt hX hFence
  have hG := PTX.Proof.event_thread_lt hX he
  have hSame : writer / l.block = g / l.block := by
    dsimp [writer]
    rw [hp.block]
    omega
  have hi : issue < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  exact Correction.correctionPublication (i := (g, issue)) stage hW hG hSame hi hOrder
    hBefore hAfter hFence hArrive (readyWaitObserves hX hSrc hWait hl)

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
