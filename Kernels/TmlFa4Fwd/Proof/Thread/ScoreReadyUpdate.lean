-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Softmax
public import Lemmas.Protocol.PairTmaRing.Hyp
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
import Kernels.TmlFa4Fwd.Proof.MbarSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.AsyncCopy PTX.MBarrier

/-- The CTA-local object notified after the MMA role finishes a score fragment group. -/
def scoreReadyObject (l : Launch) (cta : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, cta, l.sharedBase + (80 + 8 * stage.val)⟩

/-- An actual score-ready update is an initial or recurring MMA notification for its stage. -/
theorem scoreReadyUpdate {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {r : Record Ref} (hr : r ∈ X.objects (scoreReadyObject l cta stage))
    (hUpdate : CounterUpdate r.action) :
    ∃ i spec rank, r.id = .async i (.tcNotify rank) ∧ X.Commit i spec ∧
      TcCommit.target spec rank = some (scoreReadyObject l cta stage) ∧
      i.1 / l.block = cta ∧ r.action = .arrive 1 0 := by
  have offset {off owner : Nat}
      (h : scoreReadyObject l cta stage = ⟨.shared, owner, l.sharedBase + off⟩) :
      off = 80 + 8 * stage.val := by
    have hAddr := congrArg Loc.addr h
    change l.sharedBase + (80 + 8 * stage.val) = l.sharedBase + off at hAddr
    omega
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha | wait _ _ ha | inval _ _ ha => rw [ha] at hUpdate; exact hUpdate.elim
  | arrive _ he _ =>
    obtain ⟨off, hOff, hLoc⟩ := actualArriveOffsetIn hp hX he
    have hNo : 80 + 8 * stage.val ∉ ordinaryArriveOffsets := by fin_cases stage <;> decide
    exact (hNo (offset hLoc ▸ hOff)).elim
  | increment _ he _ => exact (Loader.noIncrementingCopyArrival hX ⟨_, he⟩).elim
  | tensor _ he hTarget _ =>
    obtain ⟨site, rfl⟩ := Loader.actualInputIssuePc hX he
    have hLoc := Loader.loaderTensorOffset hp hX site he
    have audit : ∀ (j : Fin 14) (s : Fin 2),
        Loader.inputBarrierBase j + (Loader.inputSite j).barrierOffset ≠ 80 + 8 * s.val := by
      decide
    exact (audit site stage (offset (hTarget.symm.trans hLoc))).elim
  | arriveOn _ he hTarget _ _ =>
    obtain ⟨⟨site, rfl⟩, rfl, _, _⟩ := Loader.actualAsyncArrival hX he
    have hSite := (by decide : ∀ q : Fin 6,
      Loader.copyCommitPc q + 1 ∈ [674, 904, 1137, 1342, 1602, 1735]) site
    obtain ⟨off, hOff, hLoc⟩ := Loader.loaderAsyncAddress hp hX he hSite
    have hEq := offset (hTarget.symm.trans hLoc)
    exact ((by decide : ∀ s : Fin 2, 80 + 8 * s.val ∉ [32, 40, 48]) stage (hEq ▸ hOff)).elim
  | bulk _ he hCompletion _ _ =>
    rw [(actualCopyShape hX ⟨_, he⟩).completion] at hCompletion
    cases hCompletion
  | commit hId he hTarget hAct =>
    obtain ⟨off, _, _, hLoc⟩ := actualCommitOffset hp hX he hTarget
    exact ⟨_, _, _, hId, ⟨_, he⟩, hTarget, (congrArg Loc.cta hLoc).symm, hAct⟩
  | clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim

/-- The two score-ready histories start with their actual single-credit initializers. -/
theorem scoreReadyInitialized {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (scoreReadyObject l cta stage)) :
    PairTmaRing.InitFirst X (scoreReadyObject l cta stage) 1 := by
  fin_cases stage
  · exact (activeObjectHistory hp hX (10 : Fin 34) hr).1
  · exact (activeObjectHistory hp hX (11 : Fin 34) hr).1

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
