-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
public import Lemmas.Protocol.PairTmaRing.Hyp
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
import Kernels.TmlFa4Fwd.Proof.MbarSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores

open PTX PTX.AsyncCopy PTX.MBarrier

/-- Each stage has a joint probability/rescale object and a tail-probability object. -/
def probabilityObject (l : Launch) (cta : Nat) (stage packet : Fin 2) : Loc :=
  ⟨.shared, cta, l.sharedBase + (96 + 8 * stage.val + 16 * packet.val)⟩

def probabilityCredits (packet : Fin 2) : Nat := if packet.val = 0 then 256 else 4

/-- The per-stage credit is an issued ordinary release on the selected physical object. -/
def ProbabilityCredit (l : Launch) (X : Execution) (i : EvId) (cta : Nat)
    (stage packet : Fin 2) : Prop :=
  X.Arrive i (probabilityObject l cta stage packet) 0 1 true .cta

/-- Every actual probability update has a unit thread arrival as its source. -/
theorem probabilityUpdate {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage packet : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (probabilityObject l cta stage packet))
    (hUpdate : CounterUpdate r.action) :
    ∃ i, r.id = .thread i ∧ ProbabilityCredit l X i cta stage packet ∧
      i.1 / l.block = cta ∧ r.action = .arrive 1 0 := by
  let target := probabilityObject l cta stage packet
  let offset := 96 + 8 * stage.val + 16 * packet.val
  have hOffset : offset ∈ [96, 104, 112, 120] := by
    fin_cases stage <;> fin_cases packet <;> decide
  have address {off owner : Nat}
      (h : target = ⟨.shared, owner, l.sharedBase + off⟩) : off = offset := by
    have ha : l.sharedBase + offset = l.sharedBase + off := congrArg Loc.addr h
    omega
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha | wait _ _ ha | inval _ _ ha => rw [ha] at hUpdate; exact hUpdate.elim
  | arrive hId he hAct =>
    rename_i g j pc tx count rel scope
    have hShape := actualProbabilityArrivalSite hp hX he hOffset rfl
    have heq : 0 = tx ∧ 1 = count ∧ true = rel ∧ MbarScope.cta = scope := by
      rcases hShape with ⟨site, rfl⟩ | hSite
      · obtain ⟨hTx, hCount, hRel, hScope, _, _⟩ := Softmax.probabilityArriveFacts hp hX site he
        exact ⟨hTx.symm, hCount.symm, hRel.symm, hScope.symm⟩
      · obtain ⟨hTx, hCount, hRel, hScope, _, _⟩ :=
          TmlFa4Fwd.Correction.correctionProbabilityCredit hp hX he hSite
        exact ⟨hTx.symm, hCount.symm, hRel.symm, hScope.symm⟩
    rcases heq with ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨_, _, hLoc⟩ := actualArriveOffsetIn hp hX he
    exact ⟨(g, j), hId, ⟨_, he⟩, (congrArg Loc.cta hLoc).symm, hAct⟩
  | increment _ he _ => exact (Loader.noIncrementingCopyArrival hX ⟨_, he⟩).elim
  | tensor _ he hTarget _ =>
    obtain ⟨site, rfl⟩ := Loader.actualInputIssuePc hX he
    have hLoc := Loader.loaderTensorOffset hp hX site he
    have audit : ∀ j : Fin 14, Loader.inputBarrierBase j + (Loader.inputSite j).barrierOffset
        ∉ [96, 104, 112, 120] := by decide
    exact (audit site ((address (hTarget.symm.trans hLoc)).symm ▸ hOffset)).elim
  | arriveOn _ he hTarget _ _ =>
    obtain ⟨⟨site, rfl⟩, rfl, _, _⟩ := Loader.actualAsyncArrival hX he
    have hSite := (by decide : ∀ j : Fin 6,
      Loader.copyCommitPc j + 1 ∈ [674, 904, 1137, 1342, 1602, 1735]) site
    obtain ⟨off, hOff, hLoc⟩ := Loader.loaderAsyncAddress hp hX he hSite
    have hEq := address (hTarget.symm.trans hLoc)
    have audit : ∀ j ∈ [32, 40, 48], j ∉ [96, 104, 112, 120] := by decide
    exact (audit off hOff (hEq.symm ▸ hOffset)).elim
  | bulk _ he hCompletion _ _ =>
    rw [(actualCopyShape hX ⟨_, he⟩).completion] at hCompletion
    cases hCompletion
  | commit _ he hTarget _ =>
    rcases inCommitSites hX he with hFixed | hRing
    · obtain ⟨off, hOff, hLoc⟩ := Mma.mmaFixedCommitAddress hp hX he hFixed hTarget
      have hOut := address hLoc
      have audit : ∀ j ∈ [16, 24, 56, 80, 88, 144, 152], j ∉ [96, 104, 112, 120] :=
        by decide
      exact (audit off hOff (hOut.symm ▸ hOffset)).elim
    · obtain ⟨slot, hLoc⟩ := Mma.mmaRingCommitAddress hp hX he hRing hTarget
      have hOut := address hLoc
      have audit : ∀ j : Fin 3, 8 * j.val + 56 ∉ [96, 104, 112, 120] := by decide
      exact (audit slot (hOut.symm ▸ hOffset)).elim
  | clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim

/-- The probability history begins with the initializer for its actual packet and stage. -/
theorem probabilityInitialized {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage packet : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (probabilityObject l cta stage packet)) :
    PairTmaRing.InitFirst X (probabilityObject l cta stage packet) (probabilityCredits packet) := by
  fin_cases packet <;> fin_cases stage
  · exact (activeObjectHistory hp hX (12 : Fin 34) hr).1
  · exact (activeObjectHistory hp hX (13 : Fin 34) hr).1
  · exact (activeObjectHistory hp hX (14 : Fin 34) hr).1
  · exact (activeObjectHistory hp hX (15 : Fin 34) hr).1

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
