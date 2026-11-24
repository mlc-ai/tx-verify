-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityCredits
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreReadyUpdate
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputFree
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit
public import Kernels.TmlFa4Fwd.Proof.CorrectionCreditBalance
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasCredits
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryDrainRelease
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFacts
public import Kernels.TmlFa4Fwd.Proof.Thread.Mma
import Kernels.TmlFa4Fwd.Proof.LoaderReadyBarriers
import Kernels.TmlFa4Fwd.Proof.LoaderReadyClosure
import Kernels.TmlFa4Fwd.Proof.LoaderRingMbarAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.AsyncCopy PTX.MBarrier Prologue

/-- The protocol responsible for each mbarrier that receives a counter update. -/
inductive MbarUpdateFamily
  | query (stage : Fin 2)
  | queryReturn (stage : Fin 2)
  | cacheReady (slot : Fin 3)
  | cacheEmpty (slot : Fin 3)
  | scoreReady (stage : Fin 2)
  | probability (stage packet : Fin 2)
  | outputCompletion (stage : Fin 2)
  | statisticsCredit (stage : Fin 2)
  | outputReady (stage : Fin 2)
  | outputFree (stage : Fin 2)
  | biasReady (stage : Fin 2)
  | biasEmpty (stage : Fin 2)

def MbarUpdateFamily.object (l : Launch) (cta : Nat) : MbarUpdateFamily → Loc
  | .query stage => Output.queryObject l cta stage
  | .queryReturn stage => Loader.queryEmptyObject l cta stage
  | .cacheReady slot => Loader.readyObject l (cta*l.block) slot
  | .cacheEmpty slot => Mma.Observation.emptyObject l (cta*l.block) slot
  | .scoreReady stage => Scores.scoreReadyObject l cta stage
  | .probability stage packet => Scores.probabilityObject l cta stage packet
  | .outputCompletion stage => outputCompletionObject l cta stage
  | .statisticsCredit stage => TmlFa4Fwd.Correction.statsCreditLoc l cta stage
  | .outputReady stage => Epilogue.readyLoc l (cta*l.block) stage
  | .outputFree stage => Output.freeObject l cta stage
  | .biasReady stage => Loader.biasReadyObject l cta stage
  | .biasEmpty stage => Loader.biasEmptyObject l cta stage

private def familyTable : List MbarUpdateFamily :=
  [.query 0, .query 1, .queryReturn 0, .queryReturn 1,
    .cacheReady 0, .cacheReady 1, .cacheReady 2, .cacheEmpty 0, .cacheEmpty 1, .cacheEmpty 2,
    .scoreReady 0, .scoreReady 1, .probability 0 0, .probability 1 0, .probability 0 1,
    .probability 1 1, .outputCompletion 0, .outputCompletion 1, .statisticsCredit 0,
    .statisticsCredit 1, .outputReady 0, .outputReady 1, .outputFree 0, .outputFree 1,
    .biasReady 0, .biasReady 1, .biasEmpty 0, .biasEmpty 1]

private def familyOffset : MbarUpdateFamily → Nat
  | .query stage => 8 * stage.val
  | .queryReturn stage => 16 + 8 * stage.val
  | .cacheReady slot => 32 + 8 * slot.val
  | .cacheEmpty slot => 56 + 8 * slot.val
  | .scoreReady stage => 80 + 8 * stage.val
  | .probability stage packet => 96 + 8 * stage.val + 16 * packet.val
  | .outputCompletion stage => 144 + 8 * stage.val
  | .statisticsCredit stage => 192 + 8 * stage.val
  | .outputReady stage => 208 + 8 * stage.val
  | .outputFree stage => 224 + 8 * stage.val
  | .biasReady stage => 320 + 8 * stage.val
  | .biasEmpty stage => 336 + 8 * stage.val

private theorem objectOfFamily {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (cta : Nat) (family : MbarUpdateFamily) :
    family.object l cta = ⟨.shared, cta, l.sharedBase + familyOffset family⟩ := by
  have hb : cta * l.block / l.block = cta := Nat.mul_div_cancel _ (by rw [hp.block]; decide)
  cases family with
  | cacheReady slot =>
    simp only [MbarUpdateFamily.object, Loader.readyObject, hb,
      TmlFa4Fwd.Loader.readySlot_address, familyOffset]
    congr 1
    omega
  | cacheEmpty slot =>
    simp only [MbarUpdateFamily.object, Mma.Observation.emptyObject, hb,
      TmlFa4Fwd.Loader.emptySlot_address, familyOffset]
    congr 1
    omega
  | outputReady => simp [MbarUpdateFamily.object,Epilogue.readyLoc,hb,familyOffset]
  | query => rfl
  | queryReturn => rfl
  | scoreReady => rfl
  | probability => rfl
  | outputCompletion => rfl
  | statisticsCredit => rfl
  | outputFree => rfl
  | biasReady => rfl
  | biasEmpty => rfl

/-- Every actual arrival or transaction update belongs to one of the live protocol objects. -/
theorem mbarUpdateFamily {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {loc : Loc} {r : Record Ref} (hr : r ∈ X.objects loc)
    (hu : (∃ count tx, r.action = .arrive count tx) ∨ ∃ bytes, r.action = .completeTx bytes) :
    ∃ (cta : Nat) (family : MbarUpdateFamily), loc = family.object l cta := by
  have lift {allowed : List Nat} (hAll : allowed.all
      (fun n => (familyTable.map familyOffset).contains n) = true)
      {i : EvId} (h : ∃ n ∈ allowed,
        loc = ⟨.shared,i.1/l.block,l.sharedBase+n⟩) :
      ∃ (cta : Nat) (family : MbarUpdateFamily), loc = family.object l cta := by
    obtain ⟨n,hn,hl⟩ := h
    have hm := List.contains_iff_mem.mp (List.all_eq_true.mp hAll n hn)
    obtain ⟨family,_,hEq⟩ := List.mem_map.mp hm
    exact ⟨i.1/l.block,family,by rw [objectOfFamily hp,hEq,hl]⟩
  cases record_source hX.tma.2.2.1 hr with
  | arrive _ he _ => exact lift (by decide) (actualArriveOffsetIn hp hX he)
  | commit _ he ht _ => exact lift (by decide) (actualCommitOffsetIn hp hX he ht)
  | @tensor i _ _ _ _ he hm _ =>
    obtain ⟨site,rfl⟩ := Loader.actualInputIssuePc hX he
    refine lift (i := i) (allowed := [0,8,320,328]) (by decide)
      ⟨Loader.inputBarrierBase site + (Loader.inputSite site).barrierOffset, ?_, ?_⟩
    · exact (by decide : ∀ s : Fin 14,
        Loader.inputBarrierBase s + (Loader.inputSite s).barrierOffset ∈ [0,8,320,328]) site
    · rw [← hm]
      exact Loader.loaderTensorOffset hp hX site he
  | @arriveOn _ pc _ _ _ he hm _ _ =>
    obtain ⟨⟨j,hPc⟩,hNoInc,_,_⟩ := Loader.actualAsyncArrival hX he
    have hSite : pc ∈ [674,904,1137,1342,1602,1735] := by
      rw [hPc]
      fin_cases j <;> decide
    obtain ⟨off, hOff, hLoc⟩ := Loader.loaderAsyncAddress hp hX (hNoInc ▸ he) hSite
    exact lift (allowed := [32,40,48]) (by decide) ⟨off,hOff,hm.symm.trans hLoc⟩
  | bulk _ he hc _ _ =>
    rw [(actualCopyShape hX ⟨_,he⟩).completion] at hc
    cases hc
  | clc _ he _ _ _ => exact (noClcIssue hX ⟨_,he⟩).elim
  | init _ _ ha | inval _ _ ha | wait _ _ ha | increment _ _ ha => simp [ha] at hu

end PTX.Kernels.TmlFa4Fwd.Thread
