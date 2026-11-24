-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasCredits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Softmax
open PTX PTX.AsyncCopy PTX.MBarrier Thread.Loader
open PTX.Kernels.TmlFa4Fwd.Loader

/-- Every update of a Bias return object is a unit release from softmax. -/
theorem biasEmptyUpdate {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (biasEmptyObject l cta stage)) (hu : CounterUpdate r.action) :
    ∃ issue, r.id = .thread issue ∧ X.Arrive issue (biasEmptyObject l cta stage) 0 1 true .cta ∧
      issue.1 / l.block = cta ∧ Prologue.warpIndex l issue.1 < 8 ∧
      Prologue.warpIndex l issue.1 / 4 = stage.val ∧
      r.action = .arrive 1 0 := by
  have offset {off owner : Nat}
      (h : biasEmptyObject l cta stage = ⟨.shared, owner, l.sharedBase + off⟩) :
      off = 336 + 8 * stage.val := by
    have hAddr := congrArg Loc.addr h
    change l.sharedBase + (336 + 8 * stage.val) = l.sharedBase + off at hAddr
    omega
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha | wait _ _ ha | inval _ _ ha => rw [ha] at hu; exact hu.elim
  | arrive hid he ha =>
    have hsite := actualBiasEmptyArrivalSite hp hX stage he rfl
    obtain ⟨rfl, rfl, rfl, rfl, hWarp, hTarget⟩ :=
      PTX.Kernels.TmlFa4Fwd.Softmax.biasEmptyArriveFacts hp hX he hsite
    have hOff := offset hTarget
    have hStage := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 8) (Nat.add_left_cancel hOff)
    exact ⟨_, hid, ⟨_, he⟩, (congrArg Loc.cta hTarget).symm, hWarp, hStage, ha⟩
  | increment _ he _ => exact (noIncrementingCopyArrival hX ⟨_, he⟩).elim
  | tensor _ he hl _ =>
    obtain ⟨site, rfl⟩ := actualInputIssuePc hX he
    obtain ⟨off, ho, hLoc⟩ := loaderTensorAddress hp hX site he
    rw [offset (hl.symm.trans hLoc)] at ho
    fin_cases stage <;> simp at ho
  | arriveOn _ he hl _ _ =>
    obtain ⟨⟨site, rfl⟩, rfl, _, _⟩ := actualAsyncArrival hX he
    have hs : copyCommitPc site + 1 ∈ [674, 904, 1137, 1342, 1602, 1735] := by
      fin_cases site <;> decide
    obtain ⟨off, ho, hLoc⟩ := loaderAsyncAddress hp hX he hs
    rw [offset (hl.symm.trans hLoc)] at ho
    fin_cases stage <;> simp at ho
  | bulk _ he hCompletion _ _ =>
    rw [(actualCopyShape hX ⟨_, he⟩).completion] at hCompletion
    cases hCompletion
  | commit _ he ht _ =>
    rcases inCommitSites hX he with hf | hr
    · obtain ⟨off, hoff, hLoc⟩ := Mma.mmaFixedCommitAddress hp hX he hf ht
      rw [offset hLoc] at hoff
      fin_cases stage <;> simp at hoff
    · obtain ⟨slot, hLoc⟩ := Mma.mmaRingCommitAddress hp hX he hr ht
      have hOff := offset hLoc
      have := stage.isLt
      have := slot.isLt
      omega
  | clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim

end PTX.Kernels.TmlFa4Fwd.Thread.Softmax
