-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MbarRecordOwner
public import Kernels.TmlFa4Fwd.Proof.MmaLayoutSafety
public import Kernels.TmlFa4Fwd.Proof.MmaQkIssue
public import Lemmas.Execution.NoTcCp

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX

private theorem noTcCopy : kernel.NoTcCp = true := by decide +kernel

/-- The launch's singleton clusters contain exactly one CTA. -/
theorem sameClusterOwner {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {issuer owner : Nat} (h : CtaInCluster l issuer owner) : owner = issuer := by
  have hc := h.2.2
  rw [Launch.oneDim_clusterOfCta hp.cluster.2.2, Launch.oneDim_clusterOfCta hp.cluster.2.2,
    hp.cluster.1, Nat.div_one, Nat.div_one] at hc
  exact hc.symm

/-- Both operand CTA identities of an actual MMA are the issuing CTA. -/
theorem mmaOperandOwners {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {dst : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i dst s acc mask) :
    s.lowCta = i.1 / l.block ∧ s.highCta = i.1 / l.block := by
  obtain ⟨hGroup, members, hMembers, hlo, hhi⟩ := Mma.actualMmaOwnership hX hi
  obtain ⟨_, he⟩ := hi
  rw [hGroup, Mma.singleCtaGroup hp (PTX.Proof.event_thread_lt hX he)] at hMembers
  obtain rfl := Option.some.inj hMembers.symm
  exact ⟨(Option.some.inj hlo).symm, (Option.some.inj hhi).symm⟩

/-- A final asynchronous stage uses the shared memory of its issuing CTA. -/
theorem finalStageOwnsShared {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {part : AsyncCopy.Part} {owner : Nat}
    (hStage : AsyncCopy.FinalStage X i part) (hUse : StageUses X i part owner) :
    owner = i.1 / l.block := by
  cases part <;> try (exact False.elim hUse)
  case writeCopy =>
    obtain ⟨s, hi, _, hDest | hSource⟩ := hUse
    · exact hDest.2.symm.trans (actualCopyFrame hX hi).2
    · rw [(actualCopyShape hX hi).srcGlobal] at hSource
      cases hSource.1
  case notifyCopy =>
    obtain ⟨s, _, hi, hc, _⟩ := hUse
    rw [(actualCopyShape hX hi).completion] at hc
    cases hc
  case notifyLoad =>
    obtain ⟨_, s, hi, _, hOwner⟩ := hUse
    exact hOwner.symm.trans (sameClusterOwner hp (actualTensorRoute hX hi).2.2.2.2.1)
  case notifyCta c =>
    rcases hStage with ⟨_, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ |
      ⟨s, targets, t, hi, _, _⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
    all_goals first | cases h | exact (noClcIssue hX hi).elim
  case tcNotify rank =>
    obtain ⟨s, target, hi, hTarget, hOwner⟩ := hUse
    exact hOwner.symm.trans (actualCommitTargetOwner hp hX hi hTarget)
  case mmaDone =>
    rcases hUse with ⟨dst, s, acc, mask, hi, hOwner⟩ | ⟨cp, hi, _⟩
    · obtain ⟨hlo, hhi⟩ := mmaOperandOwners hp hX hi
      exact hOwner.elim (·.trans hlo) (·.trans hhi)
    · exact (noCp_of_consistent noTcCopy hX i cp hi).elim

end PTX.Kernels.TmlFa4Fwd.Safety
