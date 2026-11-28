-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.Requests
public import Kernels.InklingRelDecode.Proof.Dispatch.Publication
public import Kernels.InklingRelDecode.Proof.Lib.RegLedger

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX

theorem reg_ledger (s : Site) (n : Nat)
    (early : s = .idleDec ∨ s = .idleSync ∨ s = .idleSyncAgain ∨ s = .idleInc ∨
      s = .loaderEntry ∨ s = .mmaEntry → n = 0)
    (late : s = .exitSync ∨ s = .exitDealloc ∨ s = .ret → 1 ≤ n)
    (good : s ≠ .badSync ∧ s ≠ .badSyncAgain) :
    Lib.ledgerOk s.pc (publicationPhase ⟨s,n⟩) (requestPhase ⟨s,n⟩) = true := by
  obtain ⟨g1,g2⟩ := good
  have ne0 : 3*n ≠ 0 → n ≠ 0 := by omega
  cases s <;> simp [Lib.ledgerOk,Lib.requestPcs,Lib.barOneSites,publicationPhase,requestPhase,
    publicationOffset,requestOffset,Site.pc] at * <;> omega

theorem request_group (s : Site) (h : s.pc ∈ Lib.requestPcs) : Lib.workerReq s.pc = true := by
  revert h
  cases s <;> decide

end PTX.Kernels.InklingRelDecode.Proof.Dispatch
