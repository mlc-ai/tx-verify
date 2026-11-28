-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Requests
public import Kernels.InklingRelDecode.Proof.Prologue.Publication
public import Kernels.InklingRelDecode.Proof.Lib.RegLedger

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX Control

theorem reg_ledger (s : Site) :
    Lib.ledgerOk s.pc (publicationPhase s) (requestPhase s) = true := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

theorem request_group (s : Site) (h : s.pc ∈ Lib.requestPcs) : Lib.dataReq s.pc = true := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

end PTX.Kernels.InklingRelDecode.Proof.Prologue
