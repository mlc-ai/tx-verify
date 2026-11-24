-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Machine
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Issue
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

/-! # The kind of the instruction at each site of the output warp -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

def outSites : List Epilogue.Site :=
  .start :: ([Epilogue.Scan.first, .loop, .second, .loop2].flatMap fun k =>
    [.word k, .down k, .total k] ++ (List.finRange 5).map (.up k)) ++
  ([false, true].flatMap fun l => [.vote l, .pre l, .tiles l, .exit l]) ++ [.q0, .q1] ++
  ((List.finRange 2).flatMap fun st => [.commit st, .drain st, .free st] ++
    (List.finRange 4).map (.store st))

private theorem out_kinds :
    outSites.all (fun s => siteOk s.pc false (decide (s = .start))) = true := by
  decide +kernel

/-- **A site of the output warp that is no ready poll** has a checked instruction, the register
request at the entry only. -/
theorem out_kind {s : Epilogue.Site} (h : ∀ st, s ≠ .ready st) :
    siteOk s.pc false (decide (s = .start)) = true := by
  refine List.all_eq_true.mp out_kinds s ?_
  cases s with
  | start => simp [outSites]
  | word k | down k | total k => cases k <;> simp [outSites]
  | up k j => cases k <;> simp [outSites]
  | vote l | pre l | tiles l | exit l => cases l <;> simp [outSites]
  | q0 | q1 => simp [outSites]
  | ready st => exact absurd rfl (h st)
  | store st b | commit st | drain st | free st => fin_cases st <;> simp [outSites]

end PTX.Kernels.TmlFa4Fwd.Proof.Top
