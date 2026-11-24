-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LedgerClosure

@[expose] public section

/-!
# The barrier-0 instruction of a state, by machine

The kernel's instructions on named barrier 0 are `bar.sync 0` (the common start's two, the
epilogue's last, and the exit role's) and `bar.sync 0, 128` (the prologue's and the softmax
loop's). `b0At pc` is 1 for the first form, 2 for the second, 0 for no instruction of barrier 0.

* the common start (`DStart`): sites `bar0` and `bar1` are 1, the others 0;
* the prologue and the softmax region: never 1;
* the epilogue: 1 at `bar3`, else 0;
* the worker: `bar0` and `bar1` are 1, never 2; its roles' sites are 0; the exit role's `bar` is 1.

`fin` is one at the states after the last `bar.sync 0` of a thread (the epilogue's `dealloc` and
`exit`, the exit role's `ret`), and `finBar` at the states of that barrier.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The instruction at `pc` on named barrier 0: 1 for `bar.sync 0`, 2 for `bar.sync 0, 128`. -/
def b0At (pc : Nat) : Nat :=
  match kernel.code[pc]? with
  | some ins =>
    match ins.op with
    | .barSync (.imm 0) _ => 1
    | .barSyncN (.imm 0) (.imm 128) _ => 2
    | _ => 0
  | none => 0

theorem dstart_b0 (s : DStart.Site) :
    b0At s.pc = (match s with | .bar0 | .bar1 => 1 | _ => 0) := by
  cases s <;> decide +kernel

theorem pro_b0 (s : ProA.Site) : b0At s.pc ≠ 1 := by
  cases s <;> decide +kernel

theorem sm_b0 (s : Sm.Site) : b0At s.pc ≠ 1 := by
  cases s <;> first | decide +kernel | (rename_i j; revert j; decide +kernel)

theorem epi_b0 (s : Epi.Site) : b0At s.pc = (match s with | .bar3 => 1 | _ => 0) := by
  cases s <;> first | decide +kernel | (rename_i j; revert j; decide +kernel)

theorem worker_b0 (s : Worker.Site) :
    b0At s.pc = (match s with | .bar0 | .bar1 | .toExit => 1 | _ => 0) := by
  cases s <;> decide +kernel

theorem idle_b0 (s : Worker.Idle.Site) : b0At s.pc = 0 := by
  cases s <;> decide +kernel

theorem loader_b0 (s : Loader.Site) : b0At s.pc = 0 := by
  cases s <;> decide +kernel

theorem mma_b0 (s : Mma.Site) : b0At s.pc = 0 := by
  cases s <;> first | decide +kernel | (rename_i j; revert j; decide +kernel)

theorem exit_b0 (s : WComp.ExitSite) : b0At s.pc = (match s with | .bar => 1 | .ret => 0) := by
  cases s <;> decide +kernel

end
end PTX.Kernels.InklingRelDecode.Proof.Ledger
