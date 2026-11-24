-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LedgerClosure
public import Kernels.InklingRelDecode.Proof.Thread.LkD
public import Kernels.InklingRelDecode.Proof.Thread.LkWStep
public import Kernels.InklingRelDecode.Proof.Thread.LkB0
public import Kernels.InklingRelDecode.Proof.Progress.WtTime

@[expose] public section

/-!
# Two static facts for the time along a trace

* `dispatch_time`: the dispatch enters a role at its first state, timed `c0 + 4`, or the exit at
  `c4`.
* `wait_notSy`: the polls (the softmax region's `waitS` and `waitO`, the loader's `wait`, the
  MMA warp's `kvWait` and `pWait`, the epilogue's `wait`) are not synchronizing positions.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX.Kernels.InklingRelDecode.Proof.Ledger (wKind)

noncomputable section
set_option maxRecDepth 100000

/-- **The dispatch's successor**: a role's first state at `c0 + 4`, or the exit's at `c4`. -/
theorem dispatch_time {L : Launch} {g : Nat} {P : Loader.Pro} {e : Event} {s' : WComp.WSt}
    (h : WComp.next L g (.worker ⟨.ldRole, P⟩) e = some (some s')) :
    (wKind s' = 1 → wcompT s' = c0 + 4) ∧ (wKind s' = 2 → wcompT s' = c4) := by
  simp only [WComp.next, WComp.dispatch] at h
  split at h
  · rename_i d' _
    obtain ⟨site, Q⟩ := d'
    cases site <;> simp only [WComp.roleStart] at h <;> (repeat' split at h) <;>
      simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      simp [wKind, wcompT, loaderT, mmaT, idleT, exitT, Loader.D.start, Worker.Idle.D.start]
  · simp at h
  · simp at h

/-- **The polls are not synchronizing positions.** -/
theorem wait_notSy : syAt Sm.Site.waitS.pc 0 = false ∧ syAt Sm.Site.waitO.pc 0 = false ∧
    syAt Loader.Site.wait.pc 0 = false ∧ syAt Mma.Site.kvWait.pc 0 = false ∧
    syAt Mma.Site.pWait.pc 0 = false ∧ syAt Epi.Site.wait.pc 0 = false := by
  decide +kernel

end
end PTX.Kernels.InklingRelDecode.Proof.Lk
