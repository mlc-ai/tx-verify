-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.TmaWait
public import Kernels.TmlFa4Fwd.Proof.Lib.LdKvWait
public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Issue
public import Lemmas.Kernel.Progress.WaitSite
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

/-! # The kind of the instruction at each loader site -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

open PTX.Kernels.TmlFa4Fwd.Proof.Loader

/-- The instruction at a loader site's position. -/
private def insAt (n : Nat) : Option Instr :=
  if n < 543 then codeFrom 179 n else if n < 804 then codeFrom 543 n
  else if n < 1003 then codeFrom 804 n else if n < 1238 then codeFrom 1003 n
  else if n < 1469 then codeFrom 1238 n else if n < 1632 then codeFrom 1469 n
  else codeFrom 1632 n

private theorem insAt_eq {n : Nat} (h : 179 ≤ n) : insAt n = kernel.code[n]? := by
  unfold insAt
  split_ifs <;> exact codeFrom_eq (by omega)

private def chk (s : Loader.Site) : Bool :=
  decide (179 ≤ s.pc) && (decide (Loader.isWait s) || insOk (decide (s = .setmax)) (insAt s.pc)) &&
    (!kvSite s || match insAt s.pc with | some ins => Sched.waitOp ins.op | none => true)

private theorem ld_chk : AllSites fun s => chk s = true := by
  unfold AllSites; decide +kernel

/-- **A loader site that is no wait** has a checked instruction, the register request at the entry
only. -/
theorem ld_kind {s : Loader.Site} (h : ¬ Loader.isWait s) :
    siteOk s.pc false (decide (s = .setmax)) = true := by
  have hc := ld_chk.ok s
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [insAt_eq hc.1.1] at hc
  simpa [siteOk, h] using hc.1.2

/-- **A wait for an empty K/V slot** is an acquiring `try_wait`. -/
theorem ld_kv_wait_op {s : Loader.Site} (h : kvSite s = true) {ins : Instr}
    (hi : kernel.code[s.pc]? = some ins) : Sched.waitOp ins.op = true := by
  have hc := ld_chk.ok s
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [insAt_eq hc.1.1] at hc
  simpa [h, hi] using hc.2

private theorem tma_ops : AllSites fun s => (!tmaWaitSite s ||
    match kernel.code[s.pc]? with | some ins => Sched.waitOp ins.op | none => true) = true := by
  unfold AllSites; decide +kernel

/-- **A wait of a TMA group or the drain's Q wait** is an acquiring `try_wait`. -/
theorem ld_tma_wait_op {s : Loader.Site} (h : tmaWaitSite s = true) {ins : Instr}
    (hi : kernel.code[s.pc]? = some ins) : Sched.waitOp ins.op = true := by
  have := tma_ops.ok s
  simpa [h, hi] using this

end PTX.Kernels.TmlFa4Fwd.Proof.Top
