-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Places
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Issue
public import Lemmas.Kernel.Progress.WaitSite
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

/-! # The kind of the instruction at each correction site -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

/-- The instruction at a site is checked from the first site's position on. -/
private def chk (s : Correction.Site) : Bool :=
  decide (7746 ≤ s.pc) && (if s.isPoll then
    match (kernel.code.drop 7746)[s.pc - 7746]? with
    | some ins => Sched.waitOp ins.op
    | none => true
  else insOk (decide (s = .setmax)) (kernel.code.drop 7746)[s.pc - 7746]?)

private theorem chk_all : Correction.allSites.all chk = true := by decide +kernel

private theorem chk_ok (s : Correction.Site) : chk s = true :=
  List.all_eq_true.mp chk_all s (Correction.mem_allSites s)

private theorem code_at {n : Nat} (h : 7746 ≤ n) :
    (kernel.code.drop 7746)[n - 7746]? = kernel.code[n]? := by
  rw [List.getElem?_drop, Nat.add_sub_cancel' h]

/-- **A correction site that is no wait** has a checked instruction, the register request at the
entry only. -/
theorem corr_kind {s : Correction.Site} (h : s.isPoll = false) :
    siteOk s.pc false (decide (s = .setmax)) = true := by
  have hc := chk_ok s
  simp only [chk, h, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true, ite_false] at hc
  rw [code_at hc.1] at hc
  simpa [siteOk] using hc.2

/-- **A correction poll site** is an acquiring `try_wait`. -/
theorem corr_wait {s : Correction.Site} (h : s.isPoll = true) {ins : Instr}
    (hi : kernel.code[s.pc]? = some ins) : Sched.waitOp ins.op = true := by
  have hc := chk_ok s
  simp only [chk, h, Bool.and_eq_true, decide_eq_true_eq, ite_true] at hc
  rw [code_at hc.1, hi] at hc
  exact hc.2

end PTX.Kernels.TmlFa4Fwd.Proof.Top
