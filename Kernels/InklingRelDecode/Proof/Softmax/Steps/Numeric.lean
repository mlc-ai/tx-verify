-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Live
public import Kernels.InklingRelDecode.Proof.Lib.CtlSteps
public import Lemmas.Flow.CtlStepsU
import Kernels.InklingRelDecode.Flow.Code.Part020
import Kernels.InklingRelDecode.Flow.Code.Part022
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow

private noncomputable def checked (a b keepPc : Nat) :=
  Havoc.check Lib.hooks (ctlLive keepPc) a b ((kernel.code.drop a).take (b-a))

private theorem length_code : kernel.code.length = 2856 := by kernel_rfl

private theorem carry {a b c L g} (v : Nat → Value) (ab : a ≤ b) (bl : b ≤ 2856)
    (hc : checked a b c = true) : SegU kernel Assumptions.all L g
      a (factsFrom (ctlLive c) v) b (factsFrom (ctlLive c) v) := by
  apply SegU.of_havoc Lib.rulesFrame Lib.hooks_ok ab (length_code ▸ bl)
  · rwa [factsFrom_keys]
  · exact fun _ h => h

private theorem scoreChecks :
    [(1299,1302),(1303,1466),(1467,1756),(1756,1764),(1764,1838)].all
      (fun (a,b) => checked a b 1838) = true := by kernel_rfl

/-- Both data-dependent mask branches rejoin before the first reduction shuffle.
The score and bias payload registers are unconstrained on either arm. -/
theorem score_to_shuffle {L g} (v : Nat → Value) :
    SegU kernel Assumptions.all L g 1299 (factsFrom (ctlLive 1838) v)
      1838 (factsFrom (ctlLive 1838) v) := by
  let F := factsFrom (ctlLive 1838) v
  have run (a b : Nat) (h : (a,b) ∈ [(1299,1302),(1303,1466),(1467,1756),
      (1756,1764),(1764,1838)]) : SegU kernel Assumptions.all L g a F b F := by
    have order : a ≤ b ∧ b ≤ 2856 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
      omega
    exact carry v order.1 order.2 (List.all_eq_true.mp scoreChecks _ h)
  have finish := run 1764 1838 (by decide)
  have tail' := (run 1756 1764 (by decide)).comp finish
  have inner := SegU.branch_join Flow.code_1466 Lib.bra_rule (segFree (by decide))
    tail' ((run 1467 1756 (by decide)).comp tail')
  exact (run 1299 1302 (by decide)).comp (SegU.branch_join Flow.code_1302 Lib.bra_rule
    (segFree (by decide)) finish ((run 1303 1466 (by decide)).comp inner))

private theorem expChecks : checked 1839 2234 2234 = true := by kernel_rfl

/-- The entire exponential and row-sum window, including the sixteen software
segments, preserves the control facts at the second reduction shuffle. -/
theorem exp_to_shuffle {L g} (v : Nat → Value) :
    SegU kernel Assumptions.all L g 1839 (factsFrom (ctlLive 2234) v)
      2234 (factsFrom (ctlLive 2234) v) :=
  carry v (by decide) (by decide) expChecks

private theorem productChecks : checked 2262 2326 2326 = true := by kernel_rfl

theorem products_to_bar {L g} (v : Nat → Value) :
    SegU kernel Assumptions.all L g 2262 (factsFrom (ctlLive 2326) v)
      2326 (factsFrom (ctlLive 2326) v) :=
  carry v (by decide) (by decide) productChecks

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
