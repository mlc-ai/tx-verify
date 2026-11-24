-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Data.Decoded
public import Lemmas.Clc.ClcExecution
public import Lemmas.Flow.NotBulk

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX.Flow

/-- The frozen kernel has no cluster launch cancellation instruction. -/
theorem kernel_noClc : Decoded.kernel.code.all (fun ins => !clcOp ins.op) = true := by
  decide +kernel

/-- No cancellation request can be issued by any prefix of the frozen kernel. -/
theorem noClcIssue {A : List Assumption} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l Decoded.kernel A m X) {i : EvId} {s : Clc.Spec} {targets : List Nat}
    (hi : X.ClcIssue i s targets) : False := by
  obtain ⟨_, he⟩ := hi
  exact no_kind_of_code hX clcOp (fun k => ∃ s t, k = .clcIssue s t)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_clcIssue_op hf hk)
    kernel_noClc he ⟨_, _, rfl⟩

/-- A canceled cluster requires a cancellation request in the actual execution. -/
theorem noCanceled {A : List Assumption} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l Decoded.kernel A m X) {g : Nat} : ¬ ClcCanceled l X g := by
  rintro ⟨_, req, ho⟩
  obtain ⟨i, s, targets, -, hi, -⟩ := ClcOk.canceled_has_issue hX.clc ho
  exact noClcIssue hX hi

end PTX.Kernels.TmlFa4Fwd
