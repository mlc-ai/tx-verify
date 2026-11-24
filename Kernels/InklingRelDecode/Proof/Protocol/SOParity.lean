-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOHandoff

@[expose] public section

/-!
# The parity fields of `SO.Facts` from the roles' runs

`Facts.s_parity`, `p_parity` and `f_parity` say that a successful poll of the barrier has the
parity of its thread's earlier successful polls (offset 0). Each is the parity statement of one
role's execution-level theorem, once every poll of the barrier is an anchored run's:

* `s_parity_of_runs`: `s_ready b`'s polls are the softmax threads' (`SOSmExec.sm_swait_exec`);
* `p_parity_of_runs`: `p_ready b`'s polls are the MMA warp's (`SOMmaExec.mma_pwait_exec`);
* `f_parity_of_runs`: `o_final`'s polls are the epilogue threads' (`EpiRunAt`, `epi_fwait_exec`).

The anchoring premise of each (`hanch`) is the role-table protocol and the composed
default-partition thread, as for the KV ring: the poll belongs to a thread of the role, which is
in a run from the role's first state with no earlier poll of the barrier.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.SO
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ring (wAt countP_take_split)
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oFinal)

noncomputable section
set_option maxRecDepth 100000

/-! ### The epilogue on an execution -/

/-- **What the composed default-partition thread has to provide for the epilogue**: the events of
thread `g` from `k₀` are a run of the epilogue's machine from `d₀`, the events up to `k` reach `d`,
and the states of the run have the epilogue's invariant and `Epi.Means`. -/
structure EpiRunAt (Q : Params) (L : Launch) (X : Execution) (g k0 k : Nat) (d0 d : Epi.D) :
    Prop where
  trace : (Epi.code Epi.asms L g d0).toMachine.Trace (some d0) ((X.tr g).drop k0)
  reach : (Epi.code Epi.asms L g d0).toMachine.after (some d0)
    (((X.tr g).drop k0).take (k - k0)) = some (some d)
  inv : ∀ j < (((X.tr g).drop k0).take (k - k0)).length, ∃ d1 : Epi.D,
    (Epi.code Epi.asms L g d0).toMachine.after (some d0)
      ((((X.tr g).drop k0).take (k - k0)).take j) = some (some d1) ∧
      Epi.Inv d1 ∧ Epi.Means Q L g d1.pr
  last : Epi.Inv d ∧ Epi.Means Q L g d.pr

/-! ### The parity fields -/

variable {L : Launch} {X : Execution} {c : Nat}

end
end PTX.Kernels.InklingRelDecode.Proof.SO
