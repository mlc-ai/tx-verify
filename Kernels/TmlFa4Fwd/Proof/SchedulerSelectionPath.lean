-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Local
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.WarpScan
public import Lemmas.Flow.TauFrame
public import Lemmas.Kernel.ReadValue
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Proof.SchedulerBallot
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionObservations
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionReads

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Carry register facts protected by a decoded one-step scheduler write set. -/
theorem schedulerOneStepFrame {l : Launch} {g pc nextPc : Nat} {t u : TState}
    {F G : List (Nat × Value)} {ins : Instr} (ht : At t pc F) (hu : At u nextPc G)
    (hc : kernel.code[pc]? = some ins) (hr : run kernel [] l g 1 t = some u)
    (hF : ∀ pair ∈ F, pair.1 ∉ writesRegs ins.op) : At u nextPc (G ++ F) := by
  have hTau : Tau kernel [] l g t u := by
    apply tauStep_iff.mp
    cases hStep : tauStep kernel [] l g t <;> simp [run, hStep] at hr ⊢
    exact hr
  have hCode : kernel.code[t.pc]? = some ins := by rw [ht.1]; exact hc
  have hKeep : Holds u.regs F := by
    induction F with
    | nil => trivial
    | cons pair F ih =>
      refine ⟨(tau_core_regs hCode hTau (hF pair (by simp))).trans ht.2.2.2.2.1, ?_⟩
      exact ih (ht.mono ht.2.2.2.2.2) (fun pair hm => hF pair (List.mem_cons_of_mem _ hm))
  exact hu.mono ((holds_append ..).mpr ⟨hu.2.2.2.2, hKeep⟩)

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
