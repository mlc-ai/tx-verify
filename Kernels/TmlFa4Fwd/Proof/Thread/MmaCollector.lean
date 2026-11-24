-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Core.Tc.TcMmaCollector
import Lemmas.Flow.NotTcMma
import Lemmas.Flow.NotBulk
import Lemmas.Execution.EventFrameBase

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.EventFrame

private def usesCollector (c : TcMma.Collectors) : Tmpl → Prop
  | .tc (.mma _ spec _ _) _ => spec.collector = c
  | _ => True

private theorem ofExecUsesCollector {c : TcMma.Collectors} {r : Exec Tmpl}
    (h : AllOk (usesCollector c) r) : usesCollector c (ofExec r) := by
  cases r
  · trivial
  · exact h

private theorem mmaTmplCollector (l : Launch) (g : Nat) (t : TState) (op : TcMmaInstr) :
    usesCollector op.collectors (mmaTmpl l g t op) := by
  unfold mmaTmpl
  split
  · simp only [mmaSmemTmpl]
    apply ofExecUsesCollector
    repeat' first | trivial | (apply allOk_bind; intro) | (apply allOk_ite) | split
  · simp only [mmaTmemTmpl]
    apply ofExecUsesCollector
    repeat' first | trivial | (apply allOk_bind; intro) | (apply allOk_ite) | split
  · trivial

private def noReuse : Op → Bool
  | .tcMma op => !op.collectors.a.reuses && !op.collectors.b.reuses
  | _ => true

private theorem noReuseCode : kernel.code.all (fun ins => noReuse ins.op) = true := by
  decide +kernel

/-- Actual MMA issues have no collector reuse. This is independent of whether they complete. -/
theorem mmaCollectorsSafe {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) : TcMma.CollectorSafe X := by
  apply TcMma.collectorSafe_of_noReuse
  rintro i dst s accum mask ⟨site, he⟩
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨t, ins, _, _, hc, hf⟩
  · cases hBad
  have hm := fires_tcMma_op hf rfl
  have hAudited := List.all_eq_true.mp noReuseCode ins (List.mem_of_getElem? hc)
  cases hIns : ins.op <;> simp only [hIns, tcMmaOp, Bool.false_eq_true] at hm
  rename_i op
  rw [hIns] at hf
  change Fires site (mmaTmpl l i.1 t op) ⟨site, .tc (.mma dst s accum mask)⟩ _ at hf
  have hCollector := mmaTmplCollector l i.1 t op
  generalize mmaTmpl l i.1 t op = tm at hf hCollector
  cases tm <;> simp [Fires] at hf
  case tc kind _ =>
    obtain ⟨rfl, _⟩ := hf
    change s.collector = op.collectors at hCollector
    simpa [hCollector, hIns, noReuse] using hAudited

end PTX.Kernels.TmlFa4Fwd.Thread
