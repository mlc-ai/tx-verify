-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.NoEvents
public import Lemmas.Flow.NotTcMma
public import Core.Tc.TcMmaCollector

@[expose] public section

/-! # No MMA of the code reuses a collector buffer

A static scan: every `tcgen05.mma` of the code has the collector usage `fill` or `discard` for A
and B, so every issue's `Collectors` reuse nothing and `CollectorSafe` holds
(`collectorSafe_of_noReuse`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.EventFrame

noncomputable section

private def hasNoReuse : Tmpl → Prop
  | .tc (.mma _ s _ _) _ => s.collector.a.reuses = false ∧ s.collector.b.reuses = false
  | _ => True

private theorem ofExec_hasNoReuse {r : Exec Tmpl} (h : AllOk hasNoReuse r) :
    hasNoReuse (ofExec r) := by
  cases r with
  | error => trivial
  | ok _ => exact h

private theorem fires_hasNoReuse {pc dst : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {tmpl : Tmpl} {o : Option TState}
    (hf : Fires pc tmpl ⟨pc, .tc (.mma dst s acc mask)⟩ o) (hg : hasNoReuse tmpl) :
    s.collector.a.reuses = false ∧ s.collector.b.reuses = false := by
  cases tmpl <;> simp [Fires] at hf
  case tc k _ =>
    rcases hf with ⟨rfl, _⟩
    exact hg

private theorem mmaTmplNoReuse (l : Launch) (g : Nat) (t : TState) (m : TcMmaInstr)
    (hm : m.collectorA.reuses = false ∧ m.collectorB.reuses = false) :
    hasNoReuse (mmaTmpl l g t m) := by
  unfold mmaTmpl
  split
  · simp only [mmaSmemTmpl]
    apply ofExec_hasNoReuse
    repeat' first | trivial | (apply allOk_bind; intro) | (apply allOk_ite) | split
  · simp only [mmaTmemTmpl]
    apply ofExec_hasNoReuse
    repeat' first | trivial | (apply allOk_bind; intro) | (apply allOk_ite) | split
  · trivial

private def noReuseOp : Op → Bool
  | .tcMma op => !op.collectorA.reuses && !op.collectorB.reuses
  | _ => true

private theorem noReuseCode : kernel.code.all (fun i => noReuseOp i.op) = true := by
  decide +kernel

/-- **No MMA issue reuses a collector buffer.** -/
theorem mmaNoReuse {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {dst : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i dst s acc mask) :
    s.collector.a.reuses = false ∧ s.collector.b.reuses = false := by
  obtain ⟨pc, he⟩ := hi
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨t, ins, _, _, hc, hf⟩
  · cases hBad
  have hOp := fires_tcMma_op hf rfl
  have hSingle := List.all_eq_true.mp noReuseCode ins (List.mem_of_getElem? hc)
  cases hInstr : ins.op <;> simp only [hInstr, tcMmaOp, Bool.false_eq_true] at hOp
  rename_i op
  have hr : op.collectorA.reuses = false ∧ op.collectorB.reuses = false := by
    simpa [hInstr, noReuseOp] using hSingle
  rw [hInstr] at hf
  change Fires pc (mmaTmpl l i.1 t op) ⟨pc, .tc (.mma dst s acc mask)⟩ _ at hf
  exact fires_hasNoReuse hf (mmaTmplNoReuse l i.1 t op hr)

/-- **`CollectorSafe`**: no issue reuses a buffer. -/
theorem collectorSafe_mma {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) : TcMma.CollectorSafe X :=
  TcMma.collectorSafe_of_noReuse fun _ _ _ _ _ hi => mmaNoReuse hX hi

end
end PTX.Kernels.InklingRelDecode.Proof.Lib
