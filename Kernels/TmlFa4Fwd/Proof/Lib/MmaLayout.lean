-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.NotTcMma
public import Lemmas.Flow.NotBulk
public import Lemmas.Tcgen05.MmaOperandObservations
public import Lemmas.Tcgen05.TcMmaSingleLayout
public import Lemmas.Tcgen05.TcMmaSource
public import Lemmas.Tcgen05.TcMmaOperands

@[expose] public section

/-! # The MMAs' groups and layouts, from the code

Every MMA of the code is of one CTA (`actualMmaOwnership`), so its output layout is injective
(`actualMmaLayoutInjective`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Flow PTX.EventFrame

noncomputable section

private def hasMmaGroup (l : Launch) (cta : Nat) (group : CtaGroup) : Tmpl → Prop
  | .tc (.mma _ s _ _) _ => s.descriptor.group = group ∧ s.MatchesLaunch l cta
  | _ => True

private theorem operandsGroup {l : Launch} {cta bits : Nat} {group : CtaGroup}
    {ws : Bool} {kind : MmaKind} {d : TcMma.Descriptor} {a b : TcShared.Descriptor}
    {s : TcMma.OperandSpec} (hd : TcMma.decode group ws kind bits = some d)
    (hs : TcMma.makeOperands l cta d a b = some s) :
    s.descriptor.group = group ∧ s.MatchesLaunch l cta := by
  have hCtas := TcMma.makeOperands_matches hs
  unfold TcMma.makeOperands at hs
  obtain ⟨ctas, _, rest⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨low, _, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨high, _, hspec⟩ := Option.bind_eq_some_iff.mp rest
  have h : s = ⟨d, a, b, low, high, none, {}⟩ := by simpa using hspec.symm
  exact ⟨h.symm ▸ TcMma.decode_group hd, hCtas⟩

private theorem ofExec_hasMmaGroup {l : Launch} {cta : Nat} {group : CtaGroup} {r : Exec Tmpl}
    (h : AllOk (hasMmaGroup l cta group) r) : hasMmaGroup l cta group (ofExec r) := by
  cases r with
  | error => trivial
  | ok _ => exact h

private theorem fires_hasMmaGroup {l : Launch} {cta pc dst : Nat}
    {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {group : CtaGroup} {tmpl : Tmpl} {o : Option TState}
    (hf : Fires pc tmpl ⟨pc, .tc (.mma dst s acc mask)⟩ o)
    (hg : hasMmaGroup l cta group tmpl) :
    s.descriptor.group = group ∧ s.MatchesLaunch l cta := by
  cases tmpl <;> simp [Fires] at hf
  case tc k _ =>
    rcases hf with ⟨rfl, _⟩
    exact hg

private theorem mmaTmplGroup (l : Launch) (g : Nat) (t : TState) (m : TcMmaInstr) :
    hasMmaGroup l (g / l.block) m.group (mmaTmpl l g t m) := by
  unfold mmaTmpl
  split
  · simp only [mmaSmemTmpl]
    apply ofExec_hasMmaGroup
    repeat' first | trivial | (apply allOk_bind; intro) | (apply allOk_ite) | split
    rename_i hspec
    have hGroup := operandsGroup (by assumption) hspec
    exact hGroup
  · simp only [mmaTmemTmpl]
    apply ofExec_hasMmaGroup
    repeat' first | trivial | (apply allOk_bind; intro) | (apply allOk_ite) | split
    rename_i hspec
    have hGroup := operandsGroup (by assumption) hspec
    exact hGroup
  · trivial

private def singleMmaOp : Op → Bool
  | .tcMma op => op.group == .one
  | _ => true

private theorem singleMmaCode : kernel.code.all (fun i => singleMmaOp i.op) = true := by
  decide +kernel

/-- All actual MMA operand descriptors have the CTA-group qualifier of the frozen instructions. -/
theorem actualMmaOwnership {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {dst : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i dst s acc mask) :
    s.descriptor.group = .one ∧ s.MatchesLaunch l (i.1 / l.block) := by
  obtain ⟨pc, he⟩ := hi
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨t, ins, _, _, hc, hf⟩
  · cases hBad
  have hOp := fires_tcMma_op hf rfl
  have hSingle := List.all_eq_true.mp singleMmaCode ins (List.mem_of_getElem? hc)
  cases hInstr : ins.op <;> simp only [hInstr, tcMmaOp, Bool.false_eq_true] at hOp
  rename_i op
  have hGroup : op.group = .one := by simpa [hInstr, singleMmaOp] using hSingle
  rw [hInstr] at hf
  change Fires pc (mmaTmpl l i.1 t op) ⟨pc, .tc (.mma dst s acc mask)⟩ _ at hf
  obtain ⟨hD, hCtas⟩ := fires_hasMmaGroup hf (mmaTmplGroup l i.1 t op)
  exact ⟨hD.trans hGroup, hCtas⟩

/-- Every MMA uses the frozen single-CTA group. -/
theorem actualMmaGroup {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {dst : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i dst s acc mask) :
    s.descriptor.group = .one :=
  (actualMmaOwnership hX hi).1

/-- The actual issue layouts are injective independently of operand or commit completion. -/
theorem actualMmaLayoutInjective {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) : TcMma.LayoutInjective X := by
  intro i dst s acc mask hi row col row' col' cell h h'
  exact TcMma.writeCell_one_injective (actualMmaGroup hX hi) h h'

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
