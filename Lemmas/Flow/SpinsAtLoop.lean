-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.PollShape

@[expose] public section

/-! # Self-loop polls are canonical spins

A proof tool for the shape facts of a kernel's wait loops (DEP-CANONICAL-SPIN). A position whose
instruction is the unguarded poll `L: mbarrier.try_wait p, [base + off], par` and whose next
instruction is `@!p bra L` heads a canonical spin of shape B, exiting to `pc + 2`
(`Kernel.spinExit?_of_selfLoop`), provided `p` is neither the address register nor the parity
operand and no branch of the kernel targets `L + 1`; the kernel decides that the poll's predicate
is read nowhere else (`Kernel.SpinPred`), and obtains the canonical spin
(`Kernel.canonicalSpin_of_selfLoop`). A position that holds no poll writes no predicate, so it
heads no spin shape (`Kernel.spinExit?_eq_none_of_notWait`). -/

namespace PTX
noncomputable section

namespace Kernel

variable {K : Kernel}

/-- The parity operand reads no register when it is not `p`. -/
theorem Opnd.not_mem_regs_of_ne {par : Opnd} {p : Nat} (h : par ≠ .reg p) :
    p ∉ par.regs := by
  cases par with
  | reg r =>
    have hr : p ≠ r := fun he => h (by rw [he])
    simp [Opnd.regs, hr]
  | _ => simp [Opnd.regs]

/-- The poll `mbarrier.try_wait p, [base + off], par` writes the predicate `p` and does not read
it, when `p` is neither the address register nor the parity operand. -/
theorem mbarWait_readsReg_of_ne {p base : Nat} {off : Int} {par : Opnd} {acq : Bool}
    {sc : MbarScope} (hbase : base ≠ p) (hpar : par ≠ .reg p) :
    (⟨none, .mbarWait p base off par acq sc⟩ : Instr).readsReg p = false := by
  have hp : p ≠ base := fun he => hbase he.symm
  simp [Instr.readsReg, Op.readRegs, hp, Opnd.not_mem_regs_of_ne hpar]

/-- The poll at `pc` writes the predicate `p` when `p` is neither the address register nor the
parity operand. -/
theorem pollDst_of_code {pc p base : Nat} {off : Int} {par : Opnd} {acq : Bool}
    {sc : MbarScope} (h : K.code[pc]? = some { op := .mbarWait p base off par acq sc })
    (hbase : base ≠ p) (hpar : par ≠ .reg p) : K.pollDst pc = some p := by
  unfold Kernel.pollDst
  rw [h]
  show (if (⟨none, .mbarWait p base off par acq sc⟩ : Instr).readsReg p then none else some p) =
    some p
  rw [mbarWait_readsReg_of_ne hbase hpar]
  rfl

/-- **A poll followed by `@!p bra pc` heads a canonical spin of shape B**, with the exit at
`pc + 2`, when no branch of the kernel targets the branch after the poll. -/
theorem spinExit?_of_selfLoop {pc p base : Nat} {off : Int} {par : Opnd} {acq : Bool}
    {sc : MbarScope} {uni : Bool}
    (h0 : K.code[pc]? = some { op := .mbarWait p base off par acq sc })
    (h1 : K.code[pc + 1]? = some { guard := some (p, true), op := .bra pc uni })
    (hbase : base ≠ p) (hpar : par ≠ .reg p) (htg : K.targeted (pc + 1) = false) :
    K.spinExit? pc = some (pc + 2) := by
  unfold Kernel.spinExit?
  rw [pollDst_of_code h0 hbase hpar, h1]
  show (if (p == p && pc == pc) && !K.targeted (pc + 1) then some (pc + 2) else none) =
    some (pc + 2)
  rw [htg]
  simp

/-- **The poll of such a loop is a canonical spin** once its predicate is read nowhere but in the
loop's branch (`Kernel.SpinPred`, decided on the kernel's code). -/
theorem canonicalSpin_of_selfLoop {pc p base : Nat} {off : Int} {par : Opnd} {acq : Bool}
    {sc : MbarScope} {uni : Bool}
    (h0 : K.code[pc]? = some { op := .mbarWait p base off par acq sc })
    (h1 : K.code[pc + 1]? = some { guard := some (p, true), op := .bra pc uni })
    (hbase : base ≠ p) (hpar : par ≠ .reg p) (htg : K.targeted (pc + 1) = false)
    (hpred : K.SpinPred p) : K.CanonicalSpin pc (pc + 2) :=
  ⟨spinExit?_of_selfLoop h0 h1 hbase hpar htg, p, pollDst_of_code h0 hbase hpar, hpred⟩

/-- A position that holds no poll writes no predicate. -/
theorem pollDst_eq_none_of_notWait {pc : Nat}
    (h : ∀ ins, K.code[pc]? = some ins →
      ∀ p b o par a s, ins.op ≠ .mbarWait p b o par a s) :
    K.pollDst pc = none := by
  unfold Kernel.pollDst
  cases hc : K.code[pc]? with
  | none => rfl
  | some ins =>
    obtain ⟨gd, op⟩ := ins
    cases gd with
    | some g => rfl
    | none =>
      cases op with
      | mbarWait p b o par a s => exact False.elim (absurd rfl (h _ hc p b o par a s))
      | _ => rfl

/-- **A position that holds no poll heads no canonical spin**: it has no spin shape. -/
theorem spinExit?_eq_none_of_notWait {pc : Nat}
    (h : ∀ ins, K.code[pc]? = some ins →
      ∀ p b o par a s, ins.op ≠ .mbarWait p b o par a s) :
    K.spinExit? pc = none := by
  unfold Kernel.spinExit?
  rw [pollDst_eq_none_of_notWait h]

/-- **Every poll of a kernel whose polls all head this self loop is a canonical spin.** The
hypothesis is the shape of each poll of the kernel, its target and the reading of its predicate,
all decided on the code. -/
theorem canonicalSpin_of_selfLoops
    (h : ∀ pc ins, K.code[pc]? = some ins → ∀ p base off par acq sc,
      ins.op = .mbarWait p base off par acq sc →
      ins.guard = none ∧ (∃ uni, K.code[pc + 1]? =
        some { guard := some (p, true), op := .bra pc uni }) ∧
      base ≠ p ∧ par ≠ .reg p ∧ K.targeted (pc + 1) = false ∧ K.SpinPred p)
    {pc : Nat} {ins : Instr} {p base : Nat} {off : Int} {par : Opnd} {acq : Bool}
    {sc : MbarScope} (hc : K.code[pc]? = some ins)
    (ho : ins.op = .mbarWait p base off par acq sc) :
    ∃ exit, K.CanonicalSpin pc exit := by
  obtain ⟨gd, op⟩ := ins
  obtain ⟨hgd, ⟨uni, h1⟩, hbase, hpar, htg, hpred⟩ := h pc ⟨gd, op⟩ hc p base off par acq sc ho
  simp only at hgd ho
  subst hgd ho
  exact ⟨pc + 2, canonicalSpin_of_selfLoop hc h1 hbase hpar htg hpred⟩

end Kernel

end
end PTX
