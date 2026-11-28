-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.GenRulesL
public import Lemmas.Flow.RcpCore
public import Lemmas.Flow.SetpCore
public import Kernels.InklingRelDecode.Proof.Lib.RcpApprox

@[expose] public section

/-! # The epilogue's zero pairs and reciprocal, for generated runs

The lemmas `Tools/out_gen.py` names in `Gen/Out/epilogue_zero.json`, at the pcs 2567 to 2602: the
pack and the moves of the zero pair, the comparison of the row sum with zero, the selection of its
operand and the reciprocal. No assumption reads a move; the comparison is read as exact; the
reciprocal at 2602 is read by `approx`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Lib

noncomputable section
variable {L : Launch} {g : Nat}

/-- A pc of the epilogue's zero pairs, comparison, selection and reciprocal. -/
def zPc (pc : Nat) : Bool := decide (2567 ≤ pc ∧ pc < 2603)

theorem z_emu {pc : Nat} (h : zPc pc = true) : Assumptions.emuSites.contains pc = false := by
  simp only [zPc, decide_eq_true_eq] at h
  rw [Bool.eq_false_iff]
  intro h'
  simp only [Assumptions.emuSites, List.contains_iff_mem, List.mem_map, List.mem_range] at h'
  obtain ⟨i, hi, he⟩ := h'
  omega

theorem zSegFree {pc : Nat} (h : zPc pc = true) : SegFreePc Assumptions.all pc :=
  Kernels.InklingRelDecode.Proof.segFree (z_emu h)

theorem z_ne {pc : Nat} (h : zPc pc = true) : pc ≠ 600 ∧ pc ≠ 807 ∧ pc ≠ 2562 := by
  simp only [zPc, decide_eq_true_eq] at h
  omega

/-- No assumption reads a move, a pack or a selection of the run. -/
theorem rule_moveZ {it : OItem} (pc : Nat) (hp : zPc pc = true)
    (hk : (match it with
      | .mov .. | .movImm .. | .pack .. | .unpack .. | .selp .. => true
      | _ => false) = true := by exact rfl) :
    ∀ t : TState, t.pc = pc → (XItem.base it).Rule Assumptions.all L g t := by
  intro t ht
  cases it <;> simp at hk <;> exact noRuleAt pc (z_ne hp) rfl t ht

/-- The comparison with zero is read as exact. -/
theorem rule_setpZ {it : OItem} (pc : Nat) (hp : zPc pc = true)
    (hk : (match it with | .setp _ _ _ _ 0 => true | _ => false) = true := by exact rfl) :
    ∀ t : TState, t.pc = pc → (XItem.base it).Rule Assumptions.all L g t := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := z_ne hp
  cases it <;> try simp at hk
  rename_i k
  cases k
  swap
  · simp at hk
  have e : setpForm 0 = .setp .f32 := by simp [setpForm, isInfConst]
  show IdealAt Assumptions.all (setpForm 0) L g t ∧ DeclineAt Assumptions.all (setpForm 0) L g t
  rw [e]
  exact forms_at (f := .setp .f32) (by simp [idealForms]) (z_emu hp) h3 h1 h2 t ht

/-- `mov.b64 d, a` on a list of one value. -/
def mov64L : List Value → Exec Value
  | [v] => if v.bytes = 8 then .ok v else .error .typeMismatch
  | _ => .error .noRule

/-- The scalar move of 64 bits. -/
def mov64Op (d : Nat) (o : Opnd) : Op := .move ⟨.scalar, .int .b 64, [some d], [o]⟩

/-- No assumption reads a move of 64 bits; it copies a value of eight bytes. -/
theorem rule_mov64Z {d a : Nat} (pc : Nat) (hp : zPc pc = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (mov64Op d (.reg a)) d (regsOf [.reg a]) (fF mov64L [.reg a])).Rule
      Assumptions.all L g t := by
  intro t ht W hW
  have ha : t.regs a = some (W a) := hW a (by simp [regsOf, regOf])
  have h0 := noRuleAt (L := L) (g := g) (op := .move ⟨.scalar, .int .b 64, [some d], [.reg a]⟩)
    pc (z_ne hp) rfl t ht
  rw [fF_map]
  simp only [(zSegFree hp).exec ht, execLocalRule_of_none h0, mov64Op, mov64L]
  by_cases h8 : (W a).bytes = 8 <;>
    simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, ha, h8,
      fOpnd, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Except.map]


/-- `rcp.approx.f32` on a list of one value. -/
def rcpL (fz : Bool) : List Value → Exec Value
  | [a] => rcpE fz a
  | _ => .error .noRule

/-- The reciprocal at pc 2602 is read as its exact function. -/
theorem rule_rcpZ {d a : Nat} (pc : Nat) (hp : pc = 2602) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp (rcpI true) d [.reg a]) d (regsOf [.reg a])
      (fF (rcpL true) [.reg a])).Rule Assumptions.all L g t := by
  intro t ht
  obtain ⟨hA, hD⟩ := approx_2602 (L := L) (g := g) (hp ▸ ht)
  exact XItem.float_rule (by simp [fPlain]) fun W hW =>
    exec_rcpE hA hD (hW (.reg a) (by simp))

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax
