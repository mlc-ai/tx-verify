-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.GenRulesC
public import Lemmas.Flow.CvtBf

@[expose] public section

/-! # The exponent window's and the probability pack's readings for generated runs

The lemmas `Tools/out_gen.py` names in `Gen/Out/softmax_exp.json` and `softmax_pk.json`, at the
pcs of the exponent window outside the software `exp2` instances (1847 to 1912 and 2089 to 2233)
and of the probability pack (949 to 1008 but the barrier at 999). The scalar and packed
arithmetic is read exactly (`idealArith`), `ex2.approx` by `approx`, and the pack to `bf16` by
`bf16Exact` (`cvtBfE`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Lib

noncomputable section
variable {L : Launch} {g : Nat}

/-- A pc of the exponent window's runs or of the probability pack's. -/
def exPc (pc : Nat) : Bool :=
  decide ((949 ≤ pc ∧ pc < 1009 ∧ pc ≠ 999) ∨ (1847 ≤ pc ∧ pc < 1913) ∨ (2089 ≤ pc ∧ pc < 2234))

theorem ex_emu {pc : Nat} (h : exPc pc = true) : Assumptions.emuSites.contains pc = false := by
  simp only [exPc, decide_eq_true_eq] at h
  rw [Bool.eq_false_iff]
  intro h'
  simp only [Assumptions.emuSites, List.contains_iff_mem, List.mem_map, List.mem_range] at h'
  obtain ⟨i, hi, he⟩ := h'
  omega

theorem exSegFree {pc : Nat} (h : exPc pc = true) : SegFreePc Assumptions.all pc :=
  Kernels.InklingRelDecode.Proof.segFree (ex_emu h)

theorem ex_ne {pc : Nat} (h : exPc pc = true) : pc ≠ 600 ∧ pc ≠ 807 ∧ pc ≠ 2562 := by
  simp only [exPc, decide_eq_true_eq] at h
  omega

/-- No assumption reads a move or a selection of a run. -/
theorem rule_moveE {it : OItem} (pc : Nat) (hp : exPc pc = true)
    (hk : (match it with
      | .mov .. | .movImm .. | .pack .. | .unpack .. | .selp .. => true
      | _ => false) = true := by exact rfl) :
    ∀ t : TState, t.pc = pc → (XItem.base it).Rule Assumptions.all L g t := by
  intro t ht
  cases it <;> simp at hk <;> exact noRuleAt pc (ex_ne hp) rfl t ht

/-- The product or the sum of two numbers is read as exact. -/
theorem rule_arithE {it : OItem} (pc : Nat) (hp : exPc pc = true)
    (hk : (match it with | .mul .. | .add .. => true | _ => false) = true := by exact rfl) :
    ∀ t : TState, t.pc = pc → (XItem.base it).Rule Assumptions.all L g t := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := ex_ne hp
  cases it <;> simp at hk
  · exact forms_at (f := .mul .f32) (by simp [idealForms]) (ex_emu hp) h3 h1 h2 t ht
  · exact forms_at (f := .add .f32) (by simp [idealForms]) (ex_emu hp) h3 h1 h2 t ht

/-- The fused multiply-add of three scalars is read as exact. -/
theorem rule_fmaE {rnd : FloatRound} {fz : Bool} {d : Nat} {a b c : Opnd} (pc : Nat)
    (hp : exPc pc = true) (hq : [a, b, c].all fPlain = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp (fmaI rnd fz) d [a, b, c]) d (regsOf [a, b, c])
      (fF (floatE (fmaI rnd fz)) [a, b, c])).Rule Assumptions.all L g t := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := ex_ne hp
  have h := forms_at (L := L) (g := g) (f := .fma .f32) (by simp [idealForms]) (ex_emu hp)
    h3 h1 h2 t ht
  exact XItem.fma_rule h.1 h.2 hq

/-- The sum of two pairs of numbers is read as exact. -/
theorem rule_add2E {d a b : Nat} (pc : Nat) (hp : exPc pc = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp add2NI d [.reg a, .reg b]) d (regsOf [.reg a, .reg b])
      (fF add2NL [.reg a, .reg b])).Rule Assumptions.all L g t := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := ex_ne hp
  have h := forms_at (L := L) (g := g) (f := .addRnF32x2) (by simp [idealForms]) (ex_emu hp)
    h3 h1 h2 t ht
  exact XItem.add2N_rule h.1 h.2

/-- `ex2.approx.ftz.f32` is read as the exact power of two. -/
theorem rule_ex2E {fz : Bool} {d a : Nat} (pc : Nat) (hp : exPc pc = true) :
    ∀ t : TState, t.pc = pc → (XItem.base (.ex2 fz d a)).Rule Assumptions.all L g t := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := ex_ne hp
  exact ex2_at (L := L) (g := g) (t := t) (by rw [ht]; exact ex_emu hp) (by omega) (by omega)
    (by omega)

/-- `cvt.rn.bf16x2.f32` on the list of its two operands' values. -/
def cvtBfL : List Value → Exec Value
  | [va, vb] => cvtBfE va vb
  | _ => .error .noRule

/-- `cvt.rn.bf16x2.f32 d, a, b`. -/
def cvtBfOp (d : Nat) (s : List Nat) : Op := .cvt (cvtBfInstr d (s.getD 0 0) (s.getD 1 0))

/-- The pack of two numbers to `bf16` is read as exact (`bf16Exact`). -/
theorem rule_bfE {d a b : Nat} (pc : Nat) (hp : exPc pc = true) :
    ∀ t : TState, t.pc = pc →
      (XItem.fn (cvtBfOp d [a, b]) d [a, b] cvtBfL).Rule Assumptions.all L g t := by
  intro t ht W hW
  have ha := hW a (by simp)
  have hb := hW b (by simp)
  obtain ⟨h1, h2, h3⟩ := ex_ne hp
  have hr := (exSegFree hp).exec (L := L) (g := g) (op := cvtBfOp d [a, b]) ht
  have hl : ∀ a' ∈ Assumptions.all.take 6 ++ Assumptions.all.drop 7,
      a'.localRule L g t (cvtBfOp d [a, b]) = none := by
    intro a' ha'
    simp only [Assumptions.all, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ha'
    rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact idealReal_localRule_none fun f hf => by
        simp [cvtBfOp, FloatForm.ofOp, CvtInstr.widenF16?, CvtInstr.packF16?] at hf
    · exact approxExact_localRule_none fun f hf => by simp [cvtBfOp, ApproxForm.ofOp] at hf
    all_goals first
      | rfl
      | (simp only [Assumptions.lg2Exact, Assumptions.divFullExact, Assumptions.negExact]
         split <;> rfl)
  have hall : Assumptions.all.findSome? (fun a' => a'.localRule L g t (cvtBfOp d [a, b])) =
      Assumptions.bf16Exact.localRule L g t (cvtBfOp d [a, b]) := by
    have e : Assumptions.all = Assumptions.all.take 6 ++ Assumptions.bf16Exact ::
        Assumptions.all.drop 7 := rfl
    rw [e, List.findSome?_append,
      (List.findSome?_eq_none_iff.mpr fun a' h => hl a' (List.mem_append_left _ h)),
      List.findSome?_cons]
    cases hb' : Assumptions.bf16Exact.localRule L g t (cvtBfOp d [a, b]) with
    | some _ => rfl
    | none =>
      simp only [Option.none_or]
      exact List.findSome?_eq_none_iff.mpr fun a' h => hl a' (List.mem_append_right _ h)
  have hc := execLocal_cvtBf (L := L) (g := g) (d := d) ha hb
  have hra : readERealOpnd t .f32 (.reg a) = readEReal .f32 (W a) := by
    simp [readERealOpnd, readReg, ha, pure, Except.pure]
  have hrb : readERealOpnd t .f32 (.reg b) = readEReal .f32 (W b) := by
    simp [readERealOpnd, readReg, hb, pure, Except.pure]
  have hb16 : Assumptions.bf16Exact.localRule L g t (cvtBfOp d [a, b]) =
      bindRead (readEReal .f32 (W a)) fun x => bindRead (readEReal .f32 (W b)) fun y =>
        some (pure (next (setReg t d (.pair (erealValue .bf16 y) (erealValue .bf16 x))))) := by
    simp only [Assumptions.bf16Exact, cvtBfOp, cvtBfInstr, List.getD_cons_zero,
      List.getD_cons_succ, hra, hrb]
    rfl
  rw [hr, execLocalRule, hall, hb16]
  simp only [cvtBfL, List.map_cons, List.map_nil, cvtBfE]
  rcases hx : readEReal .f32 (W a) with _ | _ | x
  · simpa [bindRead, cvtBfOp, hx] using hc
  · simp [bindRead]; rfl
  · rcases hy : readEReal .f32 (W b) with _ | _ | y
    · simpa [bindRead, cvtBfOp, hx, hy] using hc
    · simp [bindRead]; rfl
    · simp [bindRead, Except.map, pure, Except.pure]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax
