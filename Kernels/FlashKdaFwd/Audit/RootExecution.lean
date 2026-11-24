-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Proof.RootContract
import Kernels.FlashKdaFwd.Audit.PackedNormalize
import Lemmas.Flow.FloatOutcome

/-! A kernel-scoped family of TxVerify local rules for register-to-register
rsqrt.approx.ftz.f32 on positive normal operands. Every allowed word is realizable.
Core handles the special cases and every other instruction. -/
namespace FlashKda.RootExecution
open PTX RootContract
noncomputable section

abbrev Proposal := Launch → Nat → TState → ℚ → Nat

def select (x : ℚ) (hx : normal x) (proposal : Nat) : {w // allowed x w} := by
  classical
  exact if h : allowed x proposal then ⟨proposal,h⟩ else
    ⟨(exists_allowed x hx).choose,(exists_allowed x hx).choose_spec⟩

theorem select_valid {x : ℚ} (hx : normal x) {w : Nat} (good : allowed x w) :
    (select x hx w).val = w := by simp [select,good]

def bits32 (w : Nat) : Value := .bits 32 (BitVec.ofNat 64 w)
def source (t : TState) (r : Nat) : Option FVal :=
  (t.regs r).bind fun v => (classify .f32 v).toOption

def onOperand (pick : Proposal) (L : Launch) (g : Nat) (t : TState) (dst : Nat) :
    Option FVal → Option (Exec TState)
  | some (.fin x) => if hx : format.minNormal ≤ x ∧ x ≤ format.maxNorm then
      some (.ok (next (setReg t dst (bits32 (select x hx (pick L g t x)).val)))) else none
  | _ => none

def rule (pick : Proposal) (L : Launch) (g : Nat) (t : TState) : Op → Option (Exec TState)
  | .float f => match f.srcs, f.dsts with
    | [.reg src], [some dst] =>
      if f = Normalize.rootAt src dst then onOperand pick L g t dst (source t src) else none
    | _, _ => none
  | _ => none

def assumption (pick : Proposal) : Assumption where
  name := "FlashKDA normal binary32 reciprocal square root"
  statement := "For rsqrt.approx.ftz.f32 with a positive normal register operand, the result is a
    positive normal binary32 word satisfying the PTX 9.2 relative error bound of 2^(-22.9)."
  localRule := rule pick

theorem execute (pick : Proposal) (L : Launch) (g : Nat) (t : TState) (src dst : Nat) {x : ℚ}
    (read : source t src = some (.fin x)) (hx : normal x) :
    execLocalA [assumption pick] L g t (.float (Normalize.rootAt src dst)) =
      .ok (next (setReg t dst (bits32 (select x hx (pick L g t x)).val))) := by
  simp [execLocalA,execLocalRule,assumption,rule,Normalize.rootAt,read,onOperand,normal] at hx ⊢
  simp [hx.1,hx.2]

theorem falls_through (pick : Proposal) (L : Launch) (g : Nat) (t : TState) (op : Op)
    (no : rule pick L g t op = none) :
    execLocalA [assumption pick] L g t op = execLocal L g t op := by
  simp [execLocalA,execLocalRule,assumption,no]

theorem other_form (pick : Proposal) (L : Launch) (g : Nat) (t : TState) (f : FloatInstr)
    (other : ∀ s d, f ≠ Normalize.rootAt s d) : rule pick L g t (.float f) = none := by
  unfold rule
  split <;> simp_all
  split <;> rfl

theorem special (pick : Proposal) (L : Launch) (g : Nat) (t : TState) (src dst : Nat)
    (outside : ∀ x, source t src = some (.fin x) → ¬normal x) :
    execLocalA [assumption pick] L g t (.float (Normalize.rootAt src dst)) =
      execLocal L g t (.float (Normalize.rootAt src dst)) := by
  apply falls_through
  cases h : source t src with
  | none => simp [rule,Normalize.rootAt,h,onOperand]
  | some a =>
    cases a with
    | fin x =>
      have hbad := outside x h
      simp [rule,Normalize.rootAt,h,onOperand,normal] at hbad ⊢
      exact hbad
    | _ => simp [rule,Normalize.rootAt,h,onOperand]

/-- The union over all local choices contains precisely the prescribed successor states. -/
theorem outcomes (L : Launch) (g : Nat) (t after : TState) (src dst : Nat) {x : ℚ}
    (read : source t src = some (.fin x)) (hx : normal x) :
    (∃ pick, execLocalA [assumption pick] L g t (.float (Normalize.rootAt src dst)) = .ok after) ↔
    ∃ w, allowed x w ∧ after = next (setReg t dst (bits32 w)) := by
  constructor
  · rintro ⟨pick,run⟩
    rw [execute pick L g t src dst read hx] at run
    exact ⟨_, (select x hx (pick L g t x)).property, (Except.ok.inj run).symm⟩
  · rintro ⟨w,ok,rfl⟩
    refine ⟨fun _ _ _ _ => w, ?_⟩
    rw [execute _ _ _ _ _ _ read hx, select_valid hx ok]

theorem source_word {t : TState} {r w : Nat} {x : ℚ} (reg : t.regs r = some (bits32 w))
    (width : w < 2^32) (decode : format.decode w = some (.fin x)) :
    source t r = some (.fin x) := by
  have cls := classify_bits (fmt := .f32) (n := w) (by omega) decode
  simp only [source,reg,Option.bind_some]
  change (classify .f32 (.bits (8*FloatFmt.f32.bytes) (BitVec.ofNat 64 w))).toOption = _
  rw [cls]
  rfl

end
end FlashKda.RootExecution
