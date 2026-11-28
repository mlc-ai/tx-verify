-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.SafeLd
import Lemmas.Flow.UbStop
import Lemmas.Flow.TmplOkMore
import Lemmas.Flow.TmplOkSync
import Lemmas.Flow.NoUbSites
import Lemmas.Flow.UbFree

@[expose] public section

/-! # The prologue's static sites are not undefined behaviour

The register request, the two proxy fences, the named barriers, the full-mask elections (the
vote at the head and the elections of the preload blocks) and the barrier before the softmax have
no register operand: their events do not depend on any state (`static_tmpl`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow Control

variable {L : Launch} {g : Nat} {t : TState}

/-- The warp collectives with immediate operands only: the full-mask election. -/
def staticWarp : WarpInstr → Bool
  | ⟨.elect, _, [_, some _], [], some (.imm (-1))⟩ => true
  | _ => false

/-- The instructions whose event does not depend on any register. -/
def staticOk : Op → Bool
  | .barSync (.imm id) _ => decide (0 ≤ id ∧ id < 16)
  | .barSyncN (.imm id) (.imm n) _ => decide (0 ≤ id ∧ id < 16 ∧ 0 < n ∧ n < 2 ^ 31 ∧ n % 32 = 0)
  | .warp w => staticWarp w
  | op => plainOk op

/-- The instruction at `pc` is static. -/
def staticAt (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ins => staticOk ins.op
  | none => false

set_option linter.unnecessarySimpa false in
/-- **A static instruction's event template is not undefined behaviour.** -/
theorem static_tmpl {pc : Nat} {ins : Instr} (hb : L.block % 32 = 0) (h : staticAt pc = true)
    (hc : kernel.code[pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  simp only [staticAt, hc] at h
  obtain ⟨gd, op⟩ := ins
  simp only at h ⊢
  cases op
  case barSync a al =>
    cases a <;> try (exfalso; simp [staticOk, plainOk] at h; done)
    case imm id =>
      simp only [staticOk, decide_eq_true_eq] at h
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
      exact barSync_imm_ok (by omega) f
  case barSyncN a b al =>
    cases a <;> try (exfalso; simp [staticOk, plainOk] at h; done)
    cases b <;> try (exfalso; simp [staticOk, plainOk] at h; done)
    rename_i id n
    simp only [staticOk, decide_eq_true_eq] at h
    obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h.2.2.1.le
    exact (bar_ok (by omega) (by omega) (by omega) (by omega) f).1
  case warp w =>
    have hw : staticWarp w = true := by simpa [staticOk] using h
    unfold staticWarp at hw
    split at hw
    · exact elect_imm_ok f
    · simp at hw
  all_goals first
    | (simp [staticOk, plainOk] at h; done)
    | exact plainOk_tmpl hb (by simpa [staticOk, plainOk] using h) f

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
