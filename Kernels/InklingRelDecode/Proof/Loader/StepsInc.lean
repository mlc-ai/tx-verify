-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Inputs
public import Kernels.InklingRelDecode.Proof.Lib.RawArith
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32

noncomputable section

/-- A successful pointer increment still has pointer kind. The subsequent integer
comparison faults on it. -/
def incValue (v : Value) : Value :=
  match v with
  | .ptr _ gen space off => .ptr 32 gen space (BitVec.ofInt 64 ((off.toNat : Int) + 1))
  | _ => .bits 32 (r32 (bits v + 1))

theorem inc_bits {v : Value} {x : BitVec 64} (hx : (incValue v).regBits = some x) :
    incValue v = .bits 32 (r32 (bits v + 1)) := by
  cases v <;> first | rfl | cases hx

private theorem inc_result {L : Launch} {g : Nat} {t u : TState} {i : Value}
    (hi : t.regs 1905 = some i)
    (he : execInt L g t ⟨.add, .int .s 32, false, [some 1905], [.reg 1905, .imm 1]⟩ =
      .ok u) : u = PTX.next (setReg t 1905 (incValue i)) := by
  have himm : readValue L g t 32 (.imm 1) = .ok (.bits 32 1) := rfl
  have hval : readValue L g t 32 (.reg 1905) = .ok i := by
    simp [readValue, readReg, hi, pure, Except.pure]
  simp only [execInt, DType.width, hval, himm, bind, Except.bind] at he
  cases hx : readBits L g t 32 (.reg 1905) with
  | ok x =>
    have hb := Lib.readBits_eq_pattern hi hx
    cases i with
    | ptr =>
      obtain ⟨_, h⟩ := readBits_regBits_none (w := 32) (L := L) (g := g) hi rfl
      rw [hx] at h
      cases h
    | _ =>
      simp only [hx, pure, Except.pure] at he
      subst x
      exact (Except.ok.inj he).symm
  | error f =>
    cases i with
    | ptr pw gen sp off =>
      cases sp <;>
        simp [readBits, readReg, hi, offsetPointer, throw, throwThe, MonadExceptOf.throw, bind,
          Except.bind, pure, Except.pure]
          at he
      all_goals repeat' split at he
      all_goals first | contradiction |
        (rename_i hp; split_ifs at hp; cases hp; exact (Except.ok.inj he).symm)
    | _ =>
      simp only [hx] at he
      contradiction

/-- Local step after the last copy or the last lost election. -/
theorem inc_span {L : Launch} {g : Nat} {F G : List (Nat × Value)} {i : Value}
    (hi : (1905,i) ∈ F)
    (hw : ∀ R, Holds R F → Holds (Function.update R 1905 (some (incValue i))) G) :
    SegU kernel Assumptions.all L g 2413 F 2414 G :=
  Lib.scalarStepU Flow.code_2413 rfl rfl (by decide)
    (fun _ _ hR => inc_result (holds_mem hR hi)) hw

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
