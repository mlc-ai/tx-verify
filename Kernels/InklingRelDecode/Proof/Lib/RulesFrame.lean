-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Register.RegisterFrame

public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof PTX.Assumption

variable {L : Launch} {g : Nat}

/-- A step that writes one destination of the instruction and continues at the next position
keeps the frame. -/
private theorem frame_next_setReg {op : Op} {t : TState} {d : Nat} {v : Value}
    (hpc : nextPc op t.pc = t.pc + 1) (hd : d ∈ writesRegs op) :
    LocalFrame op t (next (setReg t d v)) :=
  ⟨.inl hpc.symm, rfl, rfl, rfl, fun r hr =>
    Function.update_of_ne (fun e => hr (by subst e; exact hd)) _ _⟩

/-- Closes the frame of a kernel-local reading: one destination of a floating instruction or a
conversion, continuing at the next position. -/
local macro "rule_frame" : tactic => `(tactic| (
  repeat' (first | split_ifs at * | split at * | (simp only [bindRead] at *))
  all_goals first
    | (cases ‹_ = _›; done)
    | (simp only [Option.some.injEq, Except.ok.injEq, pure, Except.pure] at *
       subst_vars
       exact frame_next_setReg rfl (by simp_all [writesRegs]))
    | (simp_all; done)))

private theorem lg2_frame {t t' : TState} {op : Op}
    (h : Assumptions.lg2Exact.localRule L g t op = some (.ok t')) : LocalFrame op t t' := by
  simp only [Assumptions.lg2Exact] at h
  rule_frame

private theorem divFull_frame {t t' : TState} {op : Op}
    (h : Assumptions.divFullExact.localRule L g t op = some (.ok t')) : LocalFrame op t t' := by
  simp only [Assumptions.divFullExact] at h
  rule_frame

private theorem neg_frame {t t' : TState} {op : Op}
    (h : Assumptions.negExact.localRule L g t op = some (.ok t')) : LocalFrame op t t' := by
  simp only [Assumptions.negExact] at h
  rule_frame

private theorem bf16_frame {t t' : TState} {op : Op}
    (h : Assumptions.bf16Exact.localRule L g t op = some (.ok t')) : LocalFrame op t t' := by
  simp only [Assumptions.bf16Exact] at h
  rule_frame

/-- **Every local rule of the kernel's assumptions writes only its instruction's registers.** -/
theorem rulesFrame : RulesFrame Assumptions.all := by
  intro a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · intro _ _ _ _ _ h; cases h
  · exact fun _ _ _ _ _ => idealReal_frame
  · exact fun _ _ _ _ _ => approxExact_frame
  · intro _ _ _ _ _ h; cases h
  · exact fun _ _ _ _ _ => lg2_frame
  · exact fun _ _ _ _ _ => divFull_frame
  · exact fun _ _ _ _ _ => neg_frame
  · exact fun _ _ _ _ _ => bf16_frame
  all_goals intro _ _ _ _ _ h; cases h

end PTX.Kernels.InklingRelDecode.Proof.Lib
