-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Prologue
public import Lemmas.Flow.RegionFrame

@[expose] public section
namespace FlashKda.Packed
open PTX PTX.Proof

private theorem write_frame {op : Op} {t : TState} {d : Nat} {v : Value}
    (pc : nextPc op t.pc = t.pc+1) (dst : d ∈ writesRegs op) :
    LocalFrame op t (next (setReg t d v)) := by
  refine ⟨.inl pc.symm,rfl,rfl,rfl,?_⟩
  intro r keep
  exact Function.update_of_ne (by intro eq; subst r; exact keep dst) _ _

private theorem pointer_frame (base : Nat → Nat → Nat) (t u : TState) (op : Op)
    (h : Pointer.rule base t op = some (.ok u)) : LocalFrame op t u := by
  unfold Pointer.rule at h
  split at h <;> try simp only [bind,Option.bind,pure] at h
  all_goals repeat' first
    | (split at h <;> try dsimp only at h)
    | (solve | cases h)
    | (cases h; exact write_frame rfl (by simp [writesRegs]))

private theorem narrow_frame (t u : TState) (op : Op)
    (h : Bfloat.exactNarrow.localRule L g t op = some (.ok u)) : LocalFrame op t u := by
  simp only [Bfloat.exactNarrow] at h
  split at h <;> try contradiction
  repeat' first
    | (split at h <;> try dsimp only at h)
    | (solve | cases h)
    | (unfold Assumption.bindRead at h)
    | (cases h; exact write_frame rfl (by simp [writesRegs]))

theorem rules_frame (base : Nat → Nat → Nat) : RulesFrame (Prologue.assumptions base) := by
  intro a ha L g t op u h
  simp only [Prologue.assumptions,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact pointer_frame base t u op h
  · exact narrow_frame t u op h
  · exact idealReal_frame h
  · exact approxExact_frame h

theorem no_segments (base : Nat → Nat → Nat) (pc : Nat) :
    Assumption.SegFreePc (Prologue.assumptions base) pc := by
  intro a ha L g t _
  simp only [Prologue.assumptions,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> rfl

end FlashKda.Packed
