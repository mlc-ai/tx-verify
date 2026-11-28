-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Values
import Lemmas.Flow.Scalars

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

private theorem offset_ok {pw gen sp off delta v}
    (he : offsetPointer 32 (.ptr pw gen sp off) delta = .ok v) :
    v = .ptr 32 gen sp (BitVec.ofInt 64 ((off.toNat : Int)+delta)) := by
  cases sp <;> simp only [offsetPointer,bind,Except.bind,pure,Except.pure] at he
  all_goals (split_ifs at he; cases he; rfl)

/-- A successful request difference may preserve the left pointer's tag.
The right operand always supplies a 32-bit pattern. -/
theorem sub_result {L g t u dst x y a b}
    (hx : t.regs x = some a) (hy : t.regs y = some b)
    (he : execInt L g t ⟨.sub,.int .s 32,false,[some dst],[.reg x,.reg y]⟩ = .ok u) :
    u = PTX.next (setReg t dst (subValue a b)) ∧ b.regBits.isSome := by
  have hv : readValue L g t 32 (.reg x) = .ok a := by simp [readValue,readReg,hx]; rfl
  cases bys : readBits L g t 32 (.reg y) with
  | error f =>
    cases a with
    | ptr pw gen sp off =>
      cases sp <;> simp only [execInt,DType.width,hv,bind,Except.bind,bys] at he
      all_goals repeat' split at he
      all_goals contradiction
    | _ =>
      all_goals simp only [execInt,DType.width,hv,bind,Except.bind,bys] at he
      all_goals split at he <;> contradiction
  | ok byv =>
    have eq := Lib.readBits_eq_pattern hy bys
    have bits : b.regBits.isSome := by
      cases h : b.regBits with
      | none =>
        obtain ⟨f,hf⟩ := readBits_regBits_none (w := 32) (L := L) (g := g) hy h
        rw [bys] at hf
        contradiction
      | some => rfl
    refine ⟨?_,bits⟩
    cases a with
    | ptr pw gen sp off =>
      obtain ⟨f,err⟩ := readBits_regBits_none (w := 32) (L := L) (g := g) hx rfl
      cases sp <;> simp only [execInt,DType.width,hv,bind,Except.bind,bys,eq,err,
        pure,Except.pure] at he
      all_goals repeat' split at he
      all_goals first | contradiction | (rename_i hptr; rw [offset_ok hptr] at he
                                         ; simpa only [subValue,Lib.word,sub_eq_add_neg] using
                                             (Except.ok.inj he).symm)
    | _ =>
      all_goals
        cases ax : readBits L g t 32 (.reg x) <;>
          simp only [execInt,DType.width,hv,bind,Except.bind,bys,eq,ax,pure,Except.pure] at he
        · contradiction
        · rw [Lib.readBits_eq_pattern hx ax] at he
          simpa only [subValue,sub32,r32,Lib.word,truncBits_idem] using (Except.ok.inj he).symm

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
