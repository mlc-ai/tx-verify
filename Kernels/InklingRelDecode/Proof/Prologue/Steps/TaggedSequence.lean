-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
import Kernels.InklingRelDecode.Flow.Code.Part000

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

private theorem offset_ptr {sz gen sp off delta z}
    (he : offsetPointer 32 (.ptr sz gen sp off) delta = .ok z) :
    ∃ q, z = .ptr 32 gen sp q := by
  cases sp <;> simp only [offsetPointer,bind,Except.bind,pure,Except.pure] at he
  all_goals (split_ifs at he; cases he; exact ⟨_,rfl⟩)

private theorem ptr_sum {L g t u pw gen sp off}
    (hr : t.regs 482 = some (.ptr pw gen sp off))
    (he : execInt L g t ⟨.add,.int .s 32,false,[some 625],[.reg 482,.imm (-1023)]⟩ = .ok u) :
    ∃ q, u = PTX.next (setReg t 625 (.ptr 32 gen sp q)) := by
  have a : readValue L g t 32 (.reg 482) = .ok (.ptr pw gen sp off) := by
    simp [readValue,readReg,hr]; rfl
  have b : readValue L g t 32 (.imm (-1023)) = .ok (.bits 32 (i32 (-1023))) := rfl
  have c : readBits L g t 32 (.imm (-1023)) = .ok (i32 (-1023)) := rfl
  obtain ⟨f,err⟩ := readBits_regBits_none (w := 32) (L := L) (g := g) hr rfl
  cases sp <;> simp only [execInt,DType.width,a,b,c,err,bind,Except.bind,pure,Except.pure] at he
  all_goals repeat' split at he
  all_goals first | contradiction |
    (rename_i h; obtain ⟨_,rfl⟩ := offset_ptr h; exact ⟨_,(Except.ok.inj he).symm⟩)

/-- A tagged sequence difference can pass the signed immediate add at 43.
The signed maximum at 44 requires bits and faults on the preserved pointer. -/
theorem tagged_sequence_dead {L g t pw gen sp off}
    (pc : t.pc = 43) (hf : t.fault = none) (hr : t.regs 482 = some (.ptr pw gen sp off)) :
    Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t := by
  let op : IntInstr := ⟨.add,.int .s 32,false,[some 625],[.reg 482,.imm (-1023)]⟩
  have ev := Lib.workerInt (ii := op) (L := L) (g := g) (by rfl) pc (by decide)
  cases run : execInt L g t op with
  | error f => exact dead_of_error (pc ▸ Flow.code_43) rfl hf (ev.trans run)
  | ok u =>
    have tau := tau_of_ok (K := kernel) (pc ▸ Flow.code_43) rfl hf (ev.trans run)
    obtain ⟨q,rfl⟩ := ptr_sum hr run
    apply dead_of_rtg (.single tau)
    let s := PTX.next (setReg t 625 (.ptr 32 gen sp q))
    have pc' : s.pc = 44 := congrArg (·+1) pc
    have rq : s.regs 625 = some (.ptr 32 gen sp q) := by simp [s, PTX.next, setReg]
    obtain ⟨f,err⟩ := readBits_regBits_none (w := 32) (L := L) (g := g) rq rfl
    apply dead_of_error (t := s) (f := f) (pc' ▸ Flow.code_44) rfl hf
    rw [Lib.workerInt (ii := ⟨.max false,.int .s 32,false,[some 626],[.reg 625,.imm 0]⟩)
      (by rfl) pc' (by decide)]
    simp only [execInt,DType.width,err,bind,Except.bind]

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
