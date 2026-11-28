-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.Next

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

/-- The own operand a shuffle with immediate lane offset `n` records is the register it names; a
shuffle that fires has read it. -/
theorem shfl_operand {L : Launch} {g : Nat} {t : TState} {o : Option TState} {e : Event}
    {mode mode0 : ShflMode} {a w : Value} {b c src dst bv : Nat} {m} {n : Int} {pc : Nat}
    {ok : Bool}
    (one : readBits L g t 32 (.imm n) = .ok m) (tn : m.toNat = bv)
    (hf : Fires pc (shflTmpl L g t mode0 dst none (.reg src) (.imm n) (.imm 31) (.imm (-1))) e o)
    (kind : e.kind = .shfl mode a b c w ok) :
    t.regs src = some a ∧ mode = mode0 ∧ b = bv ∧ c = 31 := by
  have mask : readBits L g t 32 (.imm (-1)) = .ok 4294967295 := rfl
  have clamp : readBits L g t 32 (.imm 31) = .ok 31 := rfl
  have bad {f} (h : e.kind = .ub f) : False := by rw [kind] at h; cases h
  cases ha : t.regs src with
  | none =>
    have h : readValue L g t 32 (.reg src) = .error .uninitialized := by
      simp [readValue,readReg,ha]; rfl
    simp only [shflTmpl,mask,one,clamp,h] at hf
    exact (bad (congrArg Event.kind hf.1)).elim
  | some x =>
    have h : readValue L g t 32 (.reg src) = .ok x := by simp [readValue,readReg,ha]; rfl
    simp only [shflTmpl,mask,one,clamp,h] at hf
    split_ifs at hf <;> try exact (bad (congrArg Event.kind hf.1)).elim
    obtain ⟨_,_,eq,_⟩ := hf
    rw [eq] at kind
    cases kind
    exact ⟨rfl,rfl,tn,rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
