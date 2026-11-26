-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TensorIssue

@[expose] public section

/-! # The copy behind a tensor load's issue event

A proof tool. A unicast tensor load's issue event, from a firing that may stop the thread and
whatever its cache policy operand, carries the copy the load prepares (`tensorLoadCopy`); with
`tensorLoadCopy_ok`, its map, descriptor and completion barrier (`fires_cpTensor_copy`). A map
operand holding a 64-bit word addresses that word (`tensorMapAddress_bits`). -/

namespace PTX.Flow
open PTX

noncomputable section

theorem fires_cpTensor_copy {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {o : Option TState} {ca grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd}
    {cs : List Opnd} {lm : TensorMode} {pol : Option Opnd} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor ca grp dst off map cs mb moff none lm pol)) e o)
    {a : Nat} {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) :
    tensorLoadCopy L g t ca grp dst off map cs mb moff lm = .ok (a, s) := by
  have hf' : Fires pc (tensorTmpl L g t (.cpTensor ca grp dst off map cs mb moff none lm pol)) e
      o := hf
  simp only [tensorTmpl, ofExec, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hf'
  rcases hp : cachePolicyRead L g t pol with f | ⟨⟩ <;> rw [hp] at hf'
  · simp only [Fires] at hf'; rw [hf'.1] at hk; cases hk
  · rcases hc : tensorLoadCopy L g t ca grp dst off map cs mb moff lm with f | ⟨a', s'⟩ <;>
      rw [hc] at hf'
    · simp only [Fires] at hf'; rw [hf'.1] at hk; cases hk
    · dsimp only at hf'
      split_ifs at hf'
      · simp only [Fires] at hf'
        rw [hf'.1] at hk
        cases hk
        rfl
      · simp only [Fires] at hf'; rw [hf'.1] at hk; cases hk

/-- A map operand register holding a 64-bit word addresses that word. -/
theorem tensorMapAddress_bits {L : Launch} {g : Nat} {t : TState} {r : Nat} {x : BitVec 64}
    (hr : t.regs r = some (.bits 64 x)) : tensorMapAddress L g t (.reg r) = .ok x.toNat := by
  simp [tensorMapAddress, readValue, readBits, readReg, hr, truncBits, bind, Except.bind, pure,
    Except.pure]
  exact x.isLt

end
end PTX.Flow
