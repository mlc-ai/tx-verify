-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TensorBox

@[expose] public section

/-! # A tensor load's issue, with or without a cache policy

A proof tool. A unicast tensor load that continues has fired one tensor issue and continues at
the next instruction, whatever its `.L2::cache_hint` operand (THREAD-TENSOR: the policy is
read and otherwise ignored); the copy completes on the mbarrier its operand resolves to. -/

namespace PTX.Flow
open PTX

noncomputable section

theorem fires_cpTensor_issue {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {ca grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd} {cs : List Opnd}
    {lm : TensorMode} {pol : Option Opnd} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor ca grp dst off map cs mb moff none lm pol)) e
      (some u)) :
    ∃ a s, e = ⟨pc, .tensorIssue a s⟩ ∧ u = next t ∧
      (if ca then mbarClusterLoc L g t mb moff else mbarLoc L g t mb moff) = .ok s.mbar := by
  have hf' : Fires pc (tensorTmpl L g t (.cpTensor ca grp dst off map cs mb moff none lm pol)) e
      (some u) := hf
  simp only [tensorTmpl, ofExec, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hf'
  rcases hp : cachePolicyRead L g t pol with f | ⟨⟩ <;> rw [hp] at hf'
  · simp [Fires] at hf'
  · rcases hc : tensorLoadCopy L g t ca grp dst off map cs mb moff lm with f | ⟨a, s⟩ <;>
      rw [hc] at hf'
    · simp [Fires] at hf'
    · dsimp only at hf'
      split_ifs at hf'
      · obtain ⟨he, hu⟩ := hf'
        exact ⟨a, s, he, Option.some.inj hu, (tensorLoadCopy_ok hc).2.1⟩
      · simp [Fires] at hf'

/-- The completion barrier of a unicast tensor load's issue event, from a firing that may stop
the thread. -/
theorem fires_cpTensor_issue_loc {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {o : Option TState} {ca grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd}
    {cs : List Opnd} {lm : TensorMode} {pol : Option Opnd} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor ca grp dst off map cs mb moff none lm pol)) e o)
    {a : Nat} {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) :
    (if ca then mbarClusterLoc L g t mb moff else mbarLoc L g t mb moff) = .ok s.mbar := by
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
        exact (tensorLoadCopy_ok hc).2.1
      · simp only [Fires] at hf'; rw [hf'.1] at hk; cases hk

end
end PTX.Flow
