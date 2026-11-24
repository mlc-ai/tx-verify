-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotBulk

@[expose] public section

/-! # No bulk-group copy

A `cp.async` copy is of the asynchronous group, so a kernel with no `cp.async.bulk` and no
asynchronous store issues no copy of the bulk group (`no_bulkGroup`). -/

namespace PTX.Flow
open PTX PTX.Proof

/-- Whether an instruction is a `cp.async.bulk` or an asynchronous store. -/
def bulkGroupOp : Op → Bool
  | .cpBulk .. | .asyncStore .. => true
  | _ => false

/-- A template that fires no bulk-group copy. -/
def NotBulkGroup : Tmpl → Prop
  | .copy s _ => s.completion ≠ .bulkGroup
  | _ => True

theorem ofExec_notBulkGroup {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotBulkGroup r) :
    NotBulkGroup (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- A copy fired by an instruction that is no bulk copy is of no bulk group. -/
theorem fires_copy_group {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    (hop : bulkGroupOp op = false) {s : AsyncCopy.Spec} (hk : e.kind = .copy s) :
    s.completion ≠ .bulkGroup := by
  have hb := fires_bulk_op hf hk
  have hm : NotBulkGroup (eventTmpl A L g t op) := by
    cases op <;> simp only [bulkOp, bulkGroupOp, Bool.false_eq_true, reduceCtorEq] at hb hop
    simp only [eventTmpl, cpAsyncTmpl]
    repeat' first
      | trivial
      | (apply ofExec_notBulkGroup)
      | (apply PTX.EventFrame.allOk_bind; intro _)
      | (apply PTX.EventFrame.allOk_ite)
      | (intro h; cases h)
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [Fires] at hf <;>
    simp_all [NotBulkGroup]

/-- **A kernel with no `cp.async.bulk` and no asynchronous store issues no bulk-group copy.** -/
theorem no_bulkGroup {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X)
    (hcode : K.code.all (fun ins => !bulkGroupOp ins.op) = true) {i : EvId} {s : AsyncCopy.Spec}
    (hi : X.Copy i s) : s.completion ≠ .bulkGroup := by
  intro hb
  obtain ⟨pc, he⟩ := hi
  refine no_kind_of_code hX bulkGroupOp (fun k => ∃ s, k = .copy s ∧ s.completion = .bulkGroup)
    (fun _ ⟨_, h, _⟩ => by cases h) (fun {_ _ _ op _ _} hf ⟨s, hk, hs⟩ => ?_) hcode he ⟨s, rfl, hb⟩
  by_contra hop
  exact fires_copy_group hf (by simpa using hop) hk hs

end PTX.Flow
