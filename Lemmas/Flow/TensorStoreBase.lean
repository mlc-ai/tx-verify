-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc
public import Lemmas.Flow.NotObject

@[expose] public section

/-! # A tensor store reads its issuer's CTA

A proof tool. `cp.async.bulk.tensor` from shared to global memory takes its source through a
`.shared::cta` address (`sharedEffAddr` without cluster addressing), which is in the issuing
thread's own CTA (`sharedEffAddr_local`). So the source of every tensor store event is in its
issuer's CTA (`fires_tensorStore_base`), whatever the operands hold. -/

namespace PTX.Flow

/-- The source of a tensor store specification is in the thread's own CTA. -/
theorem tensorStoreSpec_base {L : Launch} {g : Nat} {t : TState} {map : Opnd} {cs : List Opnd}
    {src : Nat} {off : Int} {policy : Option Opnd} {mode : TensorMode}
    {reduce : Option AtomOp} {a : Nat} {s : TensorStore.Spec}
    (h : tensorStoreSpec L g t map cs src off policy mode reduce = .ok (a, s)) :
    s.sharedBase.cta = g / L.block := by
  unfold tensorStoreSpec at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (first | split at h | (cases h; done))
  all_goals (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h)
  all_goals exact (sharedEffAddr_local ‹sharedEffAddr L g t false src off = .ok _›).2

/-- **A tensor store's source is in its issuer's CTA.** -/
theorem fires_tensorStore_base {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Nat} {s : TensorStore.Spec} (hk : e.kind = .tensorStore a s) :
    s.sharedBase.cta = g / L.block := by
  have hop := fires_tensorStore_op hf hk
  cases op <;> simp only [tensorStoreOp, Bool.false_eq_true] at hop
  rename_i map cs src off policy mode reduce
  simp only [eventTmpl, tensorStoreTmpl, bind, Except.bind, pure, Except.pure] at hf
  cases h : tensorStoreSpec L g t map cs src off policy mode reduce with
  | error f =>
    simp only [h, ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok p =>
    obtain ⟨a', s'⟩ := p
    simp only [h, ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
    exact tensorStoreSpec_base h

end PTX.Flow
