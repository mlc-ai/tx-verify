-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotTensor

@[expose] public section

/-! # Instructions that fire no `tcgen05` event

A proof tool. Only the `tcgen05` instructions (`tcAnyOp`: allocation, deallocation,
relinquishment, MMA, commit, copy, load, store, shift, the waits and the fences) fire a `.tc`
event: every other instruction's template is not a Tensor Core template (`eventTmpl_notTc`), so
it fires no `.tc` event (`fires_notTc`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- A template that fires no `tcgen05` event. -/
def NotTc : Tmpl → Prop
  | .tc .. | .tcLd .. => False
  | _ => True

/-- The `tcgen05` instructions. -/
def tcAnyOp : Op → Bool
  | .tcCommit .. | .tcLd .. | .tcAlloc .. | .tcDealloc .. | .tcRelinquish .. | .tcMma ..
  | .tcFenceBefore | .tcFenceAfter | .tcWaitLd | .tcSt .. | .tcWaitSt
  | .tcCp .. | .tcShift .. => true
  | _ => false

theorem widen_notTc {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotTc m) :
    NotTc (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

/-- The event of a local rule of an integer, move or conversion instruction fires no `tcgen05`
event. -/
theorem localSregTmpl_notTc {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotTc (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotTc]

/-- The template of an instruction's rule, or its `noRule` fault, fires no `tcgen05` event. -/
theorem ruleTmpl_notTc {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    NotTc (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notTc
  · simp only [NotTc]

theorem ofExec_notTc {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotTc r) : NotTc (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- An instruction that is not a `tcgen05` instruction has no Tensor Core template. -/
theorem eventTmpl_notTc {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : tcAnyOp op = false) : NotTc (eventTmpl A L g t op) := by
  cases op <;> simp only [tcAnyOp, Bool.true_eq_false] at hop
  case mem a =>
    have hm := memTmpl_isMem (A := A) (L := L) (g := g) (t := t) (a := a)
    simp only [eventTmpl]
    generalize memTmpl A L g t a = m at hm ⊢
    cases m <;> trivial
  case warp w =>
    have hm := warpTmpl_isWarp (L := L) (g := g) (t := t) (w := w)
    simp only [eventTmpl]
    generalize warpTmpl L g t w = m at hm ⊢
    cases m <;> trivial
  case int i =>
    simp only [eventTmpl]
    exact ruleTmpl_notTc
  case move m =>
    simp only [eventTmpl]
    exact ruleTmpl_notTc
  case cvt c =>
    simp only [eventTmpl]
    exact ruleTmpl_notTc
  all_goals simp only [eventTmpl]
  all_goals first
    | (apply widen_notTc
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notTc)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | (simp only [barTmpl, SetMaxNReg.tmpl,
        tensorStoreTmpl, tensorTmpl,
        tensorPrefetchTmpl, clcTmpl, tensorMulticast,
        cpAsyncTmpl, asyncStoreTmpl, matrixTmpl, matrixMoveTmpl, fenceTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notTc)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split)
    | trivial

/-- **A non-`tcgen05` instruction fires no `tcgen05` event.** -/
theorem fires_notTc {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hop : tcAnyOp op = false)
    (hf : Fires pc (eventTmpl A L g t op) e o) : ∀ k, e.kind ≠ .tc k := by
  intro k he
  have hm := eventTmpl_notTc (A := A) (L := L) (g := g) (t := t) hop
  cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotTc] at hm <;>
    simp only [Fires] at hf <;> aesop

end
end PTX.Flow
