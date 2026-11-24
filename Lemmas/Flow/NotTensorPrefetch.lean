-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Tensor prefetches come from prefetch instructions

A proof tool. Only a `cp.async.bulk.prefetch.tensor` instruction fires a tensor prefetch event
(`fires_tensorPrefetch_op`); a kernel without such instructions issues no prefetch. -/

namespace PTX.Flow

/-- A template that fires no tensor prefetch. -/
def NotTensorPrefetch : Tmpl → Prop
  | .tensorPrefetch .. => False
  | _ => True

theorem widen_notTensorPrefetch {A : List Assumption} {site : Nat} {m : Tmpl}
    (h : NotTensorPrefetch m) :
    NotTensorPrefetch (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notTensorPrefetch {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotTensorPrefetch r) :
    NotTensorPrefetch (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a tensor prefetch. -/
def tensorPrefetchOp : Op → Bool
  | .prefetchTensor .. => true
  | _ => false

/-- The event of a local rule of an integer, move or conversion instruction fires no such
event. -/
theorem localSregTmpl_notTensorPrefetch {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotTensorPrefetch (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotTensorPrefetch]

/-- The template of an instruction's rule, or its `noRule` fault, fires no such event. -/
theorem ruleTmpl_notTensorPrefetch {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotTensorPrefetch (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notTensorPrefetch
  · simp only [NotTensorPrefetch]

/-- An `if` of two templates that fire no such event fires none. -/
theorem ite_notTensorPrefetch {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotTensorPrefetch a)
    (hb : NotTensorPrefetch b) : NotTensorPrefetch (if c then a else b) := by
  split <;> assumption

/-- An instruction other than a tensor prefetch fires no prefetch. -/
theorem eventTmpl_notTensorPrefetch {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} (hop : tensorPrefetchOp op = false) : NotTensorPrefetch (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notTensorPrefetch (op := .int i)
  case move m => exact ruleTmpl_notTensorPrefetch (op := .move m)
  case cvt c => exact ruleTmpl_notTensorPrefetch (op := .cvt c)
  all_goals simp only [tensorPrefetchOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notTensorPrefetch
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notTensorPrefetch)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, tensorStoreTmpl,
        reduxTmpl, matchTmpl, activemaskTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, tensorTmpl, tensorMulticast]
       repeat' first
         | trivial
         | (apply ofExec_notTensorPrefetch)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notTensorPrefetch)
         | split)
    | trivial

/-- A tensor prefetch is fired by a prefetch instruction. -/
theorem fires_tensorPrefetch_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Nat} {s : TensorPrefetch.Spec} (hk : e.kind = .tensorPrefetch a s) :
    tensorPrefetchOp op = true := by
  cases hq : tensorPrefetchOp op
  · exfalso
    have hm := eventTmpl_notTensorPrefetch (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotTensorPrefetch] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

end PTX.Flow
