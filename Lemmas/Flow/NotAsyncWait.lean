-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # `cp.async` group waits come from `cp.async.wait_group` instructions

A proof tool. Only a `cp.async.wait_group` or `cp.async.wait_all` instruction fires a `cp.async`
group wait (`fires_asyncWait_op`); a kernel without such instructions makes no such wait. -/

namespace PTX.Flow

/-- A template that fires no `cp.async` group wait. -/
def NotAsyncWait : Tmpl → Prop
  | .asyncWait .. => False
  | _ => True

theorem widen_notAsyncWait {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotAsyncWait m) :
    NotAsyncWait (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notAsyncWait {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotAsyncWait r) :
    NotAsyncWait (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a `cp.async` group wait. -/
def asyncWaitOp : Op → Bool
  | .cpAsyncWait .. => true
  | _ => false

/-- The event of a local rule of an integer, move or conversion instruction fires no such
event. -/
theorem localSregTmpl_notAsyncWait {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotAsyncWait (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotAsyncWait]

/-- The template of an instruction's rule, or its `noRule` fault, fires no such event. -/
theorem ruleTmpl_notAsyncWait {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotAsyncWait (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notAsyncWait
  · simp only [NotAsyncWait]

/-- An `if` of two templates that fire no such event fires none. -/
theorem ite_notAsyncWait {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotAsyncWait a)
    (hb : NotAsyncWait b) :
    NotAsyncWait (if c then a else b) := by
  split <;> assumption

/-- An instruction other than a `cp.async` group wait fires no such wait. -/
theorem eventTmpl_notAsyncWait {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : asyncWaitOp op = false) : NotAsyncWait (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notAsyncWait (op := .int i)
  case move m => exact ruleTmpl_notAsyncWait (op := .move m)
  case cvt c => exact ruleTmpl_notAsyncWait (op := .cvt c)
  all_goals simp only [asyncWaitOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notAsyncWait
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notAsyncWait)
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
         | (apply ofExec_notAsyncWait)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notAsyncWait)
         | split)
    | trivial

/-- A `cp.async` group wait is fired by a group-wait instruction. -/
theorem fires_asyncWait_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {n : Nat} (hk : e.kind = .asyncWait n) : asyncWaitOp op = true := by
  cases hq : asyncWaitOp op
  · exfalso
    have hm := eventTmpl_notAsyncWait (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotAsyncWait] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

end PTX.Flow
