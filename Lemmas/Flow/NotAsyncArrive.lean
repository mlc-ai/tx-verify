-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Arrive-ons come from `cp.async.mbarrier.arrive` instructions

A proof tool. Only a `cp.async.mbarrier.arrive` instruction fires an arrive-on event
(`fires_asyncArrive_op`); a kernel without such instructions issues no arrive-on. -/

namespace PTX.Flow

/-- A template that fires no arrive-on. -/
def NotAsyncArrive : Tmpl → Prop
  | .asyncArrive .. => False
  | _ => True

theorem widen_notAsyncArrive {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotAsyncArrive m) :
    NotAsyncArrive (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notAsyncArrive {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotAsyncArrive r) :
    NotAsyncArrive (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a `cp.async.mbarrier.arrive`. -/
def asyncArriveOp : Op → Bool
  | .cpAsyncArrive .. => true
  | _ => false

/-- The event of a local rule of an integer, move or conversion instruction fires no such
event. -/
theorem localSregTmpl_notAsyncArrive {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotAsyncArrive (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotAsyncArrive]

/-- The template of an instruction's rule, or its `noRule` fault, fires no such event. -/
theorem ruleTmpl_notAsyncArrive {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotAsyncArrive (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notAsyncArrive
  · simp only [NotAsyncArrive]

/-- An `if` of two templates that fire no such event fires none. -/
theorem ite_notAsyncArrive {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotAsyncArrive a)
    (hb : NotAsyncArrive b) :
    NotAsyncArrive (if c then a else b) := by
  split <;> assumption

/-- An instruction other than a `cp.async.mbarrier.arrive` fires no arrive-on. -/
theorem eventTmpl_notAsyncArrive {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : asyncArriveOp op = false) : NotAsyncArrive (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notAsyncArrive (op := .int i)
  case move m => exact ruleTmpl_notAsyncArrive (op := .move m)
  case cvt c => exact ruleTmpl_notAsyncArrive (op := .cvt c)
  all_goals simp only [asyncArriveOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notAsyncArrive
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notAsyncArrive)
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
         | (apply ofExec_notAsyncArrive)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notAsyncArrive)
         | split)
    | trivial

/-- An arrive-on is fired by a `cp.async.mbarrier.arrive` instruction. -/
theorem fires_asyncArrive_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {m : Loc} {noinc : Bool} (hk : e.kind = .asyncArrive m noinc) : asyncArriveOp op = true := by
  cases hq : asyncArriveOp op
  · exfalso
    have hm := eventTmpl_notAsyncArrive (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotAsyncArrive] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

end PTX.Flow
