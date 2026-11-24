-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrameSource
public import Lemmas.Execution.EventFrame
public import Lemmas.Flow.Hooks

@[expose] public section

/-! # Events that are not polls

A proof tool. Only `mbarrier.try_wait` fires a poll event; protocol proofs counting a
thread's polls on an object use this to skip every other event. -/

namespace PTX.Flow
open PTX

noncomputable section

/-- A template that does not poll an mbarrier. -/
def NotWait : Tmpl → Prop
  | .wait .. => False
  | _ => True

theorem ofExec_notWait {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotWait r) :
    NotWait (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- A non-polling template fires no poll event. -/
theorem thenWaitLd_notWait {pc : Nat} {m : Tmpl} (h : NotWait m) :
    NotWait (m.thenWaitLd pc) :=
  thenWaitLd_of (P := NotWait) (fun _ _ _ _ _ h => h) m pc h

theorem fires_notWait {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hm : NotWait m)
    (hf : Fires pc m e o) : ∀ l p ok acq sc, e.kind ≠ .wait l p ok acq sc := by
  intro l p ok acq sc he
  cases m <;> simp only [NotWait] at hm <;> simp only [Fires] at hf <;> aesop

/-- Whether an instruction is an mbarrier poll. -/
def waitOp : Op → Bool
  | .mbarWait .. => true
  | _ => false

theorem waitOp_ne {op : Op} (h : waitOp op = false) :
    ∀ p b off par a s, op ≠ .mbarWait p b off par a s := by
  intro p b off par a s hop
  subst hop
  simp [waitOp] at h

theorem widen_notWait {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotWait m) :
    NotWait (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals try exact h
    case arrive m tx t count release scope => cases release <;> cases scope <;> exact h
    case wait => exact h.elim
  · exact h

/-- The event of a local rule of an integer, move or conversion instruction does not poll. -/
theorem localSregTmpl_notWait {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotWait (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotWait]

/-- The template of an instruction's rule, or its `noRule` fault, does not poll. -/
theorem ruleTmpl_notWait {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    NotWait (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notWait
  · simp only [NotWait]

/-- An `if` of two non-polling templates does not poll. -/
theorem ite_notWait {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotWait a) (hb : NotWait b) :
    NotWait (if c then a else b) := by
  split <;> assumption

/-- A template that is a `ub` fault on a failed execution and `ok` on a successful one does not
poll when both are non-polling. -/
theorem exec_notWait {α : Type} {r : Exec α} {ub : Fault → Tmpl} {ok : α → Tmpl}
    (hub : ∀ f, NotWait (ub f)) (hok : ∀ a, NotWait (ok a)) :
    NotWait (match r with | .error f => ub f | .ok a => ok a) := by
  cases r with
  | error f => exact hub f
  | ok a => exact hok a

/-- Every instruction other than `mbarrier.try_wait` fires no poll event. -/
theorem eventTmpl_notWait {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : ∀ p b o par a s, op ≠ .mbarWait p b o par a s) : NotWait (eventTmpl A L g t op) := by
  cases op
  case mbarWait => exact absurd rfl (hop _ _ _ _ _ _)
  case int i => exact ruleTmpl_notWait (op := .int i)
  case move m => exact ruleTmpl_notWait (op := .move m)
  case cvt c => exact ruleTmpl_notWait (op := .cvt c)
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notWait
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notWait)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notWait)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notWait)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

end
end PTX.Flow
