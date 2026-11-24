-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotWait
public import Lemmas.Flow.Polls

@[expose] public section

/-! # Events that are not arrivals

A proof tool. Only `mbarrier.arrive` fires an arrival event; protocol proofs counting a
thread's arrivals on an object use this to skip every other event. -/

namespace PTX.Flow
open PTX

noncomputable section

/-- A template that does not arrive on an mbarrier. -/
def NotArrive : Tmpl → Prop
  | .arrive .. => False
  | _ => True

theorem ofExec_notArrive {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotArrive r) :
    NotArrive (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem widen_notArrive {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotArrive m) :
    NotArrive (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals first
      | exact h
      | (case arrive m' tx t count release scope => cases release <;> cases scope <;> exact h)
      | (case wait m' parity k acquire scope => cases acquire <;> cases scope <;> trivial)
  · exact h

/-- The event of a local rule of an integer, move or conversion instruction arrives nowhere. -/
theorem localSregTmpl_notArrive {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotArrive (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotArrive]

/-- The template of an instruction's rule, or its `noRule` fault, arrives nowhere. -/
theorem ruleTmpl_notArrive {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    NotArrive (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notArrive
  · simp only [NotArrive]

/-- An `if` of two templates that arrive nowhere arrives nowhere. -/
theorem ite_notArrive {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotArrive a)
    (hb : NotArrive b) : NotArrive (if c then a else b) := by
  split <;> assumption

/-- A template that is a `ub` fault on a failed execution and `ok` on a successful one arrives
    nowhere when both do not. -/
theorem exec_notArrive {α : Type} {r : Exec α} {ub : Fault → Tmpl} {ok : α → Tmpl}
    (hub : ∀ f, NotArrive (ub f)) (hok : ∀ a, NotArrive (ok a)) :
    NotArrive (match r with | .error f => ub f | .ok a => ok a) := by
  cases r with
  | error f => exact hub f
  | ok a => exact hok a

/-- Every instruction other than `mbarrier.arrive` fires no arrival event. -/
theorem eventTmpl_notArrive {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : ∀ (base : Nat) (off : Int) (tx count : Opnd) (cluster release : Bool)
      (scope : MbarScope) (state : Option Nat),
      op ≠ .mbarArrive base off tx count cluster release scope state) :
    NotArrive (eventTmpl A L g t op) := by
  cases op
  case mbarArrive base off tx count cluster release scope state =>
    exact absurd rfl (hop _ _ _ _ _ _ _ _)
  case int i => exact ruleTmpl_notArrive (op := .int i)
  case move m => exact ruleTmpl_notArrive (op := .move m)
  case cvt c => exact ruleTmpl_notArrive (op := .cvt c)
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notArrive
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notArrive)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        SetMaxNReg.tmpl, matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, tensorTmpl, tensorStoreTmpl,
        reduxTmpl, matchTmpl, activemaskTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notArrive)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notArrive)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A template that does not arrive fires no arrival event. -/
theorem fires_notArrive {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hm : NotArrive m)
    (hf : Fires pc m e o) : ∀ (l : Loc) (tx c : Nat) (rel : Bool) (sc : MbarScope),
      e.kind ≠ .arrive l tx c rel sc := by
  intro l tx c rel sc he
  cases m <;> simp only [NotArrive] at hm <;> simp only [Fires] at hf <;> aesop

/-- An event after which the thread stops (an exit or a fault) is not an arrival. -/
theorem fires_none_notArrive {pc : Nat} {m : Tmpl} {e : Event} (hf : Fires pc m e none) :
    ∀ (l : Loc) (tx c : Nat) (rel : Bool) (sc : MbarScope), e.kind ≠ .arrive l tx c rel sc := by
  intro l tx c rel sc he
  cases m <;> simp only [Fires] at hf <;> aesop

/-- Whether an instruction is an mbarrier arrival. -/
def arriveOp : Op → Bool
  | .mbarArrive .. => true
  | _ => false

theorem arriveOp_ne {op : Op} (h : arriveOp op = false) :
    ∀ (base : Nat) (off : Int) (tx count : Opnd) (cluster release : Bool)
      (scope : MbarScope) (state : Option Nat),
      op ≠ .mbarArrive base off tx count cluster release scope state := by
  intro base off tx count cluster release scope state hop
  subst hop
  simp [arriveOp] at h

/-- An instruction that is not an arrival fires no arrival event. -/
theorem arrivesOn_of_arriveOp {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} {pc : Nat} {e : Event} {o : Option TState} {m : Loc}
    (hop : arriveOp op = false) (hf : Fires pc (eventTmpl A L g t op) e o) :
    arrivesOn m e = false :=
  arrivesOn_notArrive (fires_notArrive (eventTmpl_notArrive (arriveOp_ne hop)) hf)

end
end PTX.Flow
