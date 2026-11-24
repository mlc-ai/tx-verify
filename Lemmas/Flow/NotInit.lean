-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotCommit
public import Lemmas.Isa.Tmpl

@[expose] public section

/-! # Barrier initializations

A proof tool. Only `mbarrier.init` fires an initialization event (`notInit_of_op`); a proof that
a site machine's states never initialize a barrier checks that no site of it is an
`mbarrier.init` (`initOp`). -/

namespace PTX.Flow
open PTX

noncomputable section

/-- A template that does not initialize an mbarrier. -/
def NotInit : Tmpl → Prop
  | .mbInit .. => False
  | _ => True

/-- Whether an instruction is an `mbarrier.init`. -/
def initOp : Op → Bool
  | .mbarInit .. => true
  | _ => false

theorem ofExec_notInit {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotInit r) :
    NotInit (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem widen_notInit {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotInit m) :
    NotInit (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals first
      | exact h
      | (case arrive m' tx t count release scope => cases release <;> cases scope <;> exact h)
      | (case wait m' parity k acquire scope => cases acquire <;> cases scope <;> exact h)
  · exact h

/-- The template of an instruction's local rule, or its `noRule` fault, does not initialize. -/
theorem ruleTmpl_notInit {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    NotInit (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · rename_i r _
    cases r <;> simp only [localSregTmpl, sregTmpl, NotInit]
  · simp only [NotInit]

theorem ite_notInit {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotInit a) (hb : NotInit b) :
    NotInit (if c then a else b) := by
  split <;> assumption

/-- Every instruction other than `mbarrier.init` fires no initialization. -/
theorem eventTmpl_notInit {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : initOp op = false) : NotInit (eventTmpl A L g t op) := by
  cases op
  case mbarInit => simp [initOp] at hop
  case int i => exact ruleTmpl_notInit (op := .int i)
  case move m => exact ruleTmpl_notInit (op := .move m)
  case cvt c => exact ruleTmpl_notInit (op := .cvt c)
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notInit
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notInit)
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
         | (apply ofExec_notInit)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notInit)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A template that does not initialize fires no initialization. -/
theorem fires_notInit {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hm : NotInit m)
    (hf : Fires pc m e o) : ∀ l c, e.kind ≠ .mbInit l c := by
  intro l c he
  cases m <;> simp only [Fires] at hf <;> (try simp only [NotInit] at hm) <;> aesop

/-- An instruction other than `mbarrier.init` fires no initialization. -/
theorem notInit_of_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hop : initOp op = false)
    (hf : Fires pc (eventTmpl A L g t op) e o) : ∀ l c, e.kind ≠ .mbInit l c :=
  fires_notInit (eventTmpl_notInit hop) hf

end
end PTX.Flow
