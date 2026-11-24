-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotWait
public import Lemmas.Flow.Polls

@[expose] public section

/-! # Tensor Core commits

A proof tool. Only `tcgen05.commit` fires a commit event; protocol proofs counting a
thread's commits notifying a barrier use this to skip every other event. -/

namespace PTX.Flow
open PTX

noncomputable section

/-- A template that does not commit to an mbarrier. -/
def NotCommit : Tmpl → Prop
  | .tc (.commit _) _ => False
  | _ => True

theorem ofExec_notCommit {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotCommit r) :
    NotCommit (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem widen_notCommit {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotCommit m) :
    NotCommit (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals first
      | exact h
      | (case arrive m' tx t count release scope => cases release <;> cases scope <;> exact h)
      | (case wait m' parity k acquire scope => cases acquire <;> cases scope <;> exact h)
  · exact h

/-- The event of a local rule of an integer, move or conversion instruction commits nothing. -/
theorem localSregTmpl_notCommit {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotCommit (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotCommit]

/-- The template of an instruction's rule, or its `noRule` fault, commits nothing. -/
theorem ruleTmpl_notCommit {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    NotCommit (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notCommit
  · simp only [NotCommit]

/-- An `if` of two templates that commit nothing commits nothing. -/
theorem ite_notCommit {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotCommit a)
    (hb : NotCommit b) : NotCommit (if c then a else b) := by
  split <;> assumption

/-- A template that is a `ub` fault on a failed execution and `ok` on a successful one commits
    nothing when both do not. -/
theorem exec_notCommit {α : Type} {r : Exec α} {ub : Fault → Tmpl} {ok : α → Tmpl}
    (hub : ∀ f, NotCommit (ub f)) (hok : ∀ a, NotCommit (ok a)) :
    NotCommit (match r with | .error f => ub f | .ok a => ok a) := by
  cases r with
  | error f => exact hub f
  | ok a => exact hok a

/-- Every instruction other than `tcgen05.commit` fires no commit event. -/
theorem eventTmpl_notCommit {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : ∀ (group : CtaGroup) (base : Nat) (off : Int) (mask : Option Opnd),
      op ≠ .tcCommit group base off mask) :
    NotCommit (eventTmpl A L g t op) := by
  cases op
  case tcCommit group base off mask => exact absurd rfl (hop _ _ _ _)
  case int i => exact ruleTmpl_notCommit (op := .int i)
  case move m => exact ruleTmpl_notCommit (op := .move m)
  case cvt c => exact ruleTmpl_notCommit (op := .cvt c)
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notCommit
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notCommit)
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
        tensorPrefetchTmpl, clcTmpl, tcTmpl, mmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notCommit)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notCommit)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A template that does not commit fires no commit event. -/
theorem fires_notCommit {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState} (hm : NotCommit m)
    (hf : Fires pc m e o) : ∀ sp, e.kind ≠ .tc (.commit sp) := by
  intro sp he
  cases m <;> simp only [Fires] at hf <;> (try cases ‹TcKind›) <;>
    (try simp only [NotCommit] at hm) <;> aesop

/-- Whether an instruction is a Tensor Core commit. -/
def commitOp : Op → Bool
  | .tcCommit .. => true
  | _ => false

theorem commitOp_ne {op : Op} (h : commitOp op = false) :
    ∀ (group : CtaGroup) (base : Nat) (off : Int) (mask : Option Opnd),
      op ≠ .tcCommit group base off mask := by
  intro group base off mask hop
  subst hop
  simp [commitOp] at h



/-- Whether event `e` is a Tensor Core commit that notifies barrier `m`. -/
def commitsTo (m : Loc) (e : Event) : Bool := match e.kind with
  | .tc (.commit sp) => decide (sp.mbar = m)
  | _ => false

theorem commitsTo_of_kind {m : Loc} {e : Event} {sp : TcCommit.Spec}
    (hk : e.kind = .tc (.commit sp)) : commitsTo m e = decide (sp.mbar = m) := by
  simp [commitsTo, hk]

theorem commitsTo_of_notCommit {m : Loc} {e : Event} (h : ∀ sp, e.kind ≠ .tc (.commit sp)) :
    commitsTo m e = false := by
  unfold commitsTo
  split
  · rename_i sp heq
    exact absurd heq (h sp)
  · rfl

theorem okPoll_of_kind {m : Loc} {e : Event} {k : TcKind} (hk : e.kind = .tc k) :
    okPoll m e = false := by
  simp [okPoll, sourceWaitSuccess, hk]

theorem commits_snoc (m : Loc) (es : List Event) (e : Event) :
    (es ++ [e]).countP (commitsTo m) =
      es.countP (commitsTo m) + if commitsTo m e then 1 else 0 := by
  simp only [List.countP_append, List.countP_singleton]

end
end PTX.Flow
