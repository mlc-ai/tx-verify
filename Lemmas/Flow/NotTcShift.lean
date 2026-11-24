-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Tensor Core shifts come from shift instructions

A proof tool. Only a `tcgen05.shift` instruction fires a Tensor Core shift event
(`fires_tcShift_op`); a kernel without such instructions issues no shift. -/

namespace PTX.Flow

/-- A template that fires no Tensor Core shift. -/
def NotTcShift : Tmpl → Prop
  | .tc (.shift ..) _ => False
  | _ => True

theorem widen_notTcShift {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotTcShift m) :
    NotTcShift (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notTcShift {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotTcShift r) :
    NotTcShift (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a Tensor Core shift. -/
def tcShiftOp : Op → Bool
  | .tcShift .. => true
  | _ => false

/-- The event of a local rule of an integer, move or conversion instruction fires no such
event. -/
theorem localSregTmpl_notTcShift {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotTcShift (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotTcShift]

/-- The template of an instruction's rule, or its `noRule` fault, fires no such event. -/
theorem ruleTmpl_notTcShift {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotTcShift (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notTcShift
  · simp only [NotTcShift]

/-- An `if` of two templates that fire no such event fires none. -/
theorem ite_notTcShift {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotTcShift a)
    (hb : NotTcShift b) :
    NotTcShift (if c then a else b) := by
  split <;> assumption

/-- An instruction other than a Tensor Core shift fires no shift. -/
theorem eventTmpl_notTcShift {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : tcShiftOp op = false) : NotTcShift (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notTcShift (op := .int i)
  case move m => exact ruleTmpl_notTcShift (op := .move m)
  case cvt c => exact ruleTmpl_notTcShift (op := .cvt c)
  all_goals simp only [tcShiftOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notTcShift
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notTcShift)
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
         | (apply ofExec_notTcShift)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notTcShift)
         | split)
    | trivial

/-- A Tensor Core shift is fired by a shift instruction. -/
theorem fires_tcShift_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {spec : TcShift.Spec} (hk : e.kind = .tc (.shift spec)) : tcShiftOp op = true := by
  cases hq : tcShiftOp op
  · exfalso
    have hm := eventTmpl_notTcShift (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotTcShift] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

end PTX.Flow
