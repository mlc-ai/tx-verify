-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Tensor Memory stores come from store instructions

A proof tool. Only a `tcgen05.st` instruction fires a Tensor Memory store event
(`fires_tcSt_op`); a kernel without such instructions issues no store. -/

namespace PTX.Flow

/-- A template that fires no Tensor Memory store. -/
def NotTcSt : Tmpl → Prop
  | .tc (.st ..) _ => False
  | _ => True

theorem widen_notTcSt {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotTcSt m) :
    NotTcSt (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notTcSt {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotTcSt r) :
    NotTcSt (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a Tensor Memory store. -/
def tcStOp : Op → Bool
  | .tcSt .. => true
  | _ => false

/-- The event of a local rule of an integer, move or conversion instruction fires no such
event. -/
theorem localSregTmpl_notTcSt {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotTcSt (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotTcSt]

/-- The template of an instruction's rule, or its `noRule` fault, fires no such event. -/
theorem ruleTmpl_notTcSt {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotTcSt (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notTcSt
  · simp only [NotTcSt]

/-- An `if` of two templates that fire no such event fires none. -/
theorem ite_notTcSt {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotTcSt a) (hb : NotTcSt b) :
    NotTcSt (if c then a else b) := by
  split <;> assumption

/-- An instruction other than a Tensor Memory store fires no store. -/
theorem eventTmpl_notTcSt {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : tcStOp op = false) : NotTcSt (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notTcSt (op := .int i)
  case move m => exact ruleTmpl_notTcSt (op := .move m)
  case cvt c => exact ruleTmpl_notTcSt (op := .cvt c)
  all_goals simp only [tcStOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals first
    | (apply widen_notTcSt
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notTcSt)
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
         | (apply ofExec_notTcSt)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notTcSt)
         | split)
    | trivial

/-- A Tensor Memory store is fired by a store instruction. -/
theorem fires_tcSt_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) :
    tcStOp op = true := by
  cases hq : tcStOp op
  · exfalso
    have hm := eventTmpl_notTcSt (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotTcSt] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

end PTX.Flow
