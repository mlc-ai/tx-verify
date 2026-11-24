-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Non-coherent loads need an assumption that allows them

A proof tool. A `ld.global.nc` fires a non-coherent read only under an assumption that allows
such loads at its site (`Assumption.ncLoads`); otherwise it is undefined behaviour. So a thread
run under assumptions that allow none fires no non-coherent read (`fires_not_nc`). -/

namespace PTX.Flow

/-- A template that fires no non-coherent read. -/
def NotNc : Tmpl → Prop
  | .readNC .. => False
  | _ => True

theorem widen_notNc {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotNc m) :
    NotNc (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notNc {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotNc r) :
    NotNc (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- The event of a local rule of an integer, move or conversion instruction is no non-coherent
read. -/
theorem localSregTmpl_notNc {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotNc (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotNc]

/-- The template of an instruction's rule, or its `noRule` fault, is no non-coherent read. -/
theorem ruleTmpl_notNc {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    NotNc (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notNc
  · simp only [NotNc]

/-- An `if` of two templates that fire no non-coherent read fires none. -/
theorem ite_notNc {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotNc a) (hb : NotNc b) :
    NotNc (if c then a else b) := by
  split <;> assumption

/-- Under assumptions that allow no non-coherent load, no instruction fires one. -/
theorem eventTmpl_notNc {A : List Assumption} {L : Launch} {g : Nat} {t : TState} (op : Op)
    (hA : A.any (·.ncLoads t.pc) = false) : NotNc (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notNc (op := .int i)
  case move m => exact ruleTmpl_notNc (op := .move m)
  case cvt c => exact ruleTmpl_notNc (op := .cvt c)
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notNc
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notNc)
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
        tcTmpl, mmaTmpl, tensorTmpl, tensorMulticast, hA, Bool.false_eq_true, and_false]
       repeat' first
         | trivial
         | (apply ofExec_notNc)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notNc)
         | split)
    | trivial

/-- **No non-coherent read** is fired under assumptions that allow none. -/
theorem fires_not_nc {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hA : A.any (·.ncLoads t.pc) = false)
    (hf : Fires pc (eventTmpl A L g t op) e o) {a : Acc} {bs : List (Option Byte)} :
    e.kind ≠ .nc a bs := by
  intro hk
  have hm := eventTmpl_notNc (L := L) (g := g) (t := t) op hA
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotNc] at hm <;>
    simp only [Fires] at hf <;> aesop

end PTX.Flow
