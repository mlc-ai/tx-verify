-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Instructions that fire no register request

A proof tool. A register request event (`setmaxnreg`) is fired by a register adjustment
instruction, with that instruction's direction and count. -/

namespace PTX.Flow

/-- A template that fires no register request. -/
def NotSetMaxReg : Tmpl → Prop
  | .setMaxReg .. => False
  | _ => True

theorem widen_notSetMaxReg {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotSetMaxReg m) :
    NotSetMaxReg (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notSetMaxReg {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotSetMaxReg r) :
    NotSetMaxReg (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a register adjustment. -/
def setMaxRegOp : Op → Bool
  | .setMaxReg .. => true
  | _ => false

/-- The event of a local rule of an integer, move or conversion instruction is no register
request. -/
theorem localSregTmpl_notSetMaxReg {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotSetMaxReg (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotSetMaxReg]

/-- The template of an instruction's rule, or its `noRule` fault, is no register request. -/
theorem ruleTmpl_notSetMaxReg {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotSetMaxReg (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notSetMaxReg
  · simp only [NotSetMaxReg]

/-- An `if` of two templates that fire no register request fires none. -/
theorem ite_notSetMaxReg {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotSetMaxReg a)
    (hb : NotSetMaxReg b) : NotSetMaxReg (if c then a else b) := by
  split <;> assumption

/-- An instruction other than a register adjustment fires no register request. -/
theorem eventTmpl_notSetMaxReg {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} (hop : setMaxRegOp op = false) : NotSetMaxReg (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notSetMaxReg (op := .int i)
  case move m => exact ruleTmpl_notSetMaxReg (op := .move m)
  case cvt c => exact ruleTmpl_notSetMaxReg (op := .cvt c)
  all_goals simp only [setMaxRegOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notSetMaxReg
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notSetMaxReg)
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
         | (apply ofExec_notSetMaxReg)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notSetMaxReg)
         | split)
    | trivial

/-- A register request is fired by the register adjustment with its direction and count. -/
theorem fires_setMaxReg_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {inc : Bool} {n inst : Nat} (hk : e.kind = .setMaxReg inc n inst) : op = .setMaxReg inc n := by
  cases hq : setMaxRegOp op
  · exfalso
    have hm := eventTmpl_notSetMaxReg (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotSetMaxReg] at hm <;>
      simp only [Fires] at hf <;> aesop
  · cases op <;> simp only [setMaxRegOp, Bool.false_eq_true] at hq
    rename_i inc' n'
    simp only [eventTmpl, SetMaxNReg.tmpl] at hf
    split at hf
    · obtain ⟨inst', rfl, -⟩ := hf
      simp only [Kind.setMaxReg.injEq] at hk
      obtain ⟨rfl, rfl, -⟩ := hk
      rfl
    · simp only [Fires] at hf
      obtain ⟨rfl, -⟩ := hf
      cases hk

/-- A valid register adjustment fires a register request. -/
theorem fires_of_setMaxReg_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {o : Option TState}
    {inc : Bool} {n pc : Nat} {e : Event} (hv : SetMaxNReg.validCount n = true)
    (hf : Fires pc (eventTmpl A L g t (.setMaxReg inc n)) e o) :
    ∃ inst, e = ⟨pc, .setMaxReg inc n inst⟩ := by
  simp only [eventTmpl, SetMaxNReg.tmpl, hv, ite_true] at hf
  obtain ⟨inst, he, -⟩ := hf
  exact ⟨inst, he⟩

end PTX.Flow
