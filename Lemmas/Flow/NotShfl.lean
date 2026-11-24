-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotWait
public import Lemmas.Flow.Polls
public import Lemmas.Kernel.PlainStep

@[expose] public section

/-! # Shuffles

A proof tool. Only `shfl.sync` fires a shuffle event (`fires_shfl_op`); a thread machine that
counts a thread's shuffles uses this to skip every other event. A shuffle fired by a full-warp
`shfl.sync.idx` from lane 0 of a register has the register's value as its operand
(`fires_shfl_idx`). -/

namespace PTX.Flow
open PTX

noncomputable section

/-- A template that does not shuffle. -/
def NotShfl : Tmpl → Prop
  | .shfl .. => False
  | _ => True

theorem ofExec_notShfl {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotShfl r) :
    NotShfl (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem widen_notShfl {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotShfl m) :
    NotShfl (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals first
      | exact h
      | (case arrive m' tx t count release scope => cases release <;> cases scope <;> exact h)
      | (case wait m' parity k acquire scope => cases acquire <;> cases scope <;> exact h)
  · exact h

/-- The event of a local rule of an integer, move or conversion instruction is no shuffle. -/
theorem localSregTmpl_notShfl {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotShfl (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotShfl]

/-- The template of an instruction's rule, or its `noRule` fault, is no shuffle. -/
theorem ruleTmpl_notShfl {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op} :
    NotShfl (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notShfl
  · simp only [NotShfl]

/-- An `if` of two templates that do not shuffle does not shuffle. -/
theorem ite_notShfl {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotShfl a) (hb : NotShfl b) :
    NotShfl (if c then a else b) := by
  split <;> assumption

/-- Every instruction other than `shfl.sync` fires no shuffle. -/
theorem eventTmpl_notShfl {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : op.isShfl = false) : NotShfl (eventTmpl A L g t op) := by
  cases op
  case warp w =>
    rcases w with ⟨⟨⟩, _, _, _, _⟩ <;> first
      | (simp [Op.isShfl] at hop; done)
      | (simp only [eventTmpl, warpTmpl, warpBarTmpl, electTmpl, voteTmpl, voteModeTmpl,
           reduxTmpl, matchTmpl, activemaskTmpl]
         repeat' first
           | trivial
           | split)
  case int i => exact ruleTmpl_notShfl (op := .int i)
  case move m => exact ruleTmpl_notShfl (op := .move m)
  case cvt c => exact ruleTmpl_notShfl (op := .cvt c)
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notShfl
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notShfl)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        SetMaxNReg.tmpl, matrixTmpl, matrixMoveTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcTmpl, tcCommitTmpl, mmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notShfl)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notShfl)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- **A shuffle event is fired by a `shfl.sync`.** -/
theorem fires_shfl_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    (hs : Execution.isShfl e = true) : op.isShfl = true := by
  by_contra hq
  have hm := eventTmpl_notShfl (A := A) (L := L) (g := g) (t := t) (by simpa using hq)
  obtain ⟨epc, ek⟩ := e
  cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotShfl] at hm <;>
    simp only [Fires] at hf <;> cases ek <;> simp_all [Execution.isShfl]

/-- **A full-warp `shfl.sync.idx` from lane 0 of register `r`** fires a shuffle whose operand
is the register's value. -/
theorem fires_shfl_idx {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {d r : Nat}
    {p : Option Nat} {ty : Option DType} {mask : Opnd} {pc : Nat} {e : Event}
    {o : Option TState} {v : Value} (hr : t.regs r = some v)
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.shfl .idx, ty, some d :: (p.map some).toList,
      [.reg r, .imm 0, .imm 31], some mask⟩)) e o)
    (hs : Execution.isShfl e = true) : ∃ recv ok, e = ⟨pc, .shfl .idx v 0 31 recv ok⟩ := by
  have h0 : (truncBits 32 (BitVec.ofInt 64 0)).toNat = 0 := by decide
  have h31 : (truncBits 32 (BitVec.ofInt 64 31)).toNat = 31 := by decide
  have hp : (p.map some).toList.head?.join = p := by cases p <;> rfl
  simp only [eventTmpl] at hf
  rcases warpTmpl_shfl (L := L) (g := g) (t := t) (mode := .idx) (ty := ty) (d := d)
    (ps := (p.map some).toList) (a := .reg r) (b := .imm 0) (c := .imm 31) (mask := mask) with
    h | h <;> rw [h] at hf
  swap
  · obtain ⟨epc, ek⟩ := e
    simp_all [Fires, Execution.isShfl]
  rw [hp] at hf
  simp only [shflTmpl, readValue, readReg, hr, readBits] at hf
  repeat' (split at hf)
  all_goals simp_all [Fires, pure, Except.pure, bind, Except.bind, Execution.isShfl]
  all_goals subst_vars
  all_goals aesop

end
end PTX.Flow
