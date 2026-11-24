-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Thread fences come from `fence.sc` and `fence.acq_rel` instructions

A proof tool. Only a `fence.sc` or `fence.acq_rel` instruction fires a thread fence
(`fires_threadFence_op`); a kernel without such instructions makes no thread fence. -/

namespace PTX.Flow

/-- A template that fires no thread fence. -/
def NotThreadFence : Tmpl → Prop
  | .fence .. => False
  | _ => True

theorem widen_notThreadFence {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotThreadFence m) :
    NotThreadFence (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notThreadFence {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotThreadFence r) :
    NotThreadFence (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a thread fence. -/
def threadFenceOp : Op → Bool
  | .fence (.thread ..) => true
  | _ => false

/-- The event of a local rule of an integer, move or conversion instruction fires no such
event. -/
theorem localSregTmpl_notThreadFence {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotThreadFence (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotThreadFence]

/-- The template of an instruction's rule, or its `noRule` fault, fires no such event. -/
theorem ruleTmpl_notThreadFence {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotThreadFence (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notThreadFence
  · simp only [NotThreadFence]

/-- An `if` of two templates that fire no such event fires none. -/
theorem ite_notThreadFence {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotThreadFence a)
    (hb : NotThreadFence b) :
    NotThreadFence (if c then a else b) := by
  split <;> assumption

/-- An instruction other than a thread fence fires no thread fence. -/
theorem eventTmpl_notThreadFence {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : threadFenceOp op = false) : NotThreadFence (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notThreadFence (op := .int i)
  case move m => exact ruleTmpl_notThreadFence (op := .move m)
  case cvt c => exact ruleTmpl_notThreadFence (op := .cvt c)
  case fence f =>
    cases f with
    | thread sem scope => simp [threadFenceOp] at hop
    | proxy k o a =>
      simp only [eventTmpl, fenceTmpl]
      repeat' first | trivial | (simp_all; done) | split
  all_goals simp only [threadFenceOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notThreadFence
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notThreadFence)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, tensorStoreTmpl,
        reduxTmpl, matchTmpl, activemaskTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, tensorTmpl, tensorMulticast]
       repeat' first
         | trivial
         | (apply ofExec_notThreadFence)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notThreadFence)
         | split)
    | trivial

/-- A thread fence is fired by a thread-fence instruction. -/
theorem fires_threadFence_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {sem : FenceSem} {sc : MbarScope} (hk : e.kind = .fence sem sc) : threadFenceOp op = true := by
  cases hq : threadFenceOp op
  · exfalso
    have hm := eventTmpl_notThreadFence (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotThreadFence] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

end PTX.Flow
