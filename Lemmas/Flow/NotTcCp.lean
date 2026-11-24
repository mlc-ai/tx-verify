-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Tensor Core copies come from copy instructions

A proof tool. Only a `tcgen05.cp` instruction fires a Tensor Core copy event
(`fires_tcCp_op`); a kernel without such instructions issues no copy. -/

namespace PTX.Flow

/-- A template that fires no Tensor Core copy. -/
def NotTcCp : Tmpl → Prop
  | .tc (.cp ..) _ => False
  | _ => True

theorem widen_notTcCp {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotTcCp m) :
    NotTcCp (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notTcCp {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotTcCp r) :
    NotTcCp (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a Tensor Core copy. -/
def tcCpOp : Op → Bool
  | .tcCp .. => true
  | _ => false

/-- The event of a local rule of an integer, move or conversion instruction fires no such
event. -/
theorem localSregTmpl_notTcCp {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotTcCp (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotTcCp]

/-- The template of an instruction's rule, or its `noRule` fault, fires no such event. -/
theorem ruleTmpl_notTcCp {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotTcCp (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notTcCp
  · simp only [NotTcCp]

/-- An `if` of two templates that fire no such event fires none. -/
theorem ite_notTcCp {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotTcCp a) (hb : NotTcCp b) :
    NotTcCp (if c then a else b) := by
  split <;> assumption

/-- An instruction other than a Tensor Core copy fires no copy. -/
theorem eventTmpl_notTcCp {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : tcCpOp op = false) : NotTcCp (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notTcCp (op := .int i)
  case move m => exact ruleTmpl_notTcCp (op := .move m)
  case cvt c => exact ruleTmpl_notTcCp (op := .cvt c)
  all_goals simp only [tcCpOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notTcCp
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notTcCp)
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
         | (apply ofExec_notTcCp)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notTcCp)
         | split)
    | trivial

/-- A Tensor Core copy is fired by a copy instruction. -/
theorem fires_tcCp_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {spec : TcCopy.Spec} (hk : e.kind = .tc (.cp spec)) : tcCpOp op = true := by
  cases hq : tcCpOp op
  · exfalso
    have hm := eventTmpl_notTcCp (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotTcCp] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

end PTX.Flow
