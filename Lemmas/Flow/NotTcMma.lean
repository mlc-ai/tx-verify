-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Tensor Core MMAs come from MMA instructions

A proof tool. Only a `tcgen05.mma` instruction fires an MMA event (`fires_tcMma_op`), so the
MMAs of a kernel are at the positions of its MMA instructions. -/

namespace PTX.Flow

/-- A template that fires no MMA. -/
def NotTcMma : Tmpl → Prop
  | .tc (.mma ..) _ => False
  | _ => True

theorem widen_notTcMma {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotTcMma m) :
    NotTcMma (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notTcMma {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotTcMma r) :
    NotTcMma (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is an MMA. -/
def tcMmaOp : Op → Bool
  | .tcMma _ => true
  | _ => false

/-- The event of a local rule of an integer, move or conversion instruction fires no such
event. -/
theorem localSregTmpl_notTcMma {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotTcMma (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotTcMma]

/-- The template of an instruction's rule, or its `noRule` fault, fires no such event. -/
theorem ruleTmpl_notTcMma {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotTcMma (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notTcMma
  · simp only [NotTcMma]

/-- An `if` of two templates that fire no such event fires none. -/
theorem ite_notTcMma {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotTcMma a) (hb : NotTcMma b) :
    NotTcMma (if c then a else b) := by
  split <;> assumption

/-- An instruction other than an MMA fires no MMA. -/
theorem eventTmpl_notTcMma {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : tcMmaOp op = false) : NotTcMma (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notTcMma (op := .int i)
  case move m => exact ruleTmpl_notTcMma (op := .move m)
  case cvt c => exact ruleTmpl_notTcMma (op := .cvt c)
  all_goals simp only [tcMmaOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notTcMma
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notTcMma)
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
         | (apply ofExec_notTcMma)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notTcMma)
         | split)
    | trivial

/-- An MMA is fired by an MMA instruction. -/
theorem fires_tcMma_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {dst : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hk : e.kind = .tc (.mma dst sp acc mask)) :
    tcMmaOp op = true := by
  cases hq : tcMmaOp op
  · exfalso
    have hm := eventTmpl_notTcMma (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotTcMma] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

end PTX.Flow
