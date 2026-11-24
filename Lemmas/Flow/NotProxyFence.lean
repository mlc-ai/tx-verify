-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Proxy-fence instruction origin

A proxy fence event is fired only by a decoded proxy-fence instruction.
-/

namespace PTX.Flow

/-- A template that fires no proxy fence. -/
def NotProxyFence : Tmpl → Prop
  | .fenceProxy .. => False
  | _ => True

theorem widen_notProxyFence {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotProxyFence m) :
    NotProxyFence (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notProxyFence {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotProxyFence r) :
    NotProxyFence (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a proxy fence. -/
def proxyFenceOp : Op → Bool
  | .fence (.proxy ..) => true
  | _ => false

/-- The event of a local rule of an integer, move or conversion instruction fires no such
event. -/
theorem localSregTmpl_notProxyFence {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotProxyFence (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotProxyFence]

/-- The template of an instruction's rule, or its `noRule` fault, fires no such event. -/
theorem ruleTmpl_notProxyFence {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotProxyFence (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notProxyFence
  · simp only [NotProxyFence]

/-- An `if` of two templates that fire no such event fires none. -/
theorem ite_notProxyFence {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotProxyFence a)
    (hb : NotProxyFence b) :
    NotProxyFence (if c then a else b) := by
  split <;> assumption

/-- An instruction other than a proxy fence fires no proxy fence. -/
theorem eventTmpl_notProxyFence {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : proxyFenceOp op = false) : NotProxyFence (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notProxyFence (op := .int i)
  case move m => exact ruleTmpl_notProxyFence (op := .move m)
  case cvt c => exact ruleTmpl_notProxyFence (op := .cvt c)
  case fence f =>
    cases f with
    | thread sem scope => simp [eventTmpl, fenceTmpl, NotProxyFence]
    | proxy k o a => simp [proxyFenceOp] at hop
  all_goals simp only [proxyFenceOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notProxyFence
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notProxyFence)
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
         | (apply ofExec_notProxyFence)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notProxyFence)
         | split)
    | trivial

/-- A proxy fence is fired by a proxy-fence instruction. -/
theorem fires_proxyFence_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {kind : ProxyFence} {sc : Option MbarScope} (hk : e.kind = .fenceProxy kind sc) :
    proxyFenceOp op = true := by
  cases hq : proxyFenceOp op
  · exfalso
    have hm := eventTmpl_notProxyFence (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotProxyFence] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

end PTX.Flow
