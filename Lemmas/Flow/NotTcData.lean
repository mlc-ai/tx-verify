-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # Tensor Memory loads, stores and their waits come from their instructions

A proof tool. A warp-collective `tcgen05` data event (a load, a store, or the wait for one) is fired
only by its instruction (`fires_tcData_op`), so the data events of a kernel are at the positions of
those instructions. A Tensor Memory load wait fires its event when the block is a multiple of the
warp size (`fires_tcWaitLd`). -/

namespace PTX.Flow

/-- A warp-collective `tcgen05` data event: a Tensor Memory load, a store, or the wait for one. -/
def isTcData (e : Event) : Bool := match e.kind with
  | .tc (.ld ..) | .tc .waitLd | .tc (.st ..) | .tc .waitSt => true
  | _ => false

/-- A template that fires no data event. -/
def NotTcData : Tmpl → Prop
  | .tc (.ld ..) _ | .tc .waitLd _ | .tc (.st ..) _ | .tc .waitSt _ | .tcLd .. => False
  | _ => True

theorem widen_notTcData {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotTcData m) :
    NotTcData (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notTcData {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotTcData r) :
    NotTcData (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- Whether an instruction is a Tensor Memory load, a store, or the wait for one. -/
def tcDataOp : Op → Bool
  | .tcLd .. | .tcWaitLd | .tcSt .. | .tcWaitSt => true
  | _ => false

/-- The event of a local rule of an integer, move or conversion instruction fires no such
event. -/
theorem localSregTmpl_notTcData {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {r : RuleId} {op : Op} : NotTcData (localSregTmpl A L g t r op) := by
  cases r <;> simp only [localSregTmpl, sregTmpl, NotTcData]

/-- The template of an instruction's rule, or its `noRule` fault, fires no such event. -/
theorem ruleTmpl_notTcData {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} : NotTcData (match op.rule with
      | some r => localSregTmpl A L g t r op
      | none => Tmpl.ub Fault.noRule) := by
  split
  · exact localSregTmpl_notTcData
  · simp only [NotTcData]

/-- An `if` of two templates that fire no such event fires none. -/
theorem ite_notTcData {c : Prop} [Decidable c] {a b : Tmpl} (ha : NotTcData a) (hb : NotTcData b) :
    NotTcData (if c then a else b) := by
  split <;> assumption

/-- An instruction other than a data instruction fires no data event. -/
theorem eventTmpl_notTcData {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : tcDataOp op = false) : NotTcData (eventTmpl A L g t op) := by
  cases op
  case int i => exact ruleTmpl_notTcData (op := .int i)
  case move m => exact ruleTmpl_notTcData (op := .move m)
  case cvt c => exact ruleTmpl_notTcData (op := .cvt c)
  all_goals simp only [tcDataOp] at hop
  all_goals simp only [eventTmpl]
  all_goals first
    | (apply widen_notTcData
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notTcData)
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
         | (apply ofExec_notTcData)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | (apply ite_notTcData)
         | split)
    | trivial

/-- A data event is fired by a data instruction. -/
theorem fires_tcData_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    (hk : isTcData e = true) : tcDataOp op = true := by
  cases hq : tcDataOp op
  · exfalso
    have hm := eventTmpl_notTcData (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only [isTcData] at hk
    split at hk
    all_goals
      cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotTcData] at hm <;>
        simp only [Fires] at hf <;> aesop
  · rfl

/-- A Tensor Memory load wait fires its event, in a block of whole warps. -/
theorem fires_tcWaitLd {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat}
    {e : Event} {o : Option TState} (hb : L.block % 32 = 0)
    (hf : Fires pc (eventTmpl A L g t .tcWaitLd) e o) : e = ⟨pc, .tc .waitLd⟩ := by
  simp only [eventTmpl, tcTmpl, hb, ofExec, pure, Except.pure, ↓reduceIte] at hf
  exact hf.1

end PTX.Flow
