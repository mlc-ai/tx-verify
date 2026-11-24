-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotBulk

@[expose] public section

/-! # Atomic read-modify-writes come from atomic instructions

A proof tool. Only a memory instruction with the atomic rule (`atom`, `red`; THREAD-ATOMIC) fires
an atomic read-modify-write event (`fires_rmw_op`). With `no_kind_of_code`, a kernel without such
instructions has no such event in any consistent execution. -/

namespace PTX.Flow

/-- A template that fires no atomic read-modify-write. -/
def NotRmw : Tmpl → Prop
  | .rmw .. => False
  | _ => True

/-- Whether an instruction is a memory access with the atomic rule. -/
def atomicOp : Op → Bool
  | .mem a => decide (a.rule = some .threadAtomic)
  | _ => false

theorem widen_notRmw {A : List Assumption} {site : Nat} {m : Tmpl}
    (h : NotRmw m) : NotRmw (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notRmw {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotRmw r) :
    NotRmw (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- An instruction other than an atomic memory access fires no read-modify-write. -/
theorem eventTmpl_notRmw {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} (hop : atomicOp op = false) : NotRmw (eventTmpl A L g t op) := by
  cases op
  case mem a =>
    have hr : a.rule ≠ some .threadAtomic := by simpa [atomicOp] using hop
    simp only [eventTmpl, memTmpl]
    repeat' first
      | trivial
      | (simp only [accessTmpl, acquireLoadTmpl, releaseStoreTmpl, loadTmpl, storeTmpl,
          bulkInitTmpl])
      | split
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notRmw
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notRmw)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [warpTmpl, barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notRmw)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- An atomic read-modify-write is fired by a memory instruction with the atomic rule. -/
theorem fires_rmw_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Acc} {old : List (Option Byte)} {new : Option (List Byte)}
    (hk : e.kind = .rmw a old new) : atomicOp op = true := by
  cases hq : atomicOp op
  · exfalso
    have hm := eventTmpl_notRmw (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotRmw] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

end PTX.Flow
