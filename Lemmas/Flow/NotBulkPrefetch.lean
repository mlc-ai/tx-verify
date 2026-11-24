-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotBulk

@[expose] public section

/-! # Bulk prefetches come from their instructions

A proof tool. Only a `cp.async.bulk.prefetch` fires a bulk prefetch (`fires_bulkPrefetch_op`).
With `no_kind_of_code`, a kernel without such instructions has no such event in any consistent
execution. -/

namespace PTX.Flow

/-- A template that fires no bulk prefetch. -/
def NotBulkPrefetch : Tmpl → Prop
  | .bulkPrefetch .. => False
  | _ => True

/-- Whether an instruction is a `cp.async.bulk.prefetch`. -/
def bulkPrefetchOp : Op → Bool
  | .prefetchBulk .. => true
  | _ => false

theorem widen_notBulkPrefetch {A : List Assumption} {site : Nat} {m : Tmpl}
    (h : NotBulkPrefetch m) : NotBulkPrefetch (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notBulkPrefetch {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotBulkPrefetch r) :
    NotBulkPrefetch (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- An instruction other than `cp.async.bulk.prefetch` fires no bulk prefetch. -/
theorem eventTmpl_notBulkPrefetch {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} (hop : bulkPrefetchOp op = false) : NotBulkPrefetch (eventTmpl A L g t op) := by
  cases op <;> simp only [bulkPrefetchOp] at hop
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notBulkPrefetch
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notBulkPrefetch)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, warpTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl,
        warpBarTmpl, electTmpl, shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
        activemaskTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notBulkPrefetch)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A bulk prefetch is fired by a `cp.async.bulk.prefetch`. -/
theorem fires_bulkPrefetch_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Acc} (hk : e.kind = .bulkPrefetch a) : bulkPrefetchOp op = true := by
  cases hq : bulkPrefetchOp op
  · exfalso
    have hm := eventTmpl_notBulkPrefetch (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotBulkPrefetch] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

end PTX.Flow
