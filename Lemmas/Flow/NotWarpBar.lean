-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotWait

@[expose] public section

namespace PTX.Flow

/-- A template that is not a warp barrier. -/
def NotWarpBar : Tmpl → Prop
  | .warpBar .. => False
  | _ => True

theorem fires_notWarpBar {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState}
    (hm : NotWarpBar m) (hf : Fires pc m e o) : ∀ mask inst, e.kind ≠ .warpBar mask inst := by
  intro mask inst he
  obtain ⟨pe, ke⟩ := e
  cases m <;> simp only [NotWarpBar] at hm <;> simp only [Fires] at hf <;> aesop

theorem ofExec_notWarpBar {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotWarpBar r) :
    NotWarpBar (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

theorem widen_notWarpBar {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotWarpBar m) :
    NotWarpBar (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m
    all_goals try exact h
    case arrive m tx t count release scope =>
      cases release <;> cases scope <;> exact trivial
    case wait m parity k acquire scope =>
      cases acquire <;> cases scope <;> exact trivial
  · exact h

/-- Every instruction other than a warp barrier fires no warp barrier event. -/
theorem eventTmpl_notWarpBar {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : ∀ w : WarpInstr, op = .warp w → w.kind ≠ .barWarp) :
    NotWarpBar (eventTmpl A L g t op) := by
  cases op
  case warp w =>
    rcases w with ⟨⟨⟩, _, _, _, _⟩ <;> first
      | exact absurd rfl (hop _ rfl)
      | (simp only [eventTmpl, warpTmpl, electTmpl, shflTmpl, voteTmpl,
           voteModeTmpl, reduxTmpl, matchTmpl, activemaskTmpl]
         repeat' first
           | trivial
           | split)
  all_goals simp only [eventTmpl]
  all_goals try (apply tcLdTmpl_pres (thenWaitLd_of fun _ _ _ _ _ h => h) fun _ => trivial)
  all_goals try (refine Flow.tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notWarpBar
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notWarpBar)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        matrixTmpl, matrixMoveTmpl, tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notWarpBar)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

theorem fires_notWarpBar_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState}
    (hop : ∀ w : WarpInstr, op = .warp w → w.kind ≠ .barWarp)
    (hf : Fires pc (eventTmpl A L g t op) e o) : ∀ mask inst, e.kind ≠ .warpBar mask inst :=
  fires_notWarpBar (eventTmpl_notWarpBar hop) hf

end PTX.Flow
