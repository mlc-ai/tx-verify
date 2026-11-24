-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.Hooks
public import Lemmas.Execution.EventFrameBase

@[expose] public section

/-! # Warp matrix events arise only from the corresponding instruction -/

namespace PTX.Flow

open PTX

noncomputable section

/-- A template that fires no warp matrix event. -/
def NotMatrix : Tmpl → Prop
  | .matrix .. => False
  | _ => True

/-- Whether an instruction is a warp matrix instruction. -/
def matrixOp : Op → Bool
  | .matrix _ => true
  | _ => false

theorem widen_notMatrix {A : List Assumption} {site : Nat} {m : Tmpl} (h : NotMatrix m) :
    NotMatrix (widenMbarScope A site m) := by
  unfold widenMbarScope
  split
  · cases m <;> first
      | exact h
      | (split <;> trivial)
  · exact h

theorem ofExec_notMatrix {r : Exec Tmpl} (h : PTX.EventFrame.AllOk NotMatrix r) :
    NotMatrix (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- An instruction other than a warp matrix instruction fires no warp matrix event. -/
theorem eventTmpl_notMatrix {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hop : matrixOp op = false) : NotMatrix (eventTmpl A L g t op) := by
  have hw : ∀ m pc, NotMatrix m → NotMatrix (m.thenWaitLd pc) := fun m _ h => by
    cases m <;> trivial
  cases op
  case matrix => simp [matrixOp] at hop
  case warp w =>
    simp only [eventTmpl, warpTmpl]
    split
    all_goals try simp only [shflTmpl, voteTmpl, voteModeTmpl, reduxTmpl, matchTmpl,
      activemaskTmpl, electTmpl, warpBarTmpl]
    all_goals repeat' first
      | trivial
      | split
  all_goals simp only [eventTmpl]
  all_goals try refine Flow.tcLdTmpl_pres hw (fun _ => trivial) ?_
  all_goals try (refine Flow.tcStTmpl_pres (fun _ => trivial) trivial ?_; intro)
  all_goals first
    | (apply widen_notMatrix
       simp only [tmaTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notMatrix)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | dsimp only)
    | (simp only [memTmpl, accessTmpl, atomTmpl, bulkInitTmpl, acquireLoadTmpl,
        releaseStoreTmpl, loadTmpl, storeTmpl,
        barTmpl, SetMaxNReg.tmpl, fenceTmpl, cpAsyncTmpl, asyncStoreTmpl,
        tensorTmpl, tensorStoreTmpl,
        tensorPrefetchTmpl, clcTmpl, tcCommitTmpl,
        tcTmpl, mmaTmpl, localSregTmpl, sregTmpl]
       repeat' first
         | trivial
         | (apply ofExec_notMatrix)
         | (apply PTX.EventFrame.allOk_bind; intro _)
         | (apply PTX.EventFrame.allOk_ite)
         | split
         | (dsimp only; done)
         | dsimp only)
    | trivial

/-- A warp matrix event is fired by a warp matrix instruction. -/
theorem fires_matrix_op {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {mo : MatrixOp} {own recv : List (Option Byte)} (hk : e.kind = .matrix mo own recv) :
    matrixOp op = true := by
  cases hq : matrixOp op
  · exfalso
    have hm := eventTmpl_notMatrix (A := A) (L := L) (g := g) (t := t) hq
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    cases h : eventTmpl A L g t op <;> rw [h] at hm hf <;> simp only [NotMatrix] at hm <;>
      simp only [Fires] at hf <;> aesop
  · rfl

/-- Code with no warp matrix instructions fires no warp matrix event. -/
theorem no_matrix_of_code {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X)
    (hCode : K.code.all (fun ins => !matrixOp ins.op) = true)
    {i : EvId} {e : Event} (he : X.get i = some e) : isMatrix e = false := by
  obtain ⟨pc, k⟩ := e
  cases k <;> try rfl
  exact absurd ⟨_, _, _, rfl⟩ (no_kind_of_code hX matrixOp
    (fun k => ∃ op own recv, k = .matrix op own recv) (fun _ ⟨_, _, _, h⟩ => by cases h)
    (fun hf ⟨_, _, _, hk⟩ => fires_matrix_op hf hk) hCode he)

end

end PTX.Flow
