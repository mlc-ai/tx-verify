-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.Static
public import Lemmas.Flow.NotClc
public import Lemmas.Execution.NoAsync
public import Lemmas.Kernel.PlainSafety
public import Lemmas.Flow.Hooks

@[expose] public section

/-!
# Branches of `Unsafe` that need an event the kernel never issues

The decoded program has no cluster barrier instruction, no warp matrix instruction, no cluster
launch control request, no tensor store and no linear copy, so no execution of it has such an
event (`Flow.no_kind_of_code`, with the audits by `decide +kernel`). Then the branches of `Unsafe`
that name such an event are empty: `ClusterFault`, `MatrixUnsafe`, `ClcUnsafe`, `TensorStoreUnsafe`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### No warp matrix instruction -/

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

theorem kernel_noMatrix : kernel.code.all (fun ins => !matrixOp ins.op) = true := by
  decide +kernel

theorem kernel_noCluster : kernel.code.all (fun ins => !clusterOp ins.op) = true := by
  decide +kernel

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

/-- **The kernel has no warp matrix event.** -/
theorem no_matrix_ev (hX : Consistent L kernel asms mem0 X) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : isMatrix ev = false := by
  obtain ⟨pc, k⟩ := ev
  cases k <;> try rfl
  exact absurd ⟨_, _, _, rfl⟩ (Flow.no_kind_of_code hX matrixOp
    (fun k => ∃ op own recv, k = .matrix op own recv) (fun _ ⟨_, _, _, h⟩ => by cases h)
    (fun hf ⟨_, _, _, hk⟩ => fires_matrix_op hf hk) kernel_noMatrix he)

/-- **No warp matrix instance is undefined.** -/
theorem no_matrixUnsafe (hX : Consistent L kernel asms mem0 X) : ¬ MatrixUnsafe L asms X :=
  not_matrixUnsafe_of_none (L := L) fun _ _ he => no_matrix_ev hX he

/-! ### No cluster barrier, no cancellation request, no tensor store, no linear copy -/

/-- **The kernel has no cluster barrier event.** -/
theorem no_cluster (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {op : ClusterOp}, X.get i ≠ some ⟨pc, .cluster op⟩ :=
  fun he => no_kind_of_code hX clusterOp (fun k => ∃ op, k = .cluster op)
    (fun _ ⟨_, h⟩ => by cases h)
    (fun hf ⟨_, hk⟩ => by rw [fires_cluster_op hf hk]; rfl) kernel_noCluster he ⟨_, rfl⟩

/-- **No cluster barrier faults**: a faulting record names an issued cluster instruction. -/
theorem no_clusterFault (hX : Consistent L kernel asms mem0 X) : ¬ ClusterFault L X := by
  rintro ⟨c, -, s, -, r, err, hsrc, -, hp, hf⟩
  cases r with
  | exit g e =>
    simp only [ClusterBarrier.Record.perform, ClusterBarrier.perform] at hp
    split at hp
    · cases hp; simp [ClusterBarrier.Error.isFault] at hf
    · cases hp
  | arrival cta warp release lanes =>
    simp only [ClusterBarrier.Record.perform] at hp
    split at hp
    · rename_i hv
      obtain ⟨p, hp'⟩ := List.exists_mem_of_ne_nil lanes (fun hnil => by
        have := (of_decide_eq_true hv).2.2.2.1
        simp only [ne_eq, List.map_eq_nil_iff] at this
        exact this hnil)
      obtain ⟨-, -, pc, al, hg⟩ := hsrc p hp'
      exact no_cluster hX hg
    · cases hp; simp [ClusterBarrier.Error.isFault] at hf
  | wait cta warp lanes =>
    simp only [ClusterBarrier.Record.perform] at hp
    split at hp
    · rename_i hv
      obtain ⟨p, hp'⟩ := List.exists_mem_of_ne_nil lanes (fun hnil => by
        have := (of_decide_eq_true hv).2.2.2.1
        simp only [ne_eq, List.map_eq_nil_iff] at this
        exact this hnil)
      obtain ⟨-, -, pc, al, hg⟩ := hsrc p hp'
      exact no_cluster hX hg
    · cases hp; simp [ClusterBarrier.Error.isFault] at hf

/-- **No cancellation request is unsafe**: the kernel issues none. -/
theorem no_clcUnsafe (hX : Consistent L kernel asms mem0 X) : ¬ ClcUnsafe L X := by
  rintro ⟨i, s, tg, q, pc, r, ⟨pc', he⟩, -⟩
  exact no_clc hX he

/-- **No tensor or linear reduction lacks a rule**: the kernel has no tensor store and no linear
copy. -/
theorem no_tensorStoreUnsafe (hX : Consistent L kernel asms mem0 X) :
    ¬ TensorStoreUnsafe asms X := by
  rintro (⟨i, o, -, -, -, hio, -⟩ | ⟨i, s, -, -, ⟨pc, hi⟩, -⟩)
  · obtain ⟨⟨addr, pc, hi⟩, -⟩ := hX.store i o hio
    exact no_tensorStore hX hi
  · exact no_copy hX hi

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
