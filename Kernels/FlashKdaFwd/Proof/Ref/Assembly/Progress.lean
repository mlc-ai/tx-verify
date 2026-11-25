-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.ProgressLast

@[expose] public section

/-!
# The progress contract of the reference layer, for every consistent execution

The two deliverables of the reference layer for progress and termination
(`Proof/Top/Final.lean: Contracts`, fields `ref` and `init`), for the numbers `nums P L` and the
bound `bound P` of `ProgressNums.lean`:

    theorem refProgress (hpre : Pre P L mem0)
        (hX : Consistent L kernel Assumptions.all mem0 X)
        (hub : ∀ g k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) :
        RefProgress L mem0 X (nums P L)

    theorem init (hpre : Pre P L mem0) :
        ∀ g < L.threads, rank (nums P L) g (Thread.code L g).init ≤ bound P

`Contracts.tiles` holds by definition: `(nums P L).tiles g = ctaTiles P (g / L.block)`
(`Progress.nums_tiles`, proved by `rfl`).

**The one hypothesis beside the precondition and consistency** is `hub`: the execution has no
undefined-behaviour event. It is the three no-undefined-behaviour fields of `Top.DirectFacts`
in one statement (`Ref/Assembly/DirectNoUb.lean: Direct.noUb` proves it from the value layer's
data conditions; it does not depend on the progress contract). It is needed because the Store
phase and the epilogue state their invariant only when no undefined-behaviour event precedes
the position, and because a step along an undefined-behaviour event is in no phase's ledger.

**Where each of the 26 fields comes from** (`…_at` are the per-thread statements of the three
files before this one; a position beyond the thread's trace has the state and the events of
the last position, `Progress.clamp`):

| field | proof |
|---|---|
| `tracked` | `Tracked.lean: tracked` |
| `tile_le`, `tile_matrix` | `ProgressState.lean: tile_le_at`, `tile_matrix_at` |
| `tile_start`, `tile_end` | by the definition of the tile index |
| `bar0`, `bar8`, `coll`, `matrix` | `bar0_at`, `bar8_at`, `coll_at`, `matrix_at` |
| the five arrival bounds `arrLoadEmpty` … `arrState` | `arrLoadEmpty_at` … `arrState_at` |
| `barStep`, `left_dec` | `ProgressStep.lean: barStep_at`, `left_dec_at` |
| `exitAt` | `Ref.exit_site_pc` (the exit is fired at the exit site only) |
| `poll`, `pollStage` | `poll_at`, `pollStage_at` |
| `collShape`, `collKind` | `ProgressLast.lean: collF`, `collEvent_at`, `collTmpl_at`, … |
| `deadReleased`, `matrixShape`, `matrixPrev` | `deadReleased_at`, `matrixShape_at`, … |
| `region` | `Sites.lean: region` |
| `collAt` | `collAt_at` |
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow PTX.Sched
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (ctaTiles)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Contracts.tiles`**: the tile count of the numbers is the tile count of the thread's
block in the specification. -/
theorem Progress.nums_tiles (P : Params) (L : Launch) (g : Nat) :
    (nums P L).tiles g = ctaTiles P (g / L.block) := rfl

/-- **The progress contract of the reference layer**, for a consistent execution without an
undefined-behaviour event. -/
theorem refProgress (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ∀ g k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) :
    Proof.Progress.RefProgress L mem0 X (nums P L) := by
  have hu : ∀ g k, NoUb X g k := fun g _ i _ pc f => hub g i pc f
  refine
    { tracked := tracked hpre hX
      tile_le := ?_, tile_start := ?_, tile_end := ?_, tile_matrix := ?_, bar0 := ?_,
      bar8 := ?_, coll := ?_, matrix := ?_, arrLoadEmpty := ?_, arrStoreFull := ?_,
      arrLoadFull := ?_, arrStoreEmpty := ?_, barStep := ?_, exitAt := ?_, poll := ?_,
      collShape := ?_, collKind := ?_, deadReleased := ?_, matrixShape := ?_,
      matrixPrev := ?_, left_dec := ?_, region := ?_, collAt := ?_, pollStage := ?_,
      arrState := ?_ }
  · intro g k d hg hσ
    obtain ⟨K, hK, hσK, -⟩ := Progress.clamp hσ
    exact Progress.tile_le_at hpre hX hg (hu g) hK hσK
  · intro g k d _ _ h
    exact Progress.tileNum_start h
  · intro g k d _ _ h
    exact Progress.tileNum_end h
  · intro g k d hg hσ hm
    obtain ⟨K, hK, hσK, -⟩ := Progress.clamp hσ
    exact Progress.tile_matrix_at hpre hX hg hK hσK hm
  · intro g k d hg hσ
    obtain ⟨K, hK, hσK, htake⟩ := Progress.clamp hσ
    rw [htake]
    exact Progress.bar0_at hpre hX hg (hu g) hK hσK
  · intro g k d hg hσ hr
    obtain ⟨K, hK, hσK, htake⟩ := Progress.clamp hσ
    rw [htake]
    exact Progress.bar8_at hpre hX hg (hu g) hK hσK (by rwa [← Progress.role_eq hpre])
  · intro g k d hg hσ
    obtain ⟨K, hK, hσK, htake⟩ := Progress.clamp hσ
    rw [htake]
    exact Progress.coll_at hpre hX hg hK hσK
  · intro g k d hg hσ hr
    obtain ⟨K, hK, hσK, htake⟩ := Progress.clamp hσ
    rw [htake]
    exact Progress.matrix_at hpre hX hg (hu g) hK hσK (by rwa [← Progress.role_eq hpre])
  · intro g k d hg hσ hr s
    obtain ⟨K, hK, hσK, htake⟩ := Progress.clamp hσ
    rw [htake]
    exact Progress.arrLoadEmpty_at hpre hX hg (hu g) hK hσK
      (by rwa [← Progress.role_eq hpre]) s
  · intro g k d hg hσ hr o
    obtain ⟨K, hK, hσK, htake⟩ := Progress.clamp hσ
    rw [htake]
    exact Progress.arrStoreFull_at hpre hX hg (hu g) hK hσK
      (by rwa [← Progress.role_eq hpre]) o
  · intro g k d hg hσ hgl s
    obtain ⟨K, hK, hσK, htake⟩ := Progress.clamp hσ
    rw [htake]
    exact Progress.arrLoadFull_at hpre hX hg (hu g) hK hσK hgl s
  · intro g k d hg hσ hgl o
    obtain ⟨K, hK, hσK, htake⟩ := Progress.clamp hσ
    rw [htake]
    exact Progress.arrStoreEmpty_at hpre hX hg (hu g) hK hσK hgl o
  · intro g k pc id cnt m d d' hg hσ he hσ'
    exact Progress.barStep_at hpre hX hg (hu g) he hσ hσ'
  · intro g k pc d _ hσ he
    exact (exit_site_pc (sounds hpre) hX he hσ rfl).2
  · intro g k d hg hσ hp
    obtain ⟨K, hK, hσK, htake⟩ := Progress.clamp hσ
    rw [htake]
    exact Progress.poll_at hpre hX hg (hu g) hK hσK hp
  · exact ⟨Progress.collF, Progress.collF_full,
      fun hg hσ he hc => Progress.collEvent_at hpre hX hg hσ he hc,
      fun hg hσ hc hat hinv hout => Progress.collTmpl_at hpre hX hg hσ hc hat hinv hout⟩
  · intro g d t m s hg hσ hc hat hinv hout hs
    exact Progress.collKind_at hpre hX hg hσ hc hat hinv hout hs
  · intro g hp hσ
    exact Progress.deadReleased_at hpre hX hp.1 (hu g) hp hσ
  · intro g d t m hg hσ hm hat hout
    exact Progress.matrixShape_at hpre hX hg hσ hm hat hout
  · intro g d hg hσ hm q hq
    exact Progress.matrixPrev_at hpre hX hg hσ hm hq
  · intro g k d d' e hg he hσ hn
    exact Progress.left_dec_at hpre hX hg (hu g) he hσ hn
  · intro g k d hg hσ
    have h := region hpre hX hg hσ
    rw [← Progress.role_eq hpre] at h
    exact h
  · intro g k d hg hσ hc
    obtain ⟨K, hK, hσK, -⟩ := Progress.clamp hσ
    exact Progress.collAt_at hpre hX hg hK hσK hc
  · intro g k d hg hσ hp t ins e o hat hc hf q ok acq sc
    obtain ⟨K, hK, hσK, -⟩ := Progress.clamp hσ
    exact Progress.pollStage_at hpre hX hg (hu g) hK hσK hp hat hc hf q ok acq sc
  · intro g k d hg hσ hgl hpc
    obtain ⟨K, hK, hσK, htake⟩ := Progress.clamp hσ
    rw [htake]
    exact Progress.arrState_at hpre hX hg hK hσK hgl hpc

set_option maxRecDepth 8000 in
/-- **The bound on the counted events of a thread at its first state** (`Contracts.init`): the
first state is a state of the startup phase, whose events left are at most `400 + 100 N`, and
the tiles of the thread's sequence are at most those of a sequence as long as the batch. -/
theorem init (hpre : Pre P L mem0) :
    ∀ g < L.threads, Proof.Progress.rank (nums P L) g (Thread.code L g).init ≤ bound P := by
  intro g _
  rw [Proof.Progress.rank, show (nums P L).left = Progress.leftNum P from rfl]
  have hinit : (Thread.code L g).init = Thread.init L g := rfl
  obtain ⟨pos, hr, -⟩ := Startup.st_init (P := P) (L := L) (g := g) hpre
  have hp : (Thread.code L g).init.site.pc ≤ 384 := by
    rw [hinit, hr.site]
    exact startup_pos_pc pos
  have h1 := Startup.leftOf_le (g := g) hpre (Thread.code L g).init
  have hlen : P.length (seqOf P g) ≤ P.total := by
    have := Producer.len_le hpre g
    omega
  have ht : tiles (P.length (seqOf P g)) ≤ tiles P.total := by
    unfold tiles
    omega
  rw [Progress.leftNum_startup (by omega)]
  unfold bound
  omega

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
