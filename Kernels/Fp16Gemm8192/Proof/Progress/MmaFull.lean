-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.LoaderEmpty
public import Kernels.Fp16Gemm8192.Proof.Progress.MmaFullBlocker
public import Lemmas.Protocol.MbarPending
public import Lemmas.MBarrier.MBarrierInitOrder

@[expose] public section

/-! # Progress at an MMA thread's full wait

A pending MMA thread at a slot's full wait, whose last event is released, extends a maximal
execution or passes to an obligation of smaller rank (`mma_full_steps`), by the mbarrier wait step
`Descent.mbar_wait_steps`: its successful poll is a counted extension, and a failed poll is blocked.
The blocked case is proved per execution (`mma_full_blocked_of`, `Progress/MmaFullBlocker`), from
the thread facts and the protocol exports of `MmaFullFacts`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow MBarrier AsyncCopy

noncomputable section

/-- The per-execution exports the MMA full blocker uses, for every consistent execution: the thread
facts, the input-full blocker, the agreement of the CLC readers, and the cluster's exit. -/
structure MmaFullFacts (L : Launch) (mem0 : Mem0) : Prop where
  ub : ∀ Y, Consistent L kernel Prod mem0 Y → ¬ HasUb Y
  thread : ∀ Y, Consistent L kernel Prod mem0 Y → ThreadFacts L Y
  inputFull : ∀ Y, Consistent L kernel Prod mem0 Y → InputFullBlocked L Y
  agree : ∀ Y, Consistent L kernel Prod mem0 Y → AllResponsesAgree L Y
  clusterAll : ∀ Y, Consistent L kernel Prod mem0 Y → ClusterExitAll L Y

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The thread's state after a trace that is not empty. -/
theorem trace_ne_nil_of_mma {g : Nat} {mm : Mma.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma mm)))) : X.tr g ≠
      [] := by
  intro h
  simp only [Frame.stateAt, h, List.length_nil, List.take_zero] at hσ
  cases hσ

/-- **Progress at an MMA thread's full wait.** A pending MMA thread at a slot's full wait, whose
last event is released, extends a maximal execution or passes to an obligation of smaller rank. -/
theorem mma_full_steps (hpre : Pre P L mem0) (hM : MmaFullFacts L mem0)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {mm : Mma.D} {s : Fin 4}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma mm))))
    (hs : mm.site = .full s) (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0
      (Descent.Obl L) (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have ht := hM.thread X hX
  have hub := hM.ub X hX
  have hne := trace_ne_nil_of_mma hσ
  have hblock := hpre.block
  have hgrid : g / L.block < L.grid := by
    have : g < L.grid * L.block := hg
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    exact this
  have hw8 : 8 ≤ g % L.block / 32 := by
    have := ht.role_warp hg (le_refl _) hσ
    simp only [roleWarp] at this
    omega
  -- the barrier is initialized, so it has a state
  obtain ⟨ipc, hinit⟩ := ht.ring_init_exists (b := ⟨.input, s.val, true⟩) hg hw8 (le_refl _) hσ
    (by simp only [Bar.Valid, Ring.slots]; exact s.isLt) hgrid rfl
  have hloc : Bar.loc L (g / L.block) ⟨.input, s.val, true⟩ = mmaFullLoc L g s := by
    simp only [mmaFullLoc, Bar.loc, Bar.off, Nat.add_assoc]
  rw [hloc] at hinit
  obtain ⟨i0, r, hr, -, hra, -, -⟩ := init_record_of_actual_get hX hinit
  obtain ⟨before, hstate⟩ := stateBefore_length_some (hX.tma.2.2.1 (mmaFullLoc L g s)).1
      (objects_noInval hX ht (mmaFullLoc L g s))
    (List.mem_of_getElem? hr) hra (by simp only [Bar.count]; decide)
  -- the rank of the thread
  have hrank : rank L X (.thread g) = ringAt (mmaCount L g (X.tr g)) + 10 := by
    rw [rank_released hrel, threadTime_of hσ (by simp [ThreadD.exitOff, Mma.exitOff, hs])]
    simp [ThreadD.vtime, Mma.vtime, hs]
  refine Descent.mbar_wait_steps prod_wfFree hub hmax hp hrel hne
    (fun t hrun ok => ht.mma_poll hg hσ hs hrun ok) hstate fun sc hafter hready hYmax => ?_
  set Y := Step.failedPoll X g mm.site.pc (mm.fp % 2) (mmaFullLoc L g s) true sc before with hY
  have htrY : Y.tr g = X.tr g ++ [⟨mm.site.pc,
      .wait (mmaFullLoc L g s) (mm.fp % 2) false true sc⟩] := by
    rw [hY, Step.failedPoll_tr]; simp
  have hσY : Frame.stateAt (code L) Y g (Y.tr g).length = some (some (.inr (.mma mm))) := by
    simp only [Frame.stateAt, List.take_length]
    rw [htrY]
    exact hafter
  have hσpY : Frame.stateAt (code L) Y g ((Y.tr g).length - 1) = some (some (.inr (.mma mm))) := by
    simp only [Frame.stateAt]
    rw [htrY, List.length_append, List.length_singleton, Nat.add_sub_cancel,
      List.take_left' rfl]
    simpa [Frame.stateAt] using hσ
  have hlastY : (Y.tr g).getLast? = some ⟨mm.site.pc,
      .wait (mmaFullLoc L g s) (mm.fp % 2) false true sc⟩ := by
    rw [htrY]; simp
  have hstateY : stateBefore (Y.objects (mmaFullLoc L g s))
      (Y.objects (mmaFullLoc L g s)).length = some before := by
    rw [hY, Step.failedPoll_objects]
    simp only [ite_true, List.length_append, List.length_singleton]
    simp [stateBefore, Step.failedRecord]
  have hready' : before.phase % 2 = mm.fp % 2 := by simpa [Nat.mod_mod] using hready
  have hYX : Consistent L kernel Prod mem0 Y := hYmax.1
  obtain ⟨o', hobl, hlt⟩ := mma_full_blocked_of hpre (hM.thread Y hYX) (hM.ub Y hYX)
    (hM.inputFull Y hYX) (hM.agree Y hYX) (hM.clusterAll Y hYX) hg hσY hσpY hs hlastY hstateY
    hready'
  have hK : mmaCount L g (Y.tr g) = mmaCount L g (X.tr g) := by
    rw [htrY]
    simp [mmaCount, List.countP_append, commitsTo]
  refine ⟨o', hobl, ?_⟩
  rw [hrank, ← hK]
  exact hlt

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
