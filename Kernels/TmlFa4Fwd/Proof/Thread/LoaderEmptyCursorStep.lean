-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyCycle
public import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part020
import Kernels.TmlFa4Fwd.Flow.Code.Part025
import Kernels.TmlFa4Fwd.Flow.Code.Part027

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvEmptyPhase loaderPhaseWord loaderNextPhase
  loaderNextRingFacts loaderRingWordsOfUse recurringStageInputs recurringEmptyWait reuseArrival
  loaderLinear)

noncomputable section

/-- The live stage and parity operands of a recurring packet. -/
def reuseCursorWords (site : Fin 4) (use : Nat) : List (Nat × Value) :=
  [((recurringStageInputs site).1, b32 (kvUseStage use).val),
   ((recurringEmptyWait site).phase, loaderPhaseWord (kvEmptyPhase use))]

/-- K's arithmetic lands in V's temporary words, while V reestablishes the ordinary cursor. -/
def reuseCursorSuccessor : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2

private theorem cursorAdvanceWords (site : Fin 4) (use : Nat) :
    [((recurringStageInputs (reuseCursorSuccessor site)).1,
      b32 (((kvUseStage use).val + 1) % 3)),
     ((recurringEmptyWait (reuseCursorSuccessor site)).phase,
      loaderPhaseWord (loaderNextPhase (kvUseStage use) (kvEmptyPhase use)))] =
      reuseCursorWords (reuseCursorSuccessor site) (use + 1) := by
  have h := loaderRingWordsOfUse use
  exact congrArg (fun words : List (Nat × Value) =>
    [((recurringStageInputs (reuseCursorSuccessor site)).1, (words[0]?.map Prod.snd).getD (b32 0)),
     ((recurringEmptyWait (reuseCursorSuccessor site)).phase,
       (words[1]?.map Prod.snd).getD (b32 0))]) h

/-- After an actual publication, five local steps advance the cursor by one ring use.
This covers both K-to-V transitions and both V-to-next-packet transitions. -/
theorem advanceEmptyCursor {l : Launch} {g : Nat} (site : Fin 4) (use : Nat) :
    Seg kernel Assumptions.all l g 5 (reuseArrival site + 1) (reuseCursorWords site use)
      (reuseArrival site + 6) (reuseCursorWords (reuseCursorSuccessor site) (use + 1)) := by
  rw [← cursorAdvanceWords site use]
  let stage := kvUseStage use
  let phase := kvEmptyPhase use
  have hCore :
      Seg kernel [] l g 5 (reuseArrival site + 1)
        [((recurringStageInputs site).1, b32 stage.val),
         ((recurringEmptyWait site).phase, loaderPhaseWord phase)] (reuseArrival site + 6)
        [((recurringStageInputs (reuseCursorSuccessor site)).1, b32 ((stage.val + 1) % 3)),
         ((recurringEmptyWait (reuseCursorSuccessor site)).phase,
          loaderPhaseWord (loaderNextPhase stage phase))] := by
    generalize hStage : stage = s
    generalize hPhase : phase = p
    clear hStage hPhase stage phase use
    fin_cases site <;> fin_cases s <;> cases p <;> intro t ht <;>
      simp only [reuseArrival, Loader.recurringPacketSite, Loader.copyCommitPc,
        reuseCursorSuccessor, recurringStageInputs, recurringEmptyWait,
        loaderPhaseWord, loaderNextPhase] at ht ⊢ <;>
      seg_fp ht using decide
  have hLo : 174 ≤ reuseArrival site + 1 := by fin_cases site <;> decide
  have hHi : reuseArrival site + 1 + 5 ≤ 1906 := by fin_cases site <;> decide
  have hSeq : ((kernel.code.drop (reuseArrival site + 1)).take 4).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  intro t ht
  obtain ⟨u, hRun, hAt⟩ := hCore t ht
  exact ⟨u, (loaderLinear (regs := []) hLo hHi ht.1 (by simp) hSeq hRun).1, hAt⟩

/-- The two decoded entry blocks that initialize the ring cursor. -/
def cursorSeedPc : Fin 2 → Nat
  | 0 => 909
  | 1 => 914

/-- Both decoded seed blocks set the first recurring use to slot two and free parity. -/
theorem seedEmptyCursor {l : Launch} {g : Nat} (seed : Fin 2) :
    Seg kernel Assumptions.all l g 2 (cursorSeedPc seed) [] (cursorSeedPc seed + 2)
      (reuseCursorWords 0 2) := by
  have hCore :
      Seg kernel [] l g 2 (cursorSeedPc seed) [] (cursorSeedPc seed + 2)
        [(7179, b32 2), (7180, b32 1)] := by
    fin_cases seed <;> intro t ht <;> simp only [cursorSeedPc] at ht ⊢ <;>
      seg_fp ht using decide
  have hLo : 174 ≤ cursorSeedPc seed := by fin_cases seed <;> decide
  have hHi : cursorSeedPc seed + 2 ≤ 1906 := by fin_cases seed <;> decide
  have hSeq : ((kernel.code.drop (cursorSeedPc seed)).take 1).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    fin_cases seed <;> (set_option maxRecDepth 100000 in kernel_rfl)
  intro t ht
  obtain ⟨u, hRun, hAt⟩ := hCore t ht
  exact ⟨u, (loaderLinear (regs := []) hLo hHi ht.1 (by simp) hSeq hRun).1, hAt⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
