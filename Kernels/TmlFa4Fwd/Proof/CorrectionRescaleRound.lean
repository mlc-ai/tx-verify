-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleControl
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleSignal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The x16 path has eight three-event chunks and a final store wait. -/
def rescaleBodyEvents (word : BitVec 32) : Nat := if word = 0 then 0 else 25

/-- Either branch of the ballot leads to the two actual release arrivals for the stage.
The taken branch includes every scaled chunk and the store wait before either arrival. -/
theorem observeRescaleBodyOfWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} {F : List (Nat × Value)} (hp : Pre p l m)
    (stage : Fin 2) (word : BitVec 32) (old : Fin 8 → Nat → ℝ)
    (coefficient : Value) (alpha : ℝ)
    (hFactor : Thread.Correction.RescaleFactorWord coefficient alpha)
    (ht : At t (if word = 0 then rescaleSkipPc stage else rescaleLoadPc stage 0)
      ((statsReg stage .alpha, coefficient) :: F))
    (hAddr : Holds t.regs (rescaleStageAddresses l g stage))
    (hCredit : (outputCreditReg stage, b32 (creditLoc l g stage).addr) ∈ F)
    (hReuse : (rescaleReuseReg stage, b32 (rescaleReuseLoc l g stage).addr) ∈ F)
    (hFrame : ∀ chunk : Fin 8, ∀ r ∈ F.map Prod.fst, r ∉ rescaleDataRegs stage chunk ∧
      rescaleLocalKeeps stage chunk r)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ rescaleCountReg stage ∧
      pair.1 ≠ rescaleSignalDst stage ∧ pair.1 ≠ rescaleSignalDst stage + 1)
    (hRead : word ≠ 0 → ∀ (chunk : Fin 8) vals, X.get (g, pos + 3 * chunk.val) =
      some ⟨rescaleLoadPc stage chunk,
        .tc (.ld (outputAddress l g stage (16 * chunk.val)) vals .s32x32b)⟩ →
      vals = List.ofFn (fun i : Fin 16 => fl (old chunk i.val)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u,
      (word ≠ 0 →
        (∀ chunk : Fin 8, RescaleChunkEffects l X g (pos + 3 * chunk.val)
          stage chunk (old chunk) alpha) ∧
        X.get (g, pos + 24) = some ⟨rescaleStorePc stage 7 + 1, .tc .waitSt⟩) ∧
      X.get (g, pos + rescaleBodyEvents word) = some ⟨rescaleSignalPc stage + 1,
        .arrive (creditLoc l g stage) 0 1 true .cta⟩ ∧
      X.get (g, pos + rescaleBodyEvents word + 1) = some ⟨rescaleSignalPc stage + 2,
        .arrive (rescaleReuseLoc l g stage) 0 1 true .cta⟩ ∧
      At u (rescaleSignalPc stage + 3) F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + rescaleBodyEvents word + 2)) none := by
  have hSignal {s : TState} {offset : Nat}
      (hs : At s (rescaleSignalPc stage) F)
      (hS : Run kernel Assumptions.all l g s ((X.tr g).drop (pos + offset)) none) :=
    observeRescaleSignals hp stage
      (hs.mono ⟨holds_mem hs.2.2.2.2 hCredit, holds_mem hs.2.2.2.2 hReuse, hs.2.2.2.2⟩)
      hFresh hS
  by_cases hw : word = 0
  · have hPc : rescaleSkipPc stage = rescaleSignalPc stage := by fin_cases stage <;> decide
    have hs : At t (rescaleSignalPc stage) F := by
      rw [← hPc]
      exact (ite_eq_left hw ▸ ht).mono ht.2.2.2.2.2
    have hr' : Run kernel Assumptions.all l g t ((X.tr g).drop (pos + 0)) none := by
      simpa only [Nat.add_zero] using hr
    obtain ⟨u, hu, hc, he, hTail⟩ := hSignal hs hr'
    exact ⟨u, fun h => (h hw).elim, by simpa only [rescaleBodyEvents, ite_eq_left hw] using hc,
      by simpa only [rescaleBodyEvents, ite_eq_left hw] using he, hu,
      by simpa only [rescaleBodyEvents, ite_eq_left hw] using hTail⟩
  · have hAt : At t (rescaleLoadPc stage 0) (rescaleStageAddresses l g stage ++ F) :=
      (ite_eq_right hw ▸ ht).mono ((holds_append _ _ _).2 ⟨hAddr, ht.2.2.2.2.2⟩)
    have hLow : valFloat .f32 (splitValue 64 (joinValue coefficient coefficient)).1 =
        .ok alpha := by rw [hFactor.unpack]; exact hFactor.value
    have hHigh : valFloat .f32 (splitValue 64 (joinValue coefficient coefficient)).2 =
        .ok alpha := by rw [hFactor.unpack]; exact hFactor.value
    obtain ⟨s, hChunks, hWait, hs, hS⟩ := observeRescaleStage hp stage old coefficient alpha hAt
      hFrame ht.2.2.2.2.1 hFactor.width hLow hHigh (hRead hw) hr
    have hs' : At s (rescaleSignalPc stage) F :=
      hs.mono ((holds_append _ _ _).1 hs.2.2.2.2.2).2
    obtain ⟨u, hu, hc, he, hTail⟩ := hSignal hs' hS
    exact ⟨u, fun _ => ⟨hChunks, hWait⟩,
      by simpa only [rescaleBodyEvents, ite_eq_right hw] using hc,
      by simpa only [rescaleBodyEvents, ite_eq_right hw] using he, hu,
      by simpa only [rescaleBodyEvents, ite_eq_right hw] using hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
