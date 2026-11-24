-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionReadySources
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalPollEntry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

def normalizingReciprocal (sum : ℝ) : ℝ := 1 / (if sum = 0 then 1 else sum)

def finalStageReciprocalFacts (stage : Fin 2) (sum maximum : ℝ)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  (reciprocalReg stage, fl (normalizingReciprocal sum)) ::
    (reciprocalPred stage, .pred (decide (sum ≠ 0))) :: finalStatsFacts stage sum maximum F

def finalStagePollFacts (l : Launch) (stage : Fin 2) (sum maximum : ℝ)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  (finalPollPrepReg stage, finalPollPrepWord l stage) ::
    finalStageReciprocalFacts stage sum maximum F

def finalStageLoadFacts (l : Launch) (stage : Fin 2) (sum maximum : ℝ)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  let r := fl (normalizingReciprocal sum)
  (finalizeReciprocalPair stage, .pair r r) :: finalStagePollFacts l stage sum maximum F

/-- The static register and footprint facts for an actual finalization stage. -/
structure FinalStageFrame (l : Launch) (g : Nat) (stage : Fin 2) (sum maximum : ℝ)
    (F : List (Nat × Value)) : Prop where
  barrier : (statsBarrierReg stage, b32 (statsBarrierId l g stage)) ∈ F
  statistics : (1627, b32 (l.sharedBase + 4 * rowOf l g)) ∈ F
  count : (6498, b32 1) ∈ F
  release : (rescaleReuseReg (1 - stage), b32 (rescaleReuseLoc l g (1 - stage)).addr) ∈ F
  shared : (2535, b32 l.sharedBase) ∈ F
  statisticsFresh : ∀ rv ∈ F, rv.1 ≠ statsReg stage .sum ∧ rv.1 ≠ statsReg stage .maximum ∧
    rv.1 ≠ finalStatsReleaseDst stage ∧
    rv.1 ∉ [reciprocalPred stage, reciprocalInput stage, reciprocalReg stage]
  prepFresh : ∀ rv ∈ finalStageReciprocalFacts stage sum maximum F,
    rv.1 ≠ finalPollPrepReg stage
  pollFresh : ∀ rv ∈ finalStagePollFacts l stage sum maximum F,
    (∀ free, rv.1 ≠ finalizePollPred stage free) ∧ rv.1 ≠ finalizeReciprocalPair stage
  pollBase : ∀ free, (finalizePollBase stage free, b32 (finalizePollLoc l g stage free).addr) ∈
    finalStagePollFacts l stage sum maximum F
  pollPhase : ∀ free, (finalizePollPhase free, b32 free.toNat) ∈
    finalStagePollFacts l stage sum maximum F
  vectorZero : finalizeVectorFact l g stage 0 ∈ F
  signals : ∀ rv ∈ outputSignalFacts l g stage, rv ∈ F
  surface : FinalizeSurfaceRegisters l g stage (normalizingReciprocal sum)
    (outputSignalFacts l g stage ++ finalStageLoadFacts l stage sum maximum F)
  outputFresh : ∀ rv ∈ finalStageLoadFacts l stage sum maximum F,
    rv.1 ≠ outputCreditDst stage ∧ rv.1 ≠ outputCreditDst stage + 1

/-- The shared statistics and TMEM values supplied by the producer on this execution. -/
structure FinalStageInputs (l : Launch) (X : Execution) (g pos : Nat) (stage : Fin 2)
    (sum maximum : ℝ) (old : Fin 16 → Nat → ℝ) : Prop where
  sumRead : ∀ bs, X.get (g, pos + 1) = some
    ⟨statsPc stage .sum, .rd {loc := statsLoc l g stage .sum, size := 4} bs⟩ →
    bs = (fl sum).toBytes.map some
  maxRead : ∀ bs, X.get (g, pos + 2) = some
    ⟨statsPc stage .maximum, .rd {loc := statsLoc l g stage .maximum, size := 4} bs⟩ →
    bs = (fl maximum).toBytes.map some
  outputRead : ∀ n k,
    X.get (g, pos + 4 + n) = some ⟨finalizePollPc stage false,
      .wait (finalizePollLoc l g stage false) 0 true true .cta⟩ →
    X.get (g, pos + 4 + n + 1 + k) = some ⟨finalizePollPc stage true,
      .wait (finalizePollLoc l g stage true) 1 true true .cta⟩ →
    ∀ (chunk : Fin 16) vals, X.get (g, pos + 4 + n + 1 + k + 1 + 10 * chunk.val) = some
      ⟨finalizeLoadPc stage chunk,
        .tc (.ld (outputAddress l g stage (8 * chunk.val)) vals .s32x32b)⟩ →
      vals = List.ofFn (fun i : Fin 8 => fl (old chunk i.val))

private theorem frameHolds {R : Nat → Option Value} :
    ∀ {F : List (Nat × Value)}, (∀ rv ∈ F, R rv.1 = some rv.2) → Holds R F
  | [], _ => trivial
  | r :: _rest, h => ⟨h r List.mem_cons_self, frameHolds
    (fun r hr => h r (List.mem_cons_of_mem _ hr))⟩

/-- The final statistics synchronization, acquire spins, normalization and ready arrival
belong to one actual lane execution. The resulting cursor retains the final statistics. -/
theorem observeFinalStage {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g pos : Nat} {t : TState} {F : List (Nat × Value)}
    (stage : Fin 2) (sum maximum : ℝ) (old : Fin 16 → Nat → ℝ)
    (ht : At t (statsBarrierPc stage false) F)
    (hFrame : FinalStageFrame l g stage sum maximum F)
    (hInputs : FinalStageInputs l X g pos stage sum maximum old)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ start u, pos + 6 ≤ start ∧
      NormalizedOutput l X g start stage old (normalizingReciprocal sum) ∧
      At u (outputFencePc stage + 3) (finalStageLoadFacts l stage sum maximum F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (start + 163)) none := by
  obtain ⟨s, _, _, _, _, hs, hS⟩ := observeFinalStatsWithPredicate hp stage sum maximum ht
    hFrame.barrier hFrame.statistics hFrame.count hFrame.release hFrame.statisticsFresh
    hInputs.sumRead hInputs.maxRead hr
  have hs' : At s (reciprocalPc stage + 3) (finalStageReciprocalFacts stage sum maximum F) := hs
  obtain ⟨v, hv, hV⟩ := finalPollPrep hp stage hs'
    (holds_mem hs.2.2.2.2.2.2.2.2 hFrame.shared) hFrame.prepFresh
  have hV' : At v (finalizePollPc stage false) (finalStagePollFacts l stage sum maximum F) := hV
  obtain ⟨n, k, w, hn, hk, hw, hW⟩ := observeFinalPollEntry hp stage
    (normalizingReciprocal sum) hV' hFrame.pollFresh hFrame.pollBase hFrame.pollPhase
    (List.mem_cons_of_mem _ List.mem_cons_self) (hS.after_local hv)
  let start := pos + 4 + n + 1 + k + 1
  let G := finalStageLoadFacts l stage sum maximum F
  have hAll : Holds w.regs G := hw.2.2.2.2
  have hF : Holds w.regs F := hw.2.2.2.2.2.2.2.2.2.2
  have hSignals : Holds w.regs (outputSignalFacts l g stage) :=
    frameHolds (fun rv hm => holds_mem hF (hFrame.signals rv hm))
  have hVector : Holds w.regs (finalizeVectorFrame l g stage 1) := by
    have hOne : finalizeVectorFrame l g stage 1 = [finalizeVectorFact l g stage 0] := rfl
    rw [hOne]
    exact ⟨holds_mem hF hFrame.vectorZero, trivial⟩
  have ht' : At w (finalizeLoadPc stage 0)
      (finalizeSurfaceFrame l g stage 0 (outputSignalFacts l g stage ++ G)) :=
    hw.mono ((holds_append _ _ _).2 ⟨hVector, (holds_append _ _ _).2 ⟨hSignals, hAll⟩⟩)
  obtain ⟨u, hChunks, hFence, _, hReady, hu, hU⟩ := observeNormalizedSurface
    (pos := start) hp stage old (normalizingReciprocal sum) hFrame.surface ht'
    hFrame.outputFresh (hInputs.outputRead n k hn hk) hW
  exact ⟨start, u, by dsimp only [start]; omega, ⟨hChunks, hFence, hReady⟩, hu, hU⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
