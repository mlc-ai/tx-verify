-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionStatsSync
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleBranch
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleChunkInputs

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The rescale stage starts with a true named rendezvous and a read of that row's alpha.
The next actual full-warp ballot sends the lane either directly to release or to the first
x16 load. The supplied alpha bytes are related to the softmax producer by its publication. -/
theorem observeRescaleControlOfWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos ordinal : Nat} {t : TState} {F : List (Nat × Value)}
    (hp : Pre p l m) (stage : Fin 2) (coefficient : Value) (alpha : ℝ)
    (hFactor : Thread.Correction.RescaleFactorWord coefficient alpha)
    (ht : At t (statsBarrierPc stage true) F)
    (hBar : t.regs (statsBarrierReg stage) = some (b32 (statsBarrierId l g stage)))
    (hAddress : t.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l g)))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ statsReg stage .alpha ∧ rv.1 ≠ rescalePredReg stage ∧
      rv.1 ≠ rescaleVoteReg stage ∧ rv.1 ≠ maskZeroReg stage)
    (hRead : ∀ bs, X.get (g, pos + 1) = some
      ⟨statsPc stage .alpha, .rd { loc := statsLoc l g stage .alpha, size := 4 } bs⟩ →
      bs = coefficient.toBytes.map some)
    (hOrdinal : ((X.tr g).take (pos + 2)).countP isFullWarpVote = ordinal)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ word u,
      X.get (g, pos) = some
        ⟨statsBarrierPc stage true, .bar (statsBarrierId l g stage) (some 64) .sync⟩ ∧
      X.get (g, pos + 1) = some ⟨statsPc stage .alpha,
        .rd { loc := statsLoc l g stage .alpha, size := 4 } (coefficient.toBytes.map some)⟩ ∧
      X.get (g, pos + 2) =
        some ⟨statsPc stage .alpha + 2, .vote (2 ^ 32 - 1) (decide (alpha < 1)) word⟩ ∧
      X.MaskK voteClass (g, pos + 2) (2 ^ 32 - 1) ordinal ∧
      At u (if word = 0 then rescaleSkipPc stage else rescaleLoadPc stage 0)
        ((statsReg stage .alpha, coefficient) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 3)) none := by
  obtain ⟨he, hAt, hTail⟩ := observeStatsBarrier hp stage true ht hBar hr
  have hRdAt : At (next t) (statsPc stage .alpha) [(1627, b32 (l.sharedBase + 4 * rowOf l g))] :=
    hAt.mono ⟨hAddress, trivial⟩
  obtain ⟨bs, hRd, hR⟩ := observeStats hp stage .alpha hRdAt hTail
  have hBytes := hRead bs hRd
  rw [hBytes] at hRd hR
  let s := next (setReg (next t) (statsReg stage .alpha) coefficient)
  have hFrame : At s (statsPc stage .alpha + 1) ((statsReg stage .alpha, coefficient) :: F) :=
    hAt.set (fun rv hm => (hFresh rv hm).1)
  have hRebuilt : rebuild 3 (coefficient.toBytes.map some) = .ok coefficient :=
    PTX.Proof.rebuild_scalar (v := coefficient) (by rw [hFactor.width]; decide) hFactor.head
  have hActual : afterLoad (next t) [statsReg stage .alpha] (coefficient.toBytes.map some) = s := by
    rw [afterLoad_ok hAt.2.1 hAt.2.2.1 hRebuilt]
    have hs := hAt.2.1
    have ha := hAt.2.2.1
    simp only [next] at hs ha
    simp [s, next, setReg, hs, ha]
  rw [hActual] at hR
  have hR' : Run kernel Assumptions.all l g s ((X.tr g).drop (pos + 2)) none := by
    simpa only [Nat.add_assoc] using hR
  obtain ⟨word, v, hVote, hOrd, hv, hRunV⟩ := observeRescaleBallot hp stage hFrame
    (fun rv hm => ⟨(hFresh rv hm).2.1, (hFresh rv hm).2.2.1⟩) hFactor.value hR' hOrdinal
  have hKeep (rv : Nat × Value) (hm : rv ∈ (statsReg stage .alpha, coefficient) :: F) :
      rv.1 ≠ maskZeroReg stage := by
    rcases List.mem_cons.mp hm with rfl | hm
    · fin_cases stage <;> dsimp only <;> decide
    · exact (hFresh rv hm).2.2.2
  obtain ⟨u, hu, hRunU⟩ := rescaleBranch stage word
    (hv.mono hv.2.2.2.2.2) hv.2.2.2.2.1 hKeep hRunV
  exact ⟨word, u, he, hRd, hVote, hOrd, hu, by simpa only [Nat.add_assoc] using hRunU⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
