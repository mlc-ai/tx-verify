-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionSearchPrefix
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescalePrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof Mma

noncomputable section

def correctionTileBudget : Nat := 2194 * 2 ^ 32 + 3849

/-- From the first request selection's continuation, either finish within the tile
budget or reach the second request search with its actual residual walk. -/
theorem cutCorrectionTilePrefix {l : Launch} {g cutoff : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hp : s.pc = 7864) (hSub : s.sub ≤ 3) (hCut : cutoff = 9083 ∨ cutoff = 9206)
    (hw : Walk kernel Assumptions.all l g s events visits) :
    countedUntil cutoff visits ≤ correctionTileBudget ∨
    ∃ u rest tail, u.pc = 9083 ∧ u.fault = none ∧ u.sub ≤ 3 ∧
      Walk kernel Assumptions.all l g u rest tail ∧
      countedUntil cutoff visits ≤ correctionTileBudget + countedUntil cutoff tail := by
  have hLower : 9083 ≤ cutoff := by omega
  have hFinalize {t : TState} {es : List Event} {ts : List Visit}
      (ht : t.pc = 8447) (hTS : t.sub ≤ 3) (hTW : Walk kernel Assumptions.all l g t es ts)
      (hN : countedUntil cutoff visits ≤ 2194 * 2 ^ 32 + 713 + countedUntil cutoff ts) :
      countedUntil cutoff visits ≤ correctionTileBudget ∨
      ∃ u rest tail, u.pc = 9083 ∧ u.fault = none ∧ u.sub ≤ 3 ∧
        Walk kernel Assumptions.all l g u rest tail ∧
        countedUntil cutoff visits ≤ correctionTileBudget + countedUntil cutoff tail := by
    rcases cutCorrectionFinalize ht hTS hLower hTW with h | ⟨u, rest, tail, hu, hf, hs, hW, hb⟩
    · exact .inl (by unfold correctionTileBudget; omega)
    · exact .inr ⟨u, rest, tail, hu, hf, hs, hW, by unfold correctionTileBudget; omega⟩
  rcases cutCorrectionLinear 1 (cutoff := cutoff) hp hSub (by change 7989 ≤ cutoff; omega) hw with
    h | ⟨a, aes, avs, ha, _, hAS, _, hAW, hAB⟩
  · have h' : countedUntil cutoff visits ≤ 629 := h
    exact .inl (by unfold correctionTileBudget; omega)
  have hAB' : countedUntil cutoff visits ≤ 629 + countedUntil cutoff avs := hAB
  have hA : a.pc = 7989 ∨ a.pc = 9201 := by simpa [correctionLinearRegion] using ha
  rcases hA with hA | hA
  · rcases cutCorrectionLinear 2 (cutoff := cutoff) hA hAS
      (by change 8005 ≤ cutoff; omega) hAW with
      h | ⟨b, bes, bvs, hb, _, hBS, _, hBW, hBB⟩
    · have h' : countedUntil cutoff avs ≤ 84 := h
      exact .inl (by unfold correctionTileBudget; omega)
    have hBB' : countedUntil cutoff avs ≤ 84 + countedUntil cutoff bvs := hBB
    have hB : b.pc = 8005 ∨ b.pc = 8447 := by simpa [correctionLinearRegion] using hb
    rcases hB with hB | hB
    · rcases cutCorrectionRescaleSeed (cutoff := cutoff) hB hBS (by omega) hBW with
        h | ⟨c, ces, cvs, hc, hCS, _, hCW, hCB⟩
      · exact .inl (by unfold correctionTileBudget; omega)
      · exact hFinalize hc hCS hCW (by omega)
    · exact hFinalize hB hBS hBW (by omega)
  · rcases hCut with hCut | hCut
    · have h := countedPastCut (by omega : ¬ a.pc < cutoff) hAW
      exact .inl (by unfold correctionTileBudget; omega)
    · rw [hCut] at hAB' ⊢
      have h := correctionExitPrefix hA hAS hAW
      exact .inl (by unfold correctionTileBudget; omega)

/-- After the last request scan, the correction exits through the terminal free-barrier poll. -/
theorem correctionPostDrainPrefix {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hp : s.pc = 9187) (hSub : s.sub ≤ 3)
    (hw : Walk kernel Assumptions.all l g s events visits) :
    countedUntil 9206 visits ≤ 89 := by
  rcases cutCorrectionLinear 8 (cutoff := 9206) hp hSub (by decide) hw with
    h | ⟨u, es, vs, he, _, hs, _, hu, hb⟩
  · have h' : countedUntil 9206 visits ≤ 74 := h
    omega
  · have hOut : u.pc = 9201 := List.mem_singleton.mp he
    have h := correctionExitPrefix hOut hs hu
    have hb' : countedUntil 9206 visits ≤ 74 + countedUntil 9206 vs := hb
    omega

end
end PTX.Kernels.TmlFa4Fwd.Correction
