-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionPollPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof Mma

noncomputable section

private theorem cutSingleLinear (i : Fin 10) {l : Launch} {g stop cutoff : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hp : s.pc = (correctionLinearRegion i).lo) (hSub : s.sub ≤ 3)
    (hCut : (correctionLinearRegion i).hi ≤ cutoff)
    (hExit : (correctionLinearRegion i).exits = [stop])
    (hw : Walk kernel Assumptions.all l g s events visits) :
    let site := correctionLinearRegion i
    let budget := 5 * (site.hi - site.lo) + 4
    countedUntil cutoff visits ≤ budget ∨
      ∃ u rest tail, u.pc = stop ∧ u.fault = none ∧ u.sub ≤ 3 ∧
        Walk kernel Assumptions.all l g u rest tail ∧
        countedUntil cutoff visits ≤ budget + countedUntil cutoff tail := by
  dsimp only
  rcases cutCorrectionLinear i hp hSub hCut hw with h | ⟨u, rest, tail, hPc, hf, hs, _, hw, hb⟩
  · exact .inl h
  · rw [hExit, List.mem_singleton] at hPc
    exact .inr ⟨u, rest, tail, hPc, hf, hs, hw, hb⟩

/-- The terminal wait, named barrier arrival and exit have a bounded arbitrary prefix. -/
theorem correctionExitPrefix {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} (hp : s.pc = 9201) (hSub : s.sub ≤ 3)
    (hw : Walk kernel Assumptions.all l g s events visits) : countedUntil 9206 visits ≤ 15 := by
  rcases cutCorrectionPoll 4 (cutoff := 9206) hp (by rw [hp]; decide) hw with
    h | ⟨u, es, vs, hu, _, hUS, hw, hB⟩
  · exact h.trans (by decide)
  · have hu' : u.pc = 9204 := hu
    have hL := correctionLinearBound 9 hw hu'.ge (by rw [hu']; decide) (hUS.trans hSub)
    have hN : countedUntil 9206 vs ≤ 14 := by rw [hu'] at hL; exact hL
    omega

/-- Both final normalization stages and their LSE tails have bounded arbitrary prefixes.
When they finish, the residual walk starts at the second request lookup. -/
theorem cutCorrectionFinalize {l : Launch} {g cutoff : Nat} {s : TState}
    {events : List Event} {visits : List Visit} (hp : s.pc = 8447) (hSub : s.sub ≤ 3)
    (hCut : 9083 ≤ cutoff)
    (hw : Walk kernel Assumptions.all l g s events visits) :
    countedUntil cutoff visits ≤ 3136 ∨
      ∃ u rest tail, u.pc = 9083 ∧ u.fault = none ∧ u.sub ≤ 3 ∧
        Walk kernel Assumptions.all l g u rest tail ∧
        countedUntil cutoff visits ≤ 3136 + countedUntil cutoff tail := by
  rcases cutSingleLinear 4 (cutoff := cutoff) hp hSub (by change 8473 ≤ cutoff; omega)
      (show _ = [8473] from rfl) hw with
    h | ⟨a, ea, va, ha, _, hAS, hAW, hAB⟩
  · exact .inl (h.trans (by decide))
  have hAB' : countedUntil cutoff visits ≤ 134 + countedUntil cutoff va := hAB
  rcases cutCorrectionPoll 0 (cutoff := cutoff) ha
      (by rw [ha]; omega) hAW with
    h | ⟨b, eb, vb, hb, _, hBS, hBW, hBB⟩
  · exact .inl (by omega)
  rcases cutCorrectionPoll 1 (cutoff := cutoff) hb
      (by rw [hb]; change 8476 < cutoff; omega) hBW with
    h | ⟨c, ec, vc, hc, _, hCS, hCW, hCB⟩
  · exact .inl (by omega)
  rcases cutSingleLinear 5 (cutoff := cutoff) hc (hCS.trans (hBS.trans hAS))
      (by change 8769 ≤ cutoff; omega)
      (show _ = [8769] from rfl) hCW with h | ⟨d, ed, vd, hd, _, hDS, hDW, hDB⟩
  · have h' : countedUntil cutoff vc ≤ 1454 := h
    exact .inl (by omega)
  have hDB' : countedUntil cutoff vc ≤ 1454 + countedUntil cutoff vd := hDB
  rcases cutCorrectionPoll 2 (cutoff := cutoff) hd
      (by rw [hd]; omega) hDW with
    h | ⟨e, ee, ve, he, _, hES, hEW, hEB⟩
  · exact .inl (by omega)
  rcases cutCorrectionPoll 3 (cutoff := cutoff) he
      (by rw [he]; change 8772 < cutoff; omega) hEW with
    h | ⟨f, ef, vf, hf, _, hFS, hFW, hFB⟩
  · exact .inl (by omega)
  rcases cutSingleLinear 6 (cutoff := cutoff) hf (hFS.trans (hES.trans hDS))
      (by change 9083 ≤ cutoff; omega)
      (show _ = [9083] from rfl) hFW with h | ⟨u, rest, tail, hu, hUF, hUS, hUW, hUB⟩
  · have h' : countedUntil cutoff vf ≤ 1544 := h
    exact .inl (by omega)
  have hUB' : countedUntil cutoff vf ≤ 1544 + countedUntil cutoff tail := hUB
  exact .inr ⟨u, rest, tail, hu, hUF, hUS, hUW, by omega⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
