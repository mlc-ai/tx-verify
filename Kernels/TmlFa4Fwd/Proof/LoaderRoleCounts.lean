-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.LoaderRawRing
public import Kernels.TmlFa4Fwd.Proof.LoaderRawShift
public import Kernels.TmlFa4Fwd.Proof.LoaderRawTrip
public import Kernels.TmlFa4Fwd.Proof.LoaderScanStart
public import Kernels.TmlFa4Fwd.Proof.NonzeroTraceBound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

/-- Trace budget for a loader lane. The ring caps include the raw signed trip word
and every bounded local scratch loop charged to it. -/
def loaderLaneBudget (p : Params) : Nat :=
  5720 * (16 * (p.batch + 1) + 15 + 16 + 7 * 58 + 7 * (5 * 2 ^ 31 + 8) + 19) + 8

theorem loaderLaneTraceBound {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g : Nat}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) :
    (X.tr g).countP Event.counts ≤ loaderLaneBudget p := by
  have hWarp := warpIndex_lt hp g
  let w : Fin 16 := ⟨warpIndex l g, hWarp⟩
  let j : Fin 2 := ⟨warpIndex l g - 14, by omega⟩
  have hj : 14 + j.val = w.val := by dsimp [j, w]; omega
  let budget := 5720 * (16 * (p.batch + 1) + 15 + 16 + 7 * 58 +
    7 * (5 * 2 ^ 31 + 8) + 19) + 3
  apply nonzeroTraceBound (n := budget) hp hX hg (by omega)
  intro s es vs hs hTid hWalk
  have hRegs := hs.2.2.2.2
  have hAbi : Holds s.regs (abiFacts p l) :=
    ((holds_append _ _ _).mp hRegs).2
  have hStart : At s 174 (loaderBarrierFacts p l g w.val) := by
    apply hs.mono
    unfold loaderBarrierFacts
    simp only [holds_append, holds_cons, holds_nil, and_true]
    exact ⟨⟨⟨hRegs.1, hRegs.2.1⟩, hAbi⟩, hTid⟩
  have hWork := loaderSearchBounds hp hg w hw hStart hWalk
  have hPage := holds_mem hAbi (by simp [abiFacts] : (1663, b32 16) ∈ abiFacts p l)
  have hShift := loaderRawShiftBound (hs.mono ⟨hPage, trivial⟩) hWalk
  have hWarm := loaderRingBoundFromDispatch 0 (budget := 58) (hs.mono trivial) hWalk
    (fun hRaw hAt hW => (loaderRawRingBounds hW hRaw hAt).1)
  have hSteady := loaderRingBoundFromDispatch 1 (budget := 5 * 2 ^ 31 + 8) (hs.mono trivial) hWalk
    (fun hRaw hAt hW => (loaderRawRingBounds hW hRaw hAt).2)
  change loaderVisitsAt 1352 vs ≤ 58 at hWarm
  change loaderVisitsAt 1743 vs ≤ 5 * 2 ^ 31 + 8 at hSteady
  have hBody := loaderPrefixFromOuterCycles hWalk hs.1 hs.2.1
  have hAll := loaderWholeEventCount j (hs.mono ⟨hRegs.2.1, hj.symm ▸ hRegs.1, trivial⟩) hWalk
  change es.countP Event.counts ≤
    5720 * (16 * (p.batch + 1) + 15 + 16 + 7 * 58 + 7 * (5 * 2 ^ 31 + 8) + 19) + 3
  obtain ⟨hSearch, hDrain⟩ := hWork
  clear hWalk hs hRegs hStart hTid hAbi hPage
  omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
