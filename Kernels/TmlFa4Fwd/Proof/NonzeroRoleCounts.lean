-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixBound
public import Kernels.TmlFa4Fwd.Proof.MmaWholePrefix
public import Kernels.TmlFa4Fwd.Proof.NonzeroTraceBound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

/-- The MMA warp's entire actual trace, including startup and return, is uniformly bounded. -/
theorem mmaLaneTraceBound {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g : Nat}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hg : g < l.threads) (hw : warpIndex l g = 12) :
    (X.tr g).countP Event.counts ≤ 256 * 2 ^ 32 + 128 * (p.batch + 1) + 1371 := by
  have hb := nonzeroTraceBound (n := 256 * 2 ^ 32 + 128 * (p.batch + 1) + 1366)
    hp hX hg (by rw [hw]; decide) (by
      intro s es vs hs _ hWalk
      have hregs := hs.2.2.2.2
      have hW : s.regs 1062 = some (b32 12) := by rw [← hw]; exact hregs.1
      have hBase := hregs.2.1
      have hOffset := holds_mem hregs (by simp [nonzeroBarrierFacts] :
        (6495, b32 (l.sharedBase + 144)) ∈ nonzeroBarrierFacts p l g)
      have hQ0 := holds_mem hregs (by simp [nonzeroBarrierFacts, abiFacts] :
        (7502, b64 p.cuQBase) ∈ nonzeroBarrierFacts p l g)
      have hQ1 := holds_mem hregs (by simp [nonzeroBarrierFacts, abiFacts] :
        (7506, b64 p.cuQBase) ∈ nonzeroBarrierFacts p l g)
      have hK := holds_mem hregs (by simp [nonzeroBarrierFacts, abiFacts] :
        (7503, b64 p.usedKBase) ∈ nonzeroBarrierFacts p l g)
      exact Mma.mmaWholePrefixFromDispatch hp hg hWalk
        (hs.mono ⟨hW, hBase, hOffset, hQ0, hQ1, hK, trivial⟩))
  exact hb

/-- The output warp's trace budget includes both request scans, polling, and its exit. -/
theorem epilogueLaneTraceBound {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g : Nat}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hg : g < l.threads) (hw : warpIndex l g = 13) :
    (X.tr g).countP Event.counts ≤ 128 * (p.batch + 1) + 1006 := by
  have hb := nonzeroTraceBound (n := 128 * (p.batch + 1) + 1001)
    hp hX hg (by rw [hw]; decide) (by
      intro s es vs hs _ hWalk
      have hW : s.regs 1062 = some (b32 13) := by rw [← hw]; exact hs.2.2.2.2.1
      exact Epilogue.epilogueRolePrefixFromDispatch hp hg hWalk
        (hs.mono ⟨hW, hs.2.2.2.2.2.1, trivial⟩))
  exact hb

end
end PTX.Kernels.TmlFa4Fwd
