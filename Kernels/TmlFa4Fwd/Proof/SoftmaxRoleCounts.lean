-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.NonzeroTraceBound
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRolePrefix
public import Kernels.TmlFa4Fwd.Proof.Warp0TraceBound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

/-- All eight softmax warps include their actual startup cost, even the initializing warp. -/
theorem softmaxLaneTraceBound {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g : Nat}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hg : g < l.threads) (hw : warpIndex l g < 8) :
    (X.tr g).countP Event.counts ≤ Softmax.softmaxRoleBudget p + 70 := by
  let warp : Fin 8 := ⟨warpIndex l g, hw⟩
  by_cases hz : warpIndex l g = 0
  · have hb := warp0TraceBound (n := Softmax.softmaxRoleBudget p + 1) hp hX hg hz (by
      intro s es vs hs hWalk
      have hWarp : s.regs 1062 = some (b32 warp.val) := by
        change s.regs 1062 = some (b32 (warpIndex l g))
        rw [hz]
        exact hs.2.2.2.2.1
      have hShared := holds_mem hs.2.2.2.2
        (show (2535, b32 l.sharedBase) ∈ initFacts l 16 from by simp [initFacts, initAddresses])
      exact Softmax.softmaxRolePrefixBound hp hg warp hWalk
        (hs.mono ⟨hWarp, hShared, trivial⟩))
    exact hb
  · have hb := nonzeroTraceBound (n := Softmax.softmaxRoleBudget p + 1) hp hX hg (by omega) (by
      intro s es vs hs _ hWalk
      exact Softmax.softmaxRolePrefixBound hp hg warp hWalk
        (hs.mono ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, trivial⟩))
    omega

end
end PTX.Kernels.TmlFa4Fwd
