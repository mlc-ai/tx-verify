-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

/-- The first five records of a nonzero warp are the common prologue. The bound for a role's
walk therefore gives its bound on every consistent trace, including one ending in the prologue. -/
theorem nonzeroTraceBound {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g n : Nat}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hg : g < l.threads) (hWarp : 0 < warpIndex l g)
    (hRole : ∀ {s : TState} {events : List Event} {visits : List Visit},
      At s 174 (nonzeroBarrierFacts p l g) → s.regs 1061 = some (b32 (g % l.block)) →
      Walk kernel Assumptions.all l g s events visits → events.countP Event.counts ≤ n) :
    (X.tr g).countP Event.counts ≤ n + 5 := by
  by_cases hLen : 5 ≤ (X.tr g).length
  · obtain ⟨s, _, hs, hTid, _, hRun⟩ := nonzeroCommonPrefix hp hX hg hWarp hLen
    obtain ⟨_, hWalk⟩ := Mma.walkFromRun hRun
    have hTail := hRole hs hTid hWalk
    have hPrefix : ((X.tr g).take 5).countP Event.counts ≤ 5 :=
      (List.countP_le_length ..).trans (List.length_take_le ..)
    have hEq := congrArg (List.countP Event.counts) (List.take_append_drop 5 (X.tr g))
    rw [List.countP_append] at hEq
    omega
  · exact (List.countP_le_length ..).trans (by omega)

end
end PTX.Kernels.TmlFa4Fwd
