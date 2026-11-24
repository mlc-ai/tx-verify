-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

/-- Warp zero has at most 69 startup records, even when it initializes every object. -/
theorem warp0TraceBound {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g n : Nat}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hg : g < l.threads) (hWarp : warpIndex l g = 0)
    (hRole : ∀ {s : TState} {events : List Event} {visits : List Visit},
      At s 174 (initFacts l 16) → Walk kernel Assumptions.all l g s events visits →
        events.countP Event.counts ≤ n) :
    (X.tr g).countP Event.counts ≤ n + 69 := by
  by_cases hLen : 69 ≤ (X.tr g).length
  · obtain ⟨k, s, _, hK, hs, _, hr⟩ := warp0CommonPrefix hp hX hg hWarp hLen
    obtain ⟨_, hWalk⟩ := Mma.walkFromRun hr
    have hTail := hRole hs hWalk
    have hPrefix : ((X.tr g).take k).countP Event.counts ≤ 69 :=
      (List.countP_le_length ..).trans ((List.length_take_le ..).trans hK)
    have hEq := congrArg (List.countP Event.counts) (List.take_append_drop k (X.tr g))
    rw [List.countP_append] at hEq
    omega
  · exact (List.countP_le_length ..).trans (by omega)

end
end PTX.Kernels.TmlFa4Fwd
