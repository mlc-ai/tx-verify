-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaLoopRank
public import Kernels.TmlFa4Fwd.Proof.MmaRoleCut
public import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof PTX.EventFrame Mma

noncomputable section

/-- A finite straight local path either stops inside the path or yields its exact continuation. -/
theorem cutWalkFallthrough {l : Launch} {g lo hi cutoff : Nat} {s : TState} {events : List Event}
    {visits : List Visit} (hw : Walk kernel Assumptions.all l g s events visits)
    (hLo : lo ≤ s.pc) (hHi : s.pc ≤ hi)
    (hStep : ∀ {t u : TState} {e : Option Event}, lo ≤ t.pc → t.pc < hi →
      WStep kernel Assumptions.all l g t e u →
      e = none ∧ Tau kernel Assumptions.all l g t u ∧ u.pc = t.pc + 1) :
    countedUntil cutoff visits ≤ 1 ∨
      ∃ u tail, run kernel Assumptions.all l g (hi - s.pc) s = some u ∧ u.pc = hi ∧
        Walk kernel Assumptions.all l g u events tail ∧
        countedUntil cutoff visits ≤ countedUntil cutoff tail := by
  induction hw with
  | stop => exact .inl (by simp [countedUntil])
  | @tau s u es vs ht hw ih =>
    by_cases hEq : s.pc = hi
    · exact .inr ⟨s, _, by simp [hEq, run], hEq, .tau ht hw, le_rfl⟩
    · have hx := hStep hLo (by omega) (e := none) (.inl ⟨rfl, ht⟩)
      have hPc := hx.2.2
      have hCount : countedUntil cutoff (visit kernel l g s none :: vs) ≤
          countedUntil cutoff vs := by
        by_cases hP : s.pc < cutoff
        · simp [countedUntil, visit_pc, List.filterMap_cons, visit_ev, hP]
        · simp [countedUntil, visit_pc, hP]
      rcases ih (by omega) (by omega) with hb | ⟨v, tail, hr, hv, hW, hq⟩
      · exact .inl (hCount.trans hb)
      · have hOne : run kernel Assumptions.all l g 1 s = some u := by
          simp [run, tauStep_iff.mpr ht]
        have hN : hi - s.pc = 1 + (hi - u.pc) := by omega
        exact .inr ⟨v, tail, hN ▸ run_comp hOne hr, hv, hW, hCount.trans hq⟩
  | @ev s u e es vs he hw ih =>
    by_cases hEq : s.pc = hi
    · exact .inr ⟨s, _, by simp [hEq, run], hEq, .ev he hw, le_rfl⟩
    · have hn : some e = none := (hStep hLo (by omega) (.inr ⟨e, rfl, he⟩)).1
      cases hn
  | @last s e he =>
    apply Or.inl
    by_cases hP : s.pc < cutoff
    · simpa [countedUntil, visit_pc, visit_ev, hP] using
        (List.countP_le_length (p := Event.counts) (l := [e]))
    · simp [countedUntil, visit_pc, hP]

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
