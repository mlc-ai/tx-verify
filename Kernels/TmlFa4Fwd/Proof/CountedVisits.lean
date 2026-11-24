-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaLoopRank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof Mma

noncomputable section

private theorem codeEndStops {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {s : TState} (h : K.code.length ≤ s.pc) :
    ∃ f, out K A l g s = .ev (.ub f) := by
  have hc : K.code[s.pc]? = none := List.getElem?_eq_none h
  cases hf : s.fault with
  | none => exact ⟨.pcOutOfRange, by simp [out, hf, hc]⟩
  | some f => exact ⟨f, by simp [out, hf]⟩

/-- Beyond the final decoded PC, a walk can only stop or emit one terminal fault. -/
theorem countedThroughCode {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {s : TState} {events : List Event} {visits : List Visit}
    (hw : Walk K A l g s events visits) : events.countP Event.counts ≤
      countedUntil K.code.length visits + 1 := by
  induction hw with
  | stop => simp [countedUntil]
  | @tau s u es vs ht hw ih =>
    by_cases hPc : s.pc < K.code.length
    · simpa [countedUntil, List.filterMap_cons, visit_pc, visit_ev, hPc] using ih
    · obtain ⟨_, hOut⟩ := codeEndStops (K := K) (A := A) (l := l) (g := g) (s := s) (by omega)
      exact (not_tau_of_stops ⟨_, hOut⟩ ht).elim
  | @ev s u e es vs he hw ih =>
    by_cases hPc : s.pc < K.code.length
    · have hB := Nat.add_le_add_right ih (if e.counts then 1 else 0)
      simpa [countedUntil, List.filterMap_cons, visit_pc, visit_ev, hPc, List.countP_cons,
        Nat.add_right_comm _ 1] using hB
    · obtain ⟨f, hOut⟩ := codeEndStops (K := K) (A := A) (l := l) (g := g) (s := s) (by omega)
      obtain ⟨m, hm, hf⟩ := he
      have hM : m = .ub f := Out.ev.inj (hm.symm.trans hOut)
      subst m
      cases hf.2
  | @last s e he => exact (List.countP_le_length (p := Event.counts) (l := [e])).trans (by simp)

end
end PTX.Kernels.TmlFa4Fwd
