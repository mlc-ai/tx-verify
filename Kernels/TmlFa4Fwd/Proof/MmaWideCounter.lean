-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaLoopCounter

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The all-ones starting word must make a whole circuit before the
postincrement sentinel test sees all ones again. -/
def wideCounterWord (remaining : Nat) : Value :=
  if remaining = 2 ^ 32 + 1 then b32 (2 ^ 32 - 1) else counterWord remaining

theorem wideCounterWord_surjective {word : Nat} (h : word < 2 ^ 32) :
    ∃ remaining, 2 ≤ remaining ∧ remaining ≤ 2 ^ 32 + 1 ∧ b32 word = wideCounterWord remaining := by
  by_cases hs : word = 2 ^ 32 - 1
  · exact ⟨2 ^ 32 + 1, by decide, le_rfl, by simp [wideCounterWord, hs]⟩
  · refine ⟨2 ^ 32 - word, by omega, by omega, ?_⟩
    rw [wideCounterWord, ite_eq_right (by omega), counterWord, Nat.sub_sub_self (by omega)]

private theorem counterWrap {l : Launch} {g n : Nat}
    (h : n = 2 ^ 32 ∨ n = 2 ^ 32 + 1) :
    Seg kernel [] l g 3 2530 [(7204, wideCounterWord n)] 2533
      [(399, .pred true), (7204, wideCounterWord (n - 1))] := by
  rcases h with rfl | rfl <;> intro t ht <;>
    simp only [wideCounterWord, counterWord, ↓reduceIte, Nat.sub_self,
      Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff] at ht ⊢ <;>
    seg_fp ht using rfl

/-- The loop budget decreases for any initial 32-bit counter word. -/
theorem stepWideCounter {l : Launch} {g n : Nat} (hn : 2 ≤ n) (hN : n ≤ 2 ^ 32 + 1)
    {t : TState} (ht : At t 2530 [(7204, wideCounterWord n)]) :
    ∃ u, run kernel Assumptions.all l g 4 t = some u ∧
      At u (if 2 < n then 2291 else 2534) [(7204, wideCounterWord (n - 1))] := by
  by_cases hs : n < 2 ^ 32
  · have hNe : n ≠ 2 ^ 32 + 1 := by omega
    have hNe' : n - 1 ≠ 2 ^ 32 + 1 := by omega
    rw [wideCounterWord, ite_eq_right hNe] at ht
    obtain ⟨u, hRun, hu⟩ := stepCounter (l := l) (g := g) hn hs ht
    exact ⟨u, hRun, by simpa only [wideCounterWord, ite_eq_right hNe'] using hu⟩
  · have hCase : n = 2 ^ 32 ∨ n = 2 ^ 32 + 1 := by omega
    obtain ⟨u, hu, hU⟩ := counterWrap hCase t ht
    have hCalc := localRun (by decide) (by decide) ht.1 (by
      set_option maxRecDepth 100000 in kernel_rfl) hu
    obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
      Flow.code_2533 true hU hU.2.2.2.2.1 (by simp)
    have hBr := localRun (by decide) (by decide) hU.1 rfl hv
    exact ⟨v, run_comp hCalc hBr, by
      rw [ite_eq_left (by omega)]
      exact hV.mono hV.2.2.2.2.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
