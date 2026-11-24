-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.AddOne.Proof.Values

@[expose] public section

/-! # `ResultGoal`

In a complete execution every thread `j` has exited, so it has written `A[j]`
(`ThreadFacts.exit_write`) with the sum of the value its read returned: `x j` (`read_value`), so
the sum is `word (x j + 1)` (`incr_word`). It is the only write of `A[j]` (`covers_A_A`), so the
final memory holds `x j + 1` there (`IsFinal.unique`). Every other byte has no writer and keeps
its launch content (`IsFinal.unwritten`). -/

namespace PTX.Kernels.AddOne.Proof
open PTX

noncomputable section

variable {L : Launch} {A : Nat} {x : Nat → BitVec 32} {mem0 : Mem0} {X : Execution}

/-- In a complete execution thread `j` has written `x j + 1` to `A[j]`. -/
theorem written (hpre : Pre L A x mem0) (hX : Consistent L kernel [] mem0 X)
    (ht : ThreadFacts L A X) (hc : Complete L X) {j : Nat} (hj : j < L.threads) :
    X.MemWrites (.thread (j, 1)) (accA A j) (word (x j + 1)).toBytes := by
  obtain ⟨pc, hlast⟩ :=
    ((noTma_of_consistent noTma hX).complete_iff L hX.clc).mp hc j hj
  have he : X.get (j, (X.tr j).length - 1) = some ⟨pc, .exit⟩ := by
    change (X.tr j)[(X.tr j).length - 1]? = _
    rw [← List.getLast?_eq_getElem?, hlast]
  obtain ⟨pc', a, bs, hw⟩ := ht.exit_write he
  obtain ⟨-, rfl, rb, v, u, u', h0, hv, hu, hsu, hbs⟩ := ht.writes hw
  rw [read_value hpre hX ht h0] at hv
  cases hv
  rw [incr_word] at hu
  cases hu
  rw [storeValue_of_bytes (by rfl : (word (x j + 1)).bytes = 4)] at hsu
  cases hsu
  rw [hbs] at hw
  exact Or.inl ⟨pc', hw⟩

/-- **A complete execution leaves `Post`.** -/
theorem result_goal (hpre : Pre L A x mem0)
    (hT : ∀ X, Consistent L kernel [] mem0 X → ThreadFacts L A X) :
    ResultGoal kernel [] L mem0 (Post L A x mem0) := by
  intro X m hX hc hfin l
  have ht := hT X hX
  have hthr : L.threads = L.block := by simp [Launch.threads, hpre.grid]
  split_ifs with hl
  · obtain ⟨h1, h2, h3, h4⟩ := hl
    have hjT : (l.addr - A) / 4 < L.threads := by omega
    have hcov : (accA A ((l.addr - A) / 4)).Covers l := by
      simp only [Acc.Covers, Loc.InRange, accA]
      exact ⟨h1, h2, by omega, by omega⟩
    rw [hfin.unique (written hpre hX ht hc hjT) hcov fun w' a' bs' hw' hc' => by
      obtain ⟨g', rfl, rfl, -⟩ := write_A hX ht hw'
      rw [covers_A_A hc' hcov]]
    have hk : (l.addr - A) % 4 < 4 := Nat.mod_lt _ (by decide)
    have hidx : l.addr - (A + 4 * ((l.addr - A) / 4)) = (l.addr - A) % 4 := by omega
    simp only [wbyte, accA, hidx]
    simp [Value.toBytes, word, Value.bytes, Value.byteAt, List.getElem?_range hk]
  · apply hfin.unwritten
    intro w a bs hw hcov
    obtain ⟨g, rfl, rfl, -⟩ := write_A hX ht hw
    rcases hw with ⟨pc, hget⟩ | ⟨old, hrmw⟩
    · have hgT : g < L.threads := Frame.lt_of_get hX hget
      apply hl
      simp only [Acc.Covers, Loc.InRange, accA] at hcov
      obtain ⟨c1, c2, c3, c4⟩ := hcov
      exact ⟨c1, c2, by omega, by omega⟩
    · exact absurd hrmw (no_rmw ht)

end

end PTX.Kernels.AddOne.Proof
