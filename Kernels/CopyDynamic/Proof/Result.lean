-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyDynamic.Proof.Values

@[expose] public section

/-! # `ResultGoal`

In a complete execution every thread `j < N` has exited, so it has written `B[j]`
(`ThreadFacts.exit_write`) with the value its read returned, `x j` (`read_value`); it is the only
write of `B[j]` (`covers_B_B`), so the final memory holds `x j` there (`IsFinal.unique`). Every
other byte has no writer and keeps its launch content (`IsFinal.unwritten`). -/

namespace PTX.Kernels.CopyDynamic.Proof
open PTX

noncomputable section

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0} {X : Execution}

/-- In a complete execution thread `j < N` has written `x j` to `B[j]`. -/
theorem written (hpre : Pre L A B N x mem0) (hX : Consistent L kernel [] mem0 X)
    (ht : ThreadFacts L A B N X) (hc : Complete L X) {j : Nat} (hj : j < L.threads)
    (hjN : j < N) : X.MemWrites (.thread (j, 1)) (accB B j) (x j).toBytes := by
  obtain ⟨pc, hlast⟩ :=
    ((noTma_of_consistent noTma hX).complete_iff L hX.clc).mp hc j hj
  have he : X.get (j, (X.tr j).length - 1) = some ⟨pc, .exit⟩ := by
    change (X.tr j)[(X.tr j).length - 1]? = _
    rw [← List.getLast?_eq_getElem?, hlast]
  obtain ⟨pc', a, bs, hw⟩ := ht.exit_write he hjN
  obtain ⟨-, -, rfl, rb, v, v', h0, hv, hsv, hbs⟩ := ht.writes hw
  obtain ⟨hv', hb4⟩ := read_value hpre hX ht h0
  rw [hv] at hv'
  cases hv'
  rw [storeValue_of_bytes (by simpa using hb4)] at hsv
  cases hsv
  rw [hbs] at hw
  exact Or.inl ⟨pc', hw⟩

/-- **A complete execution leaves `Post`.** -/
theorem result_goal (hpre : Pre L A B N x mem0)
    (hT : ∀ X, Consistent L kernel [] mem0 X → ThreadFacts L A B N X) :
    ResultGoal kernel [] L mem0 (Post L B N x mem0) := by
  intro X m hX hc hfin l
  have ht := hT X hX
  split_ifs with hl
  · obtain ⟨h1, h2, h3, h4⟩ := hl
    have hjT : (l.addr - B) / 4 < L.threads := by have := Nat.min_le_right N L.threads; omega
    have hjN : (l.addr - B) / 4 < N := by have := Nat.min_le_left N L.threads; omega
    have hcov : (accB B ((l.addr - B) / 4)).Covers l := by
      simp only [Acc.Covers, Loc.InRange, accB]
      exact ⟨h1, h2, by omega, by omega⟩
    rw [hfin.unique (written hpre hX ht hc hjT hjN) hcov fun w' a' bs' hw' hc' => by
      obtain ⟨g', rfl, -, rfl, -⟩ := write_B hX ht hw'
      rw [covers_B_B hc' hcov]]
    have hat := hpre.atom _ hjN
    have hk : (l.addr - B) % 4 < 4 := Nat.mod_lt _ (by decide)
    have hidx : l.addr - (B + 4 * ((l.addr - B) / 4)) = (l.addr - B) % 4 := by omega
    simp only [wbyte, accB, hidx]
    simp [Value.toBytes, hat.1, List.getElem?_range hk, hat.2 _ hk]
  · apply hfin.unwritten
    intro w a bs hw hcov
    obtain ⟨g, rfl, hgN, rfl, -⟩ := write_B hX ht hw
    rcases hw with ⟨pc, hget⟩ | ⟨old, hrmw⟩
    · have hgT : g < L.threads := Frame.lt_of_get hX hget
      apply hl
      simp only [Acc.Covers, Loc.InRange, accB] at hcov
      obtain ⟨c1, c2, c3, c4⟩ := hcov
      have := Nat.le_min.mpr ⟨Nat.succ_le_of_lt hgN, Nat.succ_le_of_lt hgT⟩
      exact ⟨c1, c2, by omega, by omega⟩
    · exact absurd hrmw (no_rmw ht)

end

end PTX.Kernels.CopyDynamic.Proof
