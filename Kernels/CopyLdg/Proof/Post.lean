-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Proof.Values

@[expose] public section

/-! # `copy_ldg`: the final memory

`Post` from the writes of a complete execution: thread `j` below `min N threads` writes
`x j` to `B[j]`, nothing else is written, so the final memory holds `x` on
`B[0 .. min N threads)` and the launch content elsewhere. -/

namespace PTX.Kernels.CopyLdg.Proof

open PTX PTX.Proof PTX.Flow

local notation "Nc" => [Assumptions.ncInput]

noncomputable section

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0} {X : Execution}

/-- **The postcondition from the writes.** `hmem`: every write of memory is a thread's write;
`hwrite`: thread `j` has written `x j` to `B[j]` for each `j` below `min N threads`; `hfin`: the
final memory `m` of a coherence order `co` of `X` (the body of `IsFinal`). -/
theorem post_of_writes (hpre : Pre L A B N x mem0) (hX : Consistent L kernel Nc mem0 X)
    (ht : ThreadFacts L A B N X)
    (hmem : ∀ {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte}, X.MemWrites w a bs →
      ∃ i, w = .thread i ∧ X.Writes i a bs)
    (hwrite : ∀ j, j < L.threads → j < N →
      X.Writes (j, 1) { loc := gB B j, size := 4 } (x j).toBytes)
    {m : FinalMem} {co : AsyncCopy.Ref → AsyncCopy.Ref → Prop}
    (hfin : ∀ l : Loc,
      (∀ w a bs, X.MemWrites w a bs → a.Covers l →
        (∀ w' a' bs', X.MemWrites w' a' bs' → a'.Covers l → w' = w ∨ co w' w) →
        m l = some (wbyte a bs l)) ∧
      ((∀ w a bs, X.MemWrites w a bs → ¬ a.Covers l) → m l = mem0 l)) :
    Post L B N x mem0 m := by
  intro l
  obtain ⟨hw, hn⟩ := hfin l
  split_ifs with hl
  · obtain ⟨h1, h2, h3, h4⟩ := hl
    have hjT : (l.addr - B) / 4 < L.threads := by have := Nat.min_le_right N L.threads; omega
    have hjN : (l.addr - B) / 4 < N := by have := Nat.min_le_left N L.threads; omega
    have hcov : Acc.Covers { loc := gB B ((l.addr - B) / 4), size := 4 } l := by
      simp only [Acc.Covers, Loc.InRange, gB]
      exact ⟨h1, h2, by omega, by omega⟩
    rw [hw (.thread (_, 1)) _ _ (Or.inl (hwrite _ hjT hjN)) hcov (fun w' a' bs' hw' hc' => by
      obtain ⟨w', rfl, hwThread⟩ := hmem hw'
      obtain ⟨-, -, h2', rfl, -⟩ := written_value hpre hX ht hwThread
      left
      exact congrArg AsyncCopy.Ref.thread (Prod.ext (covers_gB_gB hc' hcov) h2'))]
    have hat := hpre.atom _ hjN
    have hk : (l.addr - B) % 4 < 4 := Nat.mod_lt _ (by decide)
    have hidx : l.addr - (B + 4 * ((l.addr - B) / 4)) = (l.addr - B) % 4 := by omega
    simp only [wbyte, gB, hidx]
    simp [Value.toBytes, hat.1, List.getElem?_range hk, hat.2 _ hk]
  · apply hn
    intro w a bs hw' hcov
    obtain ⟨w, rfl, hwThread⟩ := hmem hw'
    obtain ⟨hwT, hwN, -, rfl, -⟩ := written_value hpre hX ht hwThread
    apply hl
    simp only [Acc.Covers, Loc.InRange, gB] at hcov
    obtain ⟨c1, c2, c3, c4⟩ := hcov
    have := Nat.le_min.mpr ⟨Nat.succ_le_of_lt hwN, Nat.succ_le_of_lt hwT⟩
    exact ⟨c1, c2, by omega, by omega⟩

end
end PTX.Kernels.CopyLdg.Proof
