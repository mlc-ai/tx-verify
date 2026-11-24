-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RowSum.Proof.Values
public import Lemmas.Tcgen05.MemFloat
public import Lemmas.Kernel.Goals

@[expose] public section

/-! # `row_sum`: the result

In a complete execution thread `r` of a row stores the sum of the row at `B[r]`; no other byte is
written. -/

namespace PTX.Kernels.RowSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B M K : Nat} {x : Nat → ℝ} {mem0 : Mem0}

/-- **A complete execution leaves the row sums.** -/
theorem result (hpre : Pre L A B M K x mem0)
    (htf : ∀ X, Consistent L kernel Prod mem0 X → ThreadFacts L A B M K x X) :
    ResultGoal kernel Prod L mem0 (Post L B M K x mem0) := by
  intro X m hX hc hfin
  have htf := htf X hX
  have hexits := ((noTma_of_consistent noTma hX).complete_iff L hX.clc).mp hc
  -- the write of thread `j`, when it exists
  have hwrite : ∀ j < L.threads, j < M →
      X.Writes (j, K) { loc := gB B j, size := 4 } (accV x K j K).toBytes := by
    intro j hj hjM
    obtain ⟨a, hget, hval⟩ := htf.exit_write hj hjM (hexits j hj)
    have ha : a = accV x K j K := hval fun i bs h =>
      read_bytes hpre htf hX ⟨Flow.load_0, by unfold rdE at h; exact h⟩
    subst ha
    exact ⟨Flow.store_0, by unfold wrE at hget; exact hget⟩
  let v : Nat → Value := fun j => accV x K j K
  have hbyte : ∀ l, l.space = .global ∧ l.cta = 0 ∧ B ≤ l.addr ∧ l.addr < B + 4 * min M L.threads →
      m l = some (some (v ((l.addr - B) / 4), (l.addr - B) % 4)) := by
    intro l hl
    obtain ⟨h1, h2, h3, h4⟩ := hl
    have hjT : (l.addr - B) / 4 < L.threads := by have := Nat.min_le_right M L.threads; omega
    have hjM : (l.addr - B) / 4 < M := by have := Nat.min_le_left M L.threads; omega
    have hcov : Acc.Covers { loc := gB B ((l.addr - B) / 4), size := 4 } l := by
      simp only [Acc.Covers, Loc.InRange, gB]
      exact ⟨h1, h2, by omega, by omega⟩
    rw [hfin.unique (w := .thread (_, K)) (Or.inl (hwrite _ hjT hjM)) hcov
      (fun w' a' bs' hw' hc' => by
        obtain ⟨w', heRef, hwThread | ⟨old, hrmw⟩⟩ := Execution.NoTma.memWrites_thread
          ((noTma_of_consistent noTma hX).emptyAsync hX) hw'
        · subst heRef
          obtain ⟨-, -, h2', rfl⟩ := writes_cases htf hX hwThread
          exact congrArg AsyncCopy.Ref.thread (Prod.ext (covers_gB_gB hc' hcov) h2')
        · exact absurd hrmw (no_rmw htf hX))]
    have hk : (l.addr - B) % 4 < 4 := Nat.mod_lt _ (by decide)
    have hidx : l.addr - (B + 4 * ((l.addr - B) / 4)) = (l.addr - B) % 4 := by omega
    by_cases hK : K = 0
    · simp only [v, accV, wbyte, gB, hidx, hK, ↓reduceIte, b32_byte _ hk]
    · simp only [v, accV, wbyte, gB, hidx, hK, ↓reduceIte, fl_byte _ hk]
  refine ⟨fun r hr => ?_, fun l hl => ?_⟩
  · have hm : ∀ k < FloatFmt.f32.bytes, m ((⟨.global, 0, B + 4 * r⟩ : Loc).at k) =
        some (some (v r, k)) := by
      intro k hk
      change k < 4 at hk
      rw [hbyte _ ⟨rfl, rfl, by simp only [Loc.at]; omega, by simp only [Loc.at]; omega⟩]
      simp only [Loc.at]
      rw [show (B + 4 * r + k - B) / 4 = r by omega, show (B + 4 * r + k - B) % 4 = k by omega]
    rw [memFloat_of_bytes (by intro k; simp only [v, accV]; split_ifs <;> rfl)
      (by simp only [v, accV]; split_ifs <;> rfl) hm]
    by_cases hK : K = 0
    · simp only [v, accV, hK, ↓reduceIte, valFloat_z0, S, Finset.range_zero, Finset.sum_empty]
    · simp only [v, accV, hK, ↓reduceIte, valFloat_fl]
  · apply hfin.unwritten
    intro w a bs hw' hcov
    obtain ⟨w, heRef, hwThread | ⟨old, hrmw⟩⟩ := Execution.NoTma.memWrites_thread
      ((noTma_of_consistent noTma hX).emptyAsync hX) hw'
    · subst heRef
      obtain ⟨hwT, hwM, -, rfl⟩ := writes_cases htf hX hwThread
      apply hl
      simp only [Acc.Covers, Loc.InRange, gB] at hcov
      obtain ⟨c1, c2, c3, c4⟩ := hcov
      have := Nat.le_min.mpr ⟨Nat.succ_le_of_lt hwM, Nat.succ_le_of_lt hwT⟩
      exact ⟨c1, c2, by omega, by omega⟩
    · exact absurd hrmw (no_rmw htf hX)

end
end PTX.Kernels.RowSum.Proof
