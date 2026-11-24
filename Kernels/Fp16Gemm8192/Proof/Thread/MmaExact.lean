-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaCounts
public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # The MMA thread's exact counts at its full waits and accumulator sites

`Mma.Counts` relates, along an MMA thread's run, its commits to each input empty barrier to its
full polls (`commit`, exact: the pending commit of a full wait is none), and its accumulator
commits to the tasks they complete (`accRound`). So at a full wait its successful full polls are
its round-robin share of its commits (`mma_full_count`), and at its accumulator sites its
accumulator commits and accumulator-empty polls are its commits over 128 (`mma_acc_count`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An MMA thread in state `m` after its whole trace has the counts of `Mma.Counts`. -/
theorem mma_counts_end (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat}
    (hg : g < L.threads) {m : Mma.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m)))) :
    Mma.Counts L g m (X.tr g) := by
  have h := threadCounts_run hpre hg (Frame.trace (fun _ => sound hpre) hX hg)
    (X.tr g).length (.inr (.mma m)) hσ
  rw [List.take_length] at h
  exact h

/-- At an MMA thread's full wait on slot `s`, its successful polls of the slot's full barrier are
its
round-robin share of its commits to the input empty barriers. -/
theorem mma_full_count_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ {g : Nat} {m : Mma.D} {s : Fin 4}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) → m.site = .full s →
    okPolls ⟨.shared, g / L.block, L.sharedBase + 8 + 8 * s.val⟩ (X.tr g) =
      (mmaCount L g (X.tr g) + 3 - s.val) / 4 := by
  intro g m s hg _ hσ hs
  have h := mma_counts_end hpre hX hg hσ
  have hp : Mma.pendingCommit m s = false := by simp [Mma.pendingCommit, hs]
  have hc := h.commit s
  rw [hp] at hc
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc
  rw [mmaCount_eq]
  exact hc.symm.trans (h.rank s)

/-- At an MMA thread's state, its accumulator commits (with the accumulator commit it is making) are
its commits over 128, and its accumulator-empty polls (with that commit) are that count plus its
holding of an accumulator. -/
theorem mma_acc_count_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ∀ {g : Nat} {m : Mma.D}, g < L.threads →
    (∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) →
    Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))) →
    (X.tr g).countP (commitsTo (Bar.loc L (g / L.block) ⟨.acc, m.w % 2, true⟩)) +
      (if m.site = .accCommit then 1 else 0) = mmaCount L g (X.tr g) / 128 ∧
    okPolls (Bar.loc L (g / L.block) ⟨.acc, m.w % 2, false⟩) (X.tr g) +
      (if m.site = .accCommit then 1 else 0) = mmaCount L g (X.tr g) / 128 +
        (match m.site with | .full _ | .mma _ _ | .commit _ | .accCommit => 1 | _ => 0) := by
  intro g m hg _ hσ
  have h := mma_counts_end hpre hX hg hσ
  have h1 : (X.tr g).countP (commitsTo (Bar.loc L (g / L.block) ⟨.acc, m.w % 2, true⟩)) +
      (if m.site = .accCommit then 1 else 0) = mcount L g (X.tr g) / 128 := h.accRound
  have h2 : (X.tr g).countP (commitsTo (Bar.loc L (g / L.block) ⟨.acc, m.w % 2, true⟩)) +
      (match m.site with | .full _ | .mma _ _ | .commit _ | .accCommit => 1 | _ => 0) =
      okPolls (Bar.loc L (g / L.block) ⟨.acc, m.w % 2, false⟩) (X.tr g) := by
    have h0 := h.acc (m.w % 2) (Nat.mod_lt _ (by decide))
    simp only [↓reduceIte, Mma.holdsAcc] at h0
    exact h0
  rw [mmaCount_eq]
  refine ⟨h1, ?_⟩
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
  cases site <;> simp only [reduceCtorEq, ↓reduceIte] at h1 h2 ⊢ <;> omega

/-- The working MMA leaders' response reads, from the thread facts: at an accumulator-empty wait,
each
successful response poll followed by another is followed by a claiming read, and the successful
polls
are the task count plus one. -/
theorem mma_working_claims (ht : ThreadFacts L X) : MmaWorkingClaims L X := by
  intro g m hg hσ hs
  refine ⟨fun j pc p acq sc hj hcount => ?_, ?_⟩
  · obtain ⟨pcr, a, bs, rr, h1, h2, h3, h4, h5⟩ :=
      ht.mma_claims_before hg hσ j pc p acq sc hj hcount
    exact ⟨pcr, a, bs, rr, h1, ⟨h2, h3⟩, h4, h5⟩
  · have h := ht.mma_task_count hg hσ
    simp [hs] at h
    exact h

end
end PTX.Kernels.Fp16Gemm8192.Proof
