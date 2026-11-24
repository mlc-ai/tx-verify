-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.Async

@[expose] public section

/-! # An issued tensor store completes

An open store obligation of a maximal execution is an issued TMA store whose observation is not yet
fully done. Every byte the store reads has a source write visible to its read, and every visible
write has a defined byte (`OutputSources`), so the store makes progress: its missing
reads are recorded from the latest visible writers, then its writes and its completion flags
(`Step.StoreDone.pending_issue_visible`). A maximal execution has no such store
(`store_obl_steps`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow

noncomputable section

/-- The facts the open store obligation's step uses, for every consistent execution. -/
structure StoreFacts (L : Launch) (mem0 : Mem0) : Prop where
  ub : ∀ Y, Consistent L kernel Prod mem0 Y → ¬ HasUb Y
  thread : ∀ Y, Consistent L kernel Prod mem0 Y → ThreadFacts L Y
  sources : ∀ Y, Consistent L kernel Prod mem0 Y → OutputSources L Y

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An open store obligation steps.** An issued tensor store whose observation is not fully done
extends the execution by a counted event. -/
theorem store_obl_steps (hF : StoreFacts L mem0)
    (hmax : Maximal L kernel Prod mem0 X) (hsg : SyncGuarded L kernel X)
    (ho : Descent.Obl L X .store) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X .store := by
  classical
  have hX := hmax.1
  obtain ⟨i, a, spec, hi, hn⟩ : ∃ i a spec, X.TensorStoreIssue i a spec ∧
      ¬ ∃ o, X.tensorStores i = some o ∧ o.effects.fullDone = true := by
    by_contra hc
    push Not at hc
    exact ho fun i a spec hi => hc i a spec hi
  have ht := hF.thread X hX
  obtain ⟨pc, hge⟩ := hi
  have hht : i.1 < L.threads := Frame.lt_of_get hX hge
  obtain ⟨d, hσ⟩ := Frame.state_of_noUb ht.sound hX ht.tracked (hF.ub X hX) hge
  obtain ⟨c, st, rfl, hsite, hvalid, b, cls, origin, hsp⟩ := ht.cons_tma hht hge hσ
  exact .inl (Step.StoreDone.pending_issue_visible hX (fun Y a ha => prod_wfFree a ha Y)
    ⟨a, pc, hge⟩ hvalid hn (hF.sources X hX i a spec ⟨pc, hge⟩) hsg (by rw [hsp]))

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
