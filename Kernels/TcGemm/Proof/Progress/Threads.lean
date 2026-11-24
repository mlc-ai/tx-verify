-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Progress.Blocked

@[expose] public section

/-! # `tc_gemm`: every maximal execution is complete

Descent over the obligations of an incomplete execution (`Descent.progress_of_steps`), ranked by
`rank`. Every event is of the Tensor Core/mbarrier/bulk class, so the open obligations are
pending threads, bulk copies, the MMA, the commit and uncovered allocator operations
(`Execution.TcBulk.open_cases`). A maximal execution has completed the copies and the MMA and
delivered the commit (`async_closed`). A released pending thread steps (`released_steps`), and so
does a thread that its last event blocks (`blocked_steps`); an uncovered allocator operation
passes to its pending thread (`tmem_steps`). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Proof

/-- **Every maximal execution is complete.** -/
theorem progress_goal {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0}
    (hpre : Pre L A B D a b mem0) (hC : ∀ g < L.threads, (code L A B D g).Sound)
    (hT : ∀ X, Consistent L kernel [] mem0 X → ThreadFacts L A B D X)
    (hS : SafeGoal kernel [] L mem0) : ProgressGoal kernel [] L mem0 :=
  Descent.progress_of_steps (Descent.Obl L) (rank L A B D)
    (fun _ _ hn => Descent.cover hn)
    fun X o hmax ho => by
      have ht := hT X hmax.1
      obtain ⟨P, m, u, hW⟩ := wit hpre ht hmax.1
      obtain ⟨hb, hmm, hc⟩ := async_closed hpre hmax hW ho
      rcases hW.tcBulk.open_cases ho with ⟨g, rfl⟩ | rfl | rfl | rfl | rfl
      · by_cases hrel : Step.Released L X g
        · exact released_steps hpre ht (hS.2 X hmax.1) hmax hW hC ho hrel
        · exact blocked_steps hpre ht hmax hW hC hT hS ho hrel
      · exact absurd rfl hb
      · exact absurd rfl hmm
      · exact absurd rfl hc
      · exact tmem_steps hmax hW ho

end PTX.Kernels.TcGemm.Proof
