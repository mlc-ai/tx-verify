-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Exit
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.RespSync

@[expose] public section

/-! # The order of a cluster's requests

Every request of a cluster is the leader's, numbered by its earlier requests; none is numbered
after a request whose response names no first CTA, so each request is that request or comes
before it in the leader's program order (`requestsBeforeFailure`). With
`issue_baseCausality_observer` this gives the CLC ring's exports for the failure branch of
`ClcUnsafe`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem issueBeforeObservers (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : IssueBeforeObservers L X :=
  fun _ _ _ _ hi ho => issue_baseCausality_observer hpre hX ht hi ho

theorem requestsBeforeFailure (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hv : ReaderValues L X) : RequestsBeforeFailure L X := by
  intro ⟨h, ki⟩ s tg ⟨h', ki'⟩ s' tg' r' ⟨pc, hei⟩ ⟨pc', hei'⟩ ⟨c0, hc0, c1, hc1, hcc⟩ hres hnone
  set c := c0 / 2
  obtain ⟨hp, hmb, -, -⟩ := issue_facts (c := c) hpre hX ht hei hc0 rfl
  obtain ⟨hp', hmb', -, -⟩ := issue_facts (c := c) hpre hX ht hei' hc1 hcc.symm
  have hfail : ¬ Loader.claims r' := by simp [Loader.claims, hnone]
  have hle := issues_le_failed hpre hX ht hv (c := c) (hp ▸ hei) hc0 rfl ⟨pc', hei'⟩
    ⟨c1, hc1, hcc.symm⟩ hres hfail
  simp only at hle
  subst hp
  subst hp'
  have hlen' : ki' < (X.tr (producer L X c)).length := len_of_get hei'
  rcases Nat.lt_or_ge ki ki' with hlt | hge
  · exact .inr (.single (.inl (po_of_not_access rfl hlt hlen' (by simp [hei', Event.acc]))))
  · rcases Nat.lt_or_eq_of_le hge with hgt | heq
    · exfalso
      have hlen : ki < (X.tr (producer L X c)).length := len_of_get hei
      have := issues_inj (L := L) (c := c) hei hei' (by simp [clcIssuesTo, hmb])
        (by simp [clcIssuesTo, hmb'])
        (le_antisymm hle (by
          unfold issuesBefore
          exact (List.take_sublist_take_left (l := X.tr (producer L X c)) hgt.le).countP_le
            (p := clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩))))
      omega
    · subst heq
      exact .inl rfl

end ClcRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
