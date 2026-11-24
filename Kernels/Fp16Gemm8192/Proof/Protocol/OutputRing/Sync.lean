-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Barrier

@[expose] public section

/-! # Synchronization through the output barriers

Two threads of a consumer warp group whose output barrier arrivals have the same ordinal meet
in one barrier generation: whatever the first did before its arrival happens before whatever the
second does after passing its own (`out_baseCausality`, from
`NamedBar.Sources.same_ordinal_baseCausality`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

namespace OutputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An output barrier arrival is of a warp of its group. -/
theorem out_warp (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {q : Nat} {e : EvId}
    {pc : Nat} {cnt : Option Nat}
    (he : X.IsBarrier e (q + 10) cnt pc) (hg : e.1 < L.threads) :
    (e.1 % L.block) / 32 ∈ group q ∧ cnt = some 128 ∧ Consumer.outId L e.1 = q + 10 := by
  obtain ⟨hc, hid, hw8, -⟩ := bar_facts hX ht he hg
  simp only [Consumer.tidOf, Consumer.outId] at hid hw8 ⊢
  refine ⟨?_, hc, by omega⟩
  simp only [group, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Two output barrier arrivals of a group with the same ordinal: what the first thread did
before its arrival happens before what the second does after passing its own. -/
theorem out_baseCausality (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {q : Nat} (hq : q < 2)
    {g h i j before after pc pc' : Nat} (hsame : SameCta L g h)
    (he : X.IsBarrier (g, i) (q + 10) (some 128) pc)
    (hf : X.IsBarrier (h, j) (q + 10) (some 128) pc')
    (hpassed : j + 1 < (X.tr h).length)
    (hordinal : ((X.tr g).take i).countP (Execution.isBarId (q + 10)) =
      ((X.tr h).take j).countP (Execution.isBarId (q + 10)))
    (hbefore : before < i) (hafter : j < after) (hlen : after < (X.tr h).length) :
    baseCausality L X (g, before) (h, after) :=
  (out_sources hX ht q).same_ordinal_baseCausality hX (group_shape hpre hq (by omega)) hsame he hf
    hpassed hordinal hbefore hafter hlen

end OutputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
