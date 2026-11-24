-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface
public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Barrier
public import Lemmas.Protocol.NamedBarSync
public import Lemmas.CtaBarrier.CtaBarrierIdentity
public import Kernels.Fp16Gemm8192.Proof.NoBarArrive

@[expose] public section

/-! # The CLC barriers of the consumer warp groups

Each consumer warp group `q < 2` (warps `4q` to `4q+3`, `OutputRing.group q`) has a CLC barrier,
the named barrier `q + 1`: only its 128 threads arrive there, each counting 128 (`clc_sources`).
This is the analogue of the group's output barrier `q + 10` (`OutputRing`): through the library's
named barrier lemmas (`NamedBar.Sources`), a passed generation has every participant's arrival of
its ordinal (`member_arrival`), and two arrivals of one ordinal are ordered in memory
(`baseCausality_of_ordinal`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

namespace ClcGroup

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A named barrier arrival on `q + 1` is a consumer's, of group `q`, counting 128. -/
theorem group_bar_facts (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {q : Nat}
    (hq : q < 2) {e : EvId} {pc : Nat}
    {cnt : Option Nat} (he : X.IsBarrier e (q + 1) cnt pc) (hg : e.1 < L.threads) :
    cnt = some 128 ∧ (e.1 % L.block) / 32 ∈ OutputRing.group q ∧
      ∃ c, Frame.stateAt (code L) X e.1 e.2 = some (some (.inr (.cons c))) := by
  obtain ⟨hc, hid, hw8, c, hσ⟩ := OutputRing.bar_facts hX ht he hg
  refine ⟨hc, ?_, c, hσ⟩
  simp only [Consumer.tidOf, Consumer.outId] at hid hw8
  simp only [OutputRing.group, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- **The sources of the CLC barrier `q + 1`**: only the warps of group `q` arrive there, each
counting 128. -/
theorem clc_sources (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {q : Nat}
    (hq : q < 2) : NamedBar.Sources L X (some 128) (OutputRing.group q) (q + 1) := by
  intro e pc cnt he hg
  obtain ⟨hc, hw, -⟩ := group_bar_facts hX ht hq (hX.isBarrier_of_arrival Fact.out he) hg
  exact ⟨hw, hc⟩

/-- A passed generation of a group's CLC barrier has the arrival of that ordinal of every thread
of the group in the CTA: from the released generation for a thread that never exits, and for an
exited thread from its arrivals (`OutputRing.exited_member_arrival`). -/
theorem member_arrival (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {q : Nat} (hq : q < 2) {f : EvId} {pc : Nat}
    (hf : X.IsBarrier f (q + 1) (some 128) pc)
    (hpassed : f.2 + 1 < (X.tr f.1).length)
    (hagree : OutputRing.ResponsesAgreeBelow L X
      (((X.tr f.1).take f.2).countP (Execution.isBarId (q + 1))))
    {g : Nat} (hcta : g / L.block = f.1 / L.block) (hgt : g < L.threads)
    (hw : (g % L.block) / 32 ∈ OutputRing.group q) :
    ∃ i pc', X.IsBarrier (g, i) (q + 1) (some 128) pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId (q + 1)) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId (q + 1)) := by
  refine (clc_sources hX ht hq).member_arrival hX (OutputRing.group_shape hpre hq (by omega)) hf
    hpassed hcta hw fun ⟨j, pcx, hj⟩ => ?_
  have hfg : f.1 < L.threads := Frame.lt_of_get hX hf
  have hl := Execution.exit_last hX hgt hj
  have hlast : (X.tr g).getLast? = some ⟨pcx, .exit⟩ := by
    rw [List.getLast?_eq_getElem?, show (X.tr g).length - 1 = j by omega]
    exact hj
  have hfw := (group_bar_facts hX ht hq hf hfg).2.1
  simp only [OutputRing.group, Finset.mem_insert, Finset.mem_singleton] at hw hfw
  exact OutputRing.exited_member_arrival hX ht hgt (by omega) hlast hf hfg hcta.symm (by omega)
    hagree

/-- Two CLC barrier arrivals of a group with the same ordinal: what the first thread did before
its arrival happens before what the second does after passing its own. -/
theorem baseCausality_of_ordinal (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {q : Nat} (hq : q < 2)
    {g h i j before after pc pc' : Nat} (hsame : SameCta L g h)
    (he : X.IsBarrier (g, i) (q + 1) (some 128) pc)
    (hf : X.IsBarrier (h, j) (q + 1) (some 128) pc')
    (hpassed : j + 1 < (X.tr h).length)
    (hordinal : ((X.tr g).take i).countP (Execution.isBarId (q + 1)) =
      ((X.tr h).take j).countP (Execution.isBarId (q + 1)))
    (hbefore : before < i) (hafter : j < after) (hlen : after < (X.tr h).length) :
    baseCausality L X (g, before) (h, after) :=
  (clc_sources hX ht hq).same_ordinal_baseCausality hX
    (OutputRing.group_shape hpre hq (by omega)) hsame he hf hpassed hordinal hbefore hafter hlen

end ClcGroup

end
end PTX.Kernels.Fp16Gemm8192.Proof
