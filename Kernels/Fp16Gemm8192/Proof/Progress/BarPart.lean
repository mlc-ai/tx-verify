-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.BarLag
public import Lemmas.Step.CtaBarNamed
public import Lemmas.Step.ExitLast
public import Kernels.Fp16Gemm8192.Proof.NoBarArrive

@[expose] public section

/-! # The participants of a group's named barrier

The arrivals on a consumer warp group's barrier (the group's CLC barrier or output barrier) in a
CTA are the lanes of the group's four warps, each counting 128 threads (`bar_event_facts`,
`bar_sources`), and none of those lanes has an exit event while a thread of the CTA is in its task
loop: an exit completes both cluster arrivals of every thread of the cluster (`ClusterExitAll`). So
the group's warps are the participants of the named resource (`bar_part`, `NamedBar.Part`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The warps of consumer warp group `q`. -/
def group (q : Nat) : Finset Nat := {4 * q, 4 * q + 1, 4 * q + 2, 4 * q + 3}

theorem group_card (q : Nat) : (group q).card = 4 := by
  simp only [group]
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_pair (by omega)]

theorem mem_group {q w : Nat} : w ∈ group q ↔ w / 4 = q := by
  simp only [group, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- A consumer with no exit stage has made exactly its first cluster arrival. -/
theorem clPhase_of_loop {c : Consumer.D} (h : Consumer.exitOff c = none) :
    ThreadD.clPhase (Sum.inr (Prologue.Role.cons c)) = 1 := by
  unfold ThreadD.clPhase Consumer.exitOff at *
  cases hs : c.site <;> simp_all

/-- A named barrier arrival is a consumer's, counting 128 threads, on its group's CLC barrier or
output barrier. -/
theorem bar_event_facts (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    (hub : ¬ HasUb X) {y j pc id : Nat}
    {cnt : Option Nat} (hy : y < L.threads) (he : X.get (y, j) = some ⟨pc, .bar id cnt⟩) :
    cnt = some 128 ∧
      (id = Consumer.tidOf L y / 32 / 4 + 1 ∨ id = Consumer.outId L y) ∧
      Consumer.tidOf L y / 32 < 8 := by
  obtain ⟨d, hσ⟩ := Frame.state_of_noUb ht.sound hX ht.tracked hub he
  obtain ⟨c, rfl⟩ := ht.bar_role hy he hσ rfl
  have hrw := ht.role_warp hy (len_of_get he).le hσ
  simp only [roleWarp] at hrw
  rcases (ht.cons_out hy he hσ).2.2.2.2.1 id cnt rfl with ⟨-, hid, hc⟩ | ⟨-, hid, hc⟩
  · exact ⟨hc, .inl hid, hrw⟩
  · exact ⟨hc, .inr hid, hrw⟩

/-- The shape of a group's barrier: the four warps of the group, each counting 128. -/
theorem bar_shape (hpre : Pre P L mem0) {q : Nat} (clc : Bool) (hq : q < 2) :
    NamedBar.Shape L (some 128) (group q) (barId clc q) := by
  have hB : L.block = 384 := hpre.block
  refine ⟨by rw [group_card]; decide, ?_, fun w hw => ?_, by cases clc <;> simp [barId] <;> omega⟩
  · rw [group_card]
    exact NamedBar.target_some_mul (n := 4) (by decide) (by decide)
  · have := mem_group.mp hw
    omega

/-- **The sources of a group's barrier**: its arrivals are the lanes of the group's warps, each
counting 128. -/
theorem bar_sources (ht : ThreadFacts L X) (hub : ¬ HasUb X) (hX : Consistent L kernel Prod mem0 X)
    {q : Nat} (clc : Bool) (hq : q < 2) :
    NamedBar.Sources L X (some 128) (group q) (barId clc q) := by
  intro e pc cnt he hy
  obtain ⟨h1, h2, h3⟩ := bar_event_facts hX ht hub (y := e.1) (j := e.2) hy
    (hX.isBarrier_of_arrival Fact.out he)
  refine ⟨mem_group.mpr ?_, h1⟩
  simp only [Consumer.tidOf, Consumer.outId, barId] at h2 h3 ⊢
  cases clc <;> simp at h2 <;> omega

/-- **The participants of a group's barrier in a CTA.** When a thread of the CTA is in its task loop
(its cluster arrivals are one), the warps of the group are the participants of the group's barrier
(`id = barId clc q`): its arrivals are their lanes', counting 128 (`bar_sources`), and none of
their lanes has an exit event. -/
theorem bar_part (ht : ThreadFacts L X) (hub : ¬ HasUb X) (hX : Consistent L kernel Prod mem0 X)
    (hexit : ClusterExitAll L X) {g q : Nat} {clc : Bool} (hq : q < 2) (hg : g < L.threads)
    (hcl1 : clArrives (X.tr g) = 1) :
    NamedBar.Part L X (g / L.block) (some 128) (barId clc q) (group q) := by
  refine NamedBar.Sources.part hX (bar_sources ht hub hX clc hq) fun y hyc hyw j pc hj => ?_
  have hy : y < L.threads := Frame.lt_of_get hX hj
  have hlast := Execution.exit_last hX hy hj
  have hl : (X.tr y).getLast? = some ⟨pc, .exit⟩ := by
    rw [List.getLast?_eq_getElem?]
    have : (X.tr y).length - 1 = j := by omega
    rw [this]
    exact hj
  have hclu : L.clusterOfCta (g / L.block) = L.clusterOfCta (y / L.block) := by rw [hyc]
  have := hexit y pc hy hl g hg hclu
  omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
