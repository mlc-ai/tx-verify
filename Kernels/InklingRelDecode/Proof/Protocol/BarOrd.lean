-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.BarOrdinal
public import Kernels.InklingRelDecode.Proof2.Lib.BarEarly

@[expose] public section

/-!
# The first two generations of named barrier 0

Barrier 0 has three groups in turn: the `bar.sync 0` of all 256 threads at the common start
(source ordinals 0 and 1), the `bar.sync 0, 128` of the default partition (the prologue, the
softmax loop and the epilogue) and the final `bar.sync 0` of all threads. The library's generation
lemmas, which ask one group for the whole barrier, do not apply to it; `BarEarly.lean` proves
them for the arrivals of small source ordinal (`EarlySources`), and this file discharges that
premise for barrier 0 with `N = 1`: the arrivals of source ordinal 0 and 1 are the common
start's, without a count, of a warp of the CTA. The proof is the ordinal measure of the abstract
states (`Interface/BarOrdinal.lean`): a thread's machine is at a site of the common start exactly
while it has made fewer than two barrier-0 events, and the events fired there are the two
`bar.sync 0`.

* `bar0_count_none`: a barrier-0 arrival of source ordinal at most 1 has no thread count;
* `bar0_ordinal_two`: an event fired from a state that is no site of the common start has made at
  least two barrier-0 arrivals;
* `earlySources_bar0`: `EarlySources` for barrier 0 with the group (8 warps, no count), `N = 1`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bar
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A barrier-0 arrival of source ordinal at most 1 has no thread count.** -/
theorem bar0_count_none (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {g k pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩)
    (hn : ((X.tr g).take k).countP (Execution.isBarId 0) ≤ 1) : cnt = none := by
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX ht he (fun pc' f h => by cases h)
  have hk : k ≤ (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simp only at this
    omega
  obtain ⟨h1, -⟩ := ordinal_inv hX hS k s hk hσ
  have hl : tLb s < 2 := by omega
  rcases start_event hX hS he hσ hl with ⟨-, pc', h⟩ | ⟨-, h⟩
  · simp only [Event.mk.injEq, Kind.bar.injEq, true_and] at h
    exact h.2.1
  · exact absurd rfl (h 0 cnt mode)

/-- **An event fired from a state that is no site of the common start follows two barrier-0
arrivals** of its thread. -/
theorem bar0_ordinal_two (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {s : TSt}
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some s)) (hl : ¬ tLb s < 2) :
    2 ≤ ((X.tr g).take k).countP (Execution.isBarId 0) := by
  have := (ordinal_inv hX hS k s hk hσ).1
  omega

/-- **The arrivals on barrier 0 of source ordinal at most 1 are the group's**: a warp of the
CTA, passing no thread count. -/
theorem earlySources_bar0 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X) :
    NamedBar.EarlySources L X none (Finset.range (CtaBarrier.warps L.block)) 0 1 := by
  intro e pc cnt ⟨mode, he⟩ hg hn
  refine ⟨?_, bar0_count_none hX hS ht he hn⟩
  have hb : L.block = 256 := hpre.block
  have : e.1 % L.block < 256 := by
    have := Nat.mod_lt e.1 (show L.block > 0 by omega)
    omega
  simp only [Finset.mem_range, CtaBarrier.warps, hb]
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Bar
