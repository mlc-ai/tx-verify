-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Ledger
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Ordinals
public import Lemmas.Protocol.NamedBarSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites

@[expose] public section

/-! # Barrier ordinals of the softmax warpgroup -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0BarrierCount

open PTX PTX.Flow Ledger Wg0BarrierTrace

variable {P : Params}

private theorem bar9_false {L : Launch} {mem0 : Mem0} {g : Nat} {d : Machine.ThreadD} {e : Event}
    {o : Option TState} (hpre : Pre P L mem0) (hf : (Machine.machine P L g).Fired (some d) e o)
    (hn : ∀ q, d = .wg0 q → ¬ Bar9Site q.site) : Execution.isBarId 9 e = false := by
  cases he : Execution.isBarId 9 e
  · rfl
  · obtain ⟨_, _, _, hk⟩ := NamedBar.isBarId_form he
    obtain ⟨q, hq, hs, _, _, _⟩ := bar9_fired hpre hf (congrArg Event.kind hk)
    exact (hn q hq hs).elim

private theorem count_at {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0)
    (ht : (Machine.machine P L g).Trace (Machine.machine P L g).init (X.tr g))
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d))) :
    ((X.tr g).take k).countP (Execution.isBarId 9) = ordinal d :=
  Ledger.wg0 (Z := (· = (.bar 9)))
    (fun _ _ _ _ hf hc => by subst hc; exact bar9_false hpre hf fun _ h => by cases h)
    ht (fun d n => n (.bar 9) = ordinal d)
    (fun n hn => (hn _ rfl).trans (Wg0Ordinals.init_zero P L g).1.symm)
    (fun d _ n e o hf hs hc => by
      have hf : (Machine.machine P L g).Fired (some (.wg0 d)) e o := hf
      simp only [bump_apply, hc, (Wg0Ordinals.step hs).1, Cls.test]
      by_cases hc : Bar9Site d.site
      · simp [Execution.isBarId, bar9_kind hpre hf hc, hc]
      · simp [bar9_false hpre hf (fun q h => by cases h; exact hc), hc]) hst

/-- The actual softmax warpgroup barrier prefix has the ordinal of the current state. -/
theorem count_at_wg0 {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, k) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d))) :
    ((X.tr g).take k).countP (Execution.isBarId 9) = ordinal d :=
  count_at hpre (hs.produces (hX.thr g (Frame.lt_of_get hX he))) hst

/-- The barrier count at a followed softmax tail does not require a following event. -/
theorem count_at_wg0_tail {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hg : g < L.threads)
    (hst : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d))) :
    (X.tr g).countP (Execution.isBarId 9) = ordinal d := by
  have h := count_at hpre (hs.produces (hX.thr g hg)) hst
  simpa only [List.take_length] using h

/-- An exchange write or peer read follows the first whole-warpgroup barrier of its block. -/
theorem peerCount {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {d : Wg0.D} {e : Event}
    {j : Fin 8} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, k) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)))
    (hsite : d.site = .peerRead j ∨ d.site = .exchStore j) :
    ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * d.block + 1 := by
  have htrace := hs.produces (hX.thr g (Frame.lt_of_get hX he))
  have hc := count_at hpre htrace hst
  change _ = ordinal d at hc
  rcases hsite with h | h <;> simpa only [ordinal, localOrdinal, h] using hc

/-- A probability store follows both whole-warpgroup barriers of its block. -/
theorem probabilityCount {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {d : Wg0.D}
    {e : Event} {j : Fin 4} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, k) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)))
    (hsite : d.site = .pStore j) :
    ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * d.block + 2 := by
  have htrace := hs.produces (hX.thr g (Frame.lt_of_get hX he))
  have hc := count_at hpre htrace hst
  change _ = ordinal d at hc
  simpa only [ordinal, localOrdinal, hsite] using hc

/-- The output barrier for tile `j` follows two barriers per sparse block and the two row-sum
barriers. Thus its source ordinal is a function of the CTA's row and the tile alone. -/
theorem epiOrdinal {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {d : Wg0.D} {e : Event}
    {j : Fin 4} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, k) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d))) (hj : d.site = .epiBar j)
    :
    ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * Wg0.blocksOf P L g + 2 + j.val := by
  have htrace := hs.produces (hX.thr g (Frame.lt_of_get hX he))
  have hc := count_at hpre htrace hst
  obtain ⟨_, _, ⟨_, hinv⟩, _⟩ := htrace.fired_at he hst
  have hblock := hinv.epilogueLast (by rw [hj]; rfl)
  change _ = ordinal d at hc
  simp only [ordinal, hj, localOrdinal] at hc
  omega

/-- The actual barrier at an output tile's source ordinal belongs to that same output tile. -/
theorem epiSite_of_ordinal {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {e : Event}
    {j : Fin 4} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, k) = some e) (hkind : e.kind = .bar 9 (some 128) .sync)
    (hordinal : ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * Wg0.blocksOf P L g + 2 + j.val)
    :
    ∃ d, Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)) ∧ d.site = .epiBar j := by
  obtain ⟨d, hst, hbar, _, _, _⟩ := bar9_at hpre hX hs ht he hkind
  have htrace := hs.produces (hX.thr g (Frame.lt_of_get hX he))
  have hc := count_at hpre htrace hst
  obtain ⟨_, _, ⟨_, hinv⟩, _⟩ := htrace.fired_at he hst
  have hb := hinv.blockLt
  change _ = ordinal d at hc
  rw [hordinal] at hc
  refine ⟨d, hst, ?_⟩
  cases hd : d.site <;> simp [Bar9Site, hd] at hbar
  case epiBar j' =>
    have hlast := hinv.epilogueLast (by rw [hd]; rfl)
    simp only [ordinal, hd, localOrdinal] at hc
    congr 1
    exact Fin.ext (by omega)
  all_goals simp only [ordinal, hd, localOrdinal] at hc
  all_goals omega


/-- The local maximum write and its following barrier use the first half of the block's
warpgroup barrier pair. -/
theorem rowMaxCount {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, k) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)))
    (hsite : d.site = .rowMax ∨ d.site = .wg0Sync2) :
    ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * d.block + 1 := by
  have htrace := hs.produces (hX.thr g (Frame.lt_of_get hX he))
  have hc := count_at hpre htrace hst
  change _ = ordinal d at hc
  rcases hsite with h | h <;> simpa only [ordinal, localOrdinal, h] using hc

/-- A peer maximum read follows the second barrier. The row sum aliases its word after
an additional barrier in the epilogue. -/
theorem maxReadCount {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, k) = some e)
    (hst : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)))
    (hsite : d.site = .maxRead ∨ d.site = .lseStore0) :
    ((X.tr g).take k).countP (Execution.isBarId 9) =
      2 * d.block + (if d.site = .lseStore0 then 3 else 2) := by
  have htrace := hs.produces (hX.thr g (Frame.lt_of_get hX he))
  have hc := count_at hpre htrace hst
  change _ = ordinal d at hc
  rcases hsite with h | h <;> simpa [ordinal, localOrdinal, h] using hc

/-- The odd ordinal inside the sparse loop identifies the second barrier of that block. -/
theorem maxBarrier_of_followed_ordinal {L : Launch} {mem0 : Mem0} {X : Execution} {g k block : Nat}
    {e : Event} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (hFollow : Frame.stateAt (Machine.code P L) X g k ≠ some none) (he : X.get (g, k) = some e)
    (hkind : e.kind = .bar 9 (some 128) .sync) (hblock : block < Wg0.blocksOf P L g)
    (hcount : ((X.tr g).take k).countP (Execution.isBarId 9) = 2 * block + 1) :
    ∃ d, Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)) ∧
      d.site = .wg0Sync2 ∧ d.block = block := by
  obtain ⟨q, _, hst, hf⟩ :=
    RingSourceSites.fired_at_followed hX hs hFollow he (by simp [hkind])
  obtain ⟨d, rfl, hbar, _, _, _⟩ := bar9_fired hpre hf hkind
  have htrace := hs.produces (hX.thr g (Frame.lt_of_get hX he))
  have hc := count_at hpre htrace hst
  obtain ⟨_, _, ⟨_, hinv⟩, _⟩ := htrace.fired_at he hst
  change _ = ordinal d at hc
  rw [hcount] at hc
  refine ⟨d, hst, ?_⟩
  cases hd : d.site <;> simp only [Bar9Site, hd] at hbar
  case wg0Sync2 =>
    simp only [ordinal, localOrdinal, hd] at hc
    exact ⟨rfl, by omega⟩
  case lseBar2 =>
    have hlast := hinv.epilogueLast (by rw [hd]; rfl)
    simp only [ordinal, localOrdinal, hd] at hc
    omega
  case epiBar j =>
    have hlast := hinv.epilogueLast (by rw [hd]; rfl)
    simp only [ordinal, localOrdinal, hd] at hc
    omega
  all_goals simp only [ordinal, localOrdinal, hd] at hc
  all_goals omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0BarrierCount
