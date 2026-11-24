-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaTripReads
public import Kernels.TmlFa4Fwd.Proof.MmaTrips
public import Kernels.TmlFa4Fwd.Proof.MmaFirstWait
public import Kernels.TmlFa4Fwd.Proof.MmaGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

/-- The trip counter and the first Q parity are computed from the three loaded request words. -/
theorem runToFirstQPoll {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {batch tile : Nat} (hb : batch < p.batch) (htile : 256 * tile < p.qLength batch) :
    Seg kernel Assumptions.all l g 24 2117 (tripCountEntry p l batch tile) 2141
      [(2535, b32 l.sharedBase), (2536, b32 0), (1189, b32 (trips p batch tile))] := by
  have hKeys := (hp.lengths batch hb).2.2
  have hFits := (trips_bounds hp hb htile).2.2
  have hLen := (hp.lengths batch hb).2.1
  let key := p.kLength batch
  let causal := key - p.qLength batch + 256 * (tile + 1)
  let a := (key + 127) / 128
  let b := (causal + 127) / 128
  have hk : key < 2 ^ 31 := by dsimp only [key]; omega
  have hCausal : causal < 2 ^ 31 := hFits
  have hQEnd : 256 * (tile + 1) < 2 ^ 31 :=
    (Nat.le_add_left _ (key - p.qLength batch)).trans_lt hCausal
  have ha : a < 2 ^ 31 := by dsimp only [a]; omega
  have hb' : b < 2 ^ 31 := by dsimp only [b]; omega
  intro t ht
  obtain ⟨u, hA, hu⟩ := keyBlockCount l g hk t (ht.mono ⟨ht.2.2.2.2.1, trivial⟩)
  have hFrame1 {r : Nat} (hr : r ∈ [2541, 2540, 7202]) : u.regs r = t.regs r :=
    schedulerLocalFrame (lo := 2117) (len := 10) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hA ht.1.ge (by rw [ht.1]) hr
  have hu' : At u 2127 [(2541, b32 key), (7202, b32 (256 * (tile + 1))),
      (2540, b32 (2^32 - p.qLength batch))] := hu.mono (by
    refine ⟨?_, ?_, ?_, trivial⟩
    · rw [hFrame1 (by decide)]
      exact ht.2.2.2.2.1
    · rw [hFrame1 (by decide)]
      exact ht.2.2.2.2.2.2.1
    · rw [hFrame1 (by decide)]
      exact ht.2.2.2.2.2.1)
  obtain ⟨v, hB, hv⟩ := causalLength l g hk hLen hQEnd hFits u hu'
  obtain ⟨w, hC, hw⟩ := causalBlockCount l g hCausal v hv
  have hAB := run_comp hB hC
  have hFrame2 : w.regs 2548 = u.regs 2548 :=
    schedulerLocalFrame (lo := 2127) (len := 12) (regs := [2548]) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hAB hu.1.ge (by rw [hu.1]) (by simp)
  have hw' : At w 2139 [(2548, b32 a), (2557, b32 b)] := hw.mono
    ⟨hFrame2.trans hu.2.2.2.2.1, hw.2.2.2.2.1, trivial⟩
  obtain ⟨s, hD, hs⟩ := firstPollCount l g ha hb' w hw'
  have hRun := run_comp (run_comp hA hAB) hD
  have hFrame : s.regs 2535 = t.regs 2535 :=
    schedulerLocalFrame (lo := 2117) (len := 24) (regs := [2535]) (by
      set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hRun ht.1.ge (by rw [ht.1]) (by simp)
  have hLocal := localRun (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hRun
  exact ⟨s, hLocal, hs.mono
    ⟨hFrame.trans ht.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.1, trivial⟩⟩

/-- Advance the actual three-read cursor to the first Q0 barrier with the positive trip count. -/
theorem trackToFirstQPollInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos batch tile : Nat} (hb : batch < p.batch) (htile : 256 * tile < p.qLength batch)
    {t : TState} {ending : Option TState} (ht : At t 2112 (tripReadEntry p l batch tile))
    (hCuQ : ∀ lane ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * (batch + lane))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * batch)).at k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hDemand : Loader.PrefixDemand X g pos 2145 ending) :
    0 < trips p batch tile ∧
      ∃ u, At u 2141 [(2535, b32 l.sharedBase), (2536, b32 0), (1189, b32 (trips p batch tile))] ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 3)) ending ∧
        Loader.PrefixDemand X g (pos + 3) 2145 ending := by
  obtain ⟨v, hv, hV, hFirst, hSecond, hThird⟩ :=
    tripReadsTraceInPrefix hp hX hb (by omega) ht hCuQ hUsedK hr
      (hDemand.weaken (by decide))
  have hAfter := ((hDemand.advance hFirst (show 2112 ≤ 2145 by decide)).advance
    hSecond (show 2113 ≤ 2145 by decide)).advance
    (by simpa only [Nat.add_assoc] using hThird) (show 2116 ≤ 2145 by decide)
  have hTail : Loader.PrefixDemand X g (pos + 3) 2145 ending := by
    simpa only [Nat.add_assoc] using hAfter
  obtain ⟨u, hLocal, hu⟩ := runToFirstQPoll hp g hb htile v hv
  exact ⟨(trips_bounds hp hb htile).1, u, hu,
    hV.after_local_nonempty (run_rtg hLocal) (hTail.nonempty hV), hTail⟩

end PTX.Kernels.TmlFa4Fwd.Mma
