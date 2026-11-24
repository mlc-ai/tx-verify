-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Async.AsyncChain

/-!
# Litmus test of EXT-PAIR-ASYNC without a `cta_group::2` operation

CTA0 and CTA1 form an aligned pair of a cluster of two; `s1` is a byte of CTA1's shared memory.
No instruction has `.cta_group::2`.

```
// CTA0
cp.async.bulk.shared::cluster.global.mbarrier::complete_tx::bytes [s1], [gA], 16, [m1];

// CTA1: acquire wait on m1, then
cp.async.bulk.global.shared::cta.bulk_group [out], [s1], 16;
```

The copy of CTA0 writes `s1` and the copy of CTA1 reads it. §8.9.5 orders async-proxy accesses of
one thread block only, and neither copy is a `cta_group::2` `tcgen05` operation, so the model orders
the write before the read by no chain: the read may return the old content of `s1`, and the write
and the read conflict unordered. With a `cta_group::2` `tcgen05.mma` as an endpoint, a direct edge
between the two CTAs is ordered (`modelCausality_pair_direct`).
-/

namespace PTX.Tests.PairAsyncScope
open AsyncCopy
noncomputable section

private def L : Launch := { grid := 2, block := 1, clusterSize := 2, params := fun _ => none }
private def s1 : Loc := ⟨.shared, 1, 64⟩

/-- CTA0's copy from global memory into CTA1's shared memory, completed on `m1` of CTA1. -/
private def load : AsyncCopy.Spec :=
  { src := { loc := ⟨.global, 0, 0⟩, size := 16 }, dst := { loc := s1, size := 16 },
    completion := .mbarrier ⟨.shared, 1, 0⟩ }
/-- CTA1's copy from its shared memory to global memory, completed by its bulk group. -/
private def store : AsyncCopy.Spec :=
  { src := { loc := s1, size := 16 }, dst := { loc := ⟨.global, 0, 64⟩, size := 16 },
    completion := .bulkGroup }

/-- The two copies; the acquire wait and the other instructions do not matter here. -/
private def X : Execution := {
  tr := fun t => if t = 0 then [⟨0, .copy load⟩] else if t = 1 then [⟨0, .copy store⟩] else []
  rf := fun _ _ => none
}

/-- The two CTAs form a pair and `s1` belongs to it: before the fix this alone related them. -/
example : PairAsync L s1 0 1 := by
  refine ⟨rfl, ?_, ?_⟩ <;> rw [sameCtaGroup_iff] <;>
    simp [CtaInCluster, L, s1, Launch.rankOfCta, Launch.clusterOfCta, CtaGroup.size,
      Launch.locate] <;> decide

/-- No event of `X` is a `cta_group::2` `tcgen05` operation. -/
private theorem no_pairTc (i : EvId) : ¬ PairTc X i := by
  obtain ⟨t, k⟩ := i
  rintro (⟨d, s, acc, mask, ⟨pc, h⟩, -⟩ | ⟨c, ⟨pc, h⟩, -⟩) <;>
  · rcases t with _ | _ | t <;> rcases k with _ | k <;> simp [Execution.get, X] at h

/-- The write of CTA0's copy precedes the read of CTA1's copy in no `modelCausality`, whatever
parts and chain: the read may return the old content of `s1`. -/
theorem copies_unordered (p q : Part) :
    ¬ modelCausality L X s1 (.async (0, 0) p) (.async (1, 0) q) := by
  rintro ⟨hs | ⟨-, hc | hc⟩, -⟩
  · obtain ⟨-, -, h⟩ := hs
    simp [L] at h
  · exact no_pairTc _ hc
  · exact no_pairTc _ hc

/-- In the other direction neither. -/
theorem copies_unordered' (p q : Part) :
    ¬ modelCausality L X s1 (.async (1, 0) q) (.async (0, 0) p) := by
  rintro ⟨hs | ⟨-, hc | hc⟩, -⟩
  · obtain ⟨-, -, h⟩ := hs
    simp [L] at h
  · exact no_pairTc _ hc
  · exact no_pairTc _ hc

/-- With a `cta_group::2` `tcgen05.mma` as the later endpoint, a direct asynchronous edge between
the two CTAs of the pair is ordered. -/
example {Y : Execution} {i j : EvId} {p q : Part} (hpa : PairAsync L s1 i.1 j.1) (hj : PairTc Y j)
    (h : AsyncBefore L Y s1 (i, p) (j, q)) : modelCausality L Y s1 (.async i p) (.async j q) :=
  modelCausality_pair_direct hpa (.inr hj) h

end

end PTX.Tests.PairAsyncScope
