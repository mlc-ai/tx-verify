-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.AllocationBarrierEntry
public import Lemmas.CtaBarrier.FirstGeneration
public import Lemmas.Protocol.NamedBarMember
import Kernels.TmlFa4Fwd.Proof.NamedBarrierParticipants

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue

/-- Eight softmax warps, four correction warps and the allocating warp use barrier 2. -/
theorem allocationBarrierShape {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) :
    NamedBar.Shape l (some 416) (Finset.range 13) 2 := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · rw [hp.block]
    simpa using (NamedBar.target_some_mul (block := 512) (n := 13) (by decide) (by decide))
  · intro w hw
    rw [hp.block]
    have := Finset.mem_range.mp hw
    omega

/-- Both generations of the allocation rendezvous have the same physical participants. -/
theorem allocationBarrierSources {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    NamedBar.Sources l X (some 416) (Finset.range 13) 2 := by
  intro i pc count hArrival _
  obtain ⟨mode, he⟩ := hArrival
  have hCount := actualNamedBarrierCountById hp hX he
  have hExpected : count = some 416 := by simpa [countOfBarrierId] using hCount
  have hNamed := actualNamedBarrier hp hX he
  have hSites : pc ∈ [1910, 2764, 3103, 7741, 7747, 9204] := by
    have audit : namedBarrierSites.all (fun site =>
        !decide (namedBarrierCount site = some 416) ||
          [1910, 2764, 3103, 7741, 7747, 9204].contains site) = true := by decide
    have hAllowed := List.all_eq_true.mp audit pc hNamed.1
    rw [hNamed.2.1] at hExpected
    simpa [hExpected] using hAllowed
  have hNotHint : pc ∉ registerHintSites := by
    have audit : [1910, 2764, 3103, 7741, 7747, 9204].all
        (fun site => !registerHintSites.contains site) = true := by decide
    have hSite := List.all_eq_true.mp audit pc hSites
    simpa using hSite
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSites
  have hRole := roleBodyPcOfEvent hp hX he (show 173 < pc by omega) hNotHint
  change roleBodyPc (warpIndex l i.1) pc at hRole
  have hWarp : warpIndex l i.1 < 13 := by
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  exact ⟨Finset.mem_range.mpr hWarp, hExpected⟩

/-- Barrier 2's first generation contains only the initial rendezvous of its thirteen
participants. This rules out every later arrival, even a dynamic instruction carrying ID 2. -/
theorem allocationGenerationZeroSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g j : Nat}
    (hGen : CtaBarrier.GenerationOf l.block (X.barriers (g/l.block)) (g,j) 2 0) :
    warpIndex l g < 13 ∧
      ∃ pc ∈ allocationEntrySites, X.IsBarrier (g,j) 2 (some 416) pc := by
  obtain ⟨cnt, pc, mode, he⟩ := hX.ctaBar.generation_barrier hGen
  by_cases hSite : pc ∈ allocationEntrySites
  · have hBar := actualAllocationEntry hp hX hSite he
    have role := allocationEntryRole hp hX hSite hBar
    exact ⟨by omega, pc, hSite, hBar⟩
  · obtain ⟨i, hLt, source, _, hBar⟩ := allocationEntryBeforeBarrier hp hX he hSite
    exact (CtaBarrier.not_generationZero_after_sync hX (by decide) hLt hBar hGen).elim

/-- The barrier-2 history up to its first completion has the initial thirteen-warp protocol. -/
theorem allocationProtocolPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {c last : Nat}
    (hc : c < l.grid) {s : CtaBarrier.State}
    (hAt : CtaBarrier.At l.block (X.barriers c) last s) (hGen : (s.slots 2).generation = 0) :
    NamedBar.Protocol (some 416) (Finset.range 13) 2 ((X.barriers c).take (last+1)) := by
  refine CtaBarrier.first_generation_protocol hX.ctaBar hc hAt hGen ?_
  intro g j _ hG
  obtain ⟨hWarp, pc, _, hBar⟩ := allocationGenerationZeroSource hp hX hG
  exact ⟨Finset.mem_range.mpr hWarp, pc, .sync, hBar⟩

/-- The first barrier-2 generation records each lane of each participating warp, including
lanes whose exits are already recorded. -/
theorem allocationGenerationZeroMember {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hw : warpIndex l g < 13) (hDone : CtaBarDone l X (g/l.block) 2) :
    ∃ j pc, pc ∈ allocationEntrySites ∧ X.IsBarrier (g,j) 2 (some 416) pc ∧
      CtaBarK l X (g,j) 2 := by
  obtain ⟨finish, hFinished⟩ := hDone
  have hFin := hFinished
  obtain ⟨_, _, _, _, hAt, _, hGen, _⟩ := hFin
  have hProto := allocationProtocolPrefix hp hX (NamedBar.cta_lt hg) hAt hGen
  obtain ⟨j, hSource⟩ := CtaBarrier.first_generation_member hX hg (allocationBarrierShape hp)
    (Finset.mem_range.mpr hw) hFinished hProto (fun _ _ he => by
      obtain ⟨i, hLt, pc, _, hBar⟩ := allocationBeforeParticipantExit hp hX hg hw he
      exact ⟨i, hLt, pc, some 416, hBar⟩)
  obtain ⟨_, pc, hSite, hBar⟩ := allocationGenerationZeroSource hp hX hSource
  exact ⟨j, pc, hSite, hBar, hg, ⟨some 416, pc, hBar⟩, hSource⟩

/-- For a later actual event, an earlier returned allocation wait identifies the matching
generation-zero wait, which must also precede that event. -/
theorem allocationGenerationZeroBefore {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j i pc : Nat} (hg : g < l.threads) (hw : warpIndex l g < 13) (hi : i < j)
    {e : Event} (he : X.get (g,j) = some e) (hWait : X.IsBarrier (g,i) 2 (some 416) pc) :
    CtaBarDone l X (g/l.block) 2 ∧
      ∃ k < j, CtaBarK l X (g,k) 2 := by
  have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hDone := CtaBarrier.first_generation_released_of_returned hX (by decide) hWait
    (by omega : i+1 < (X.tr g).length)
  obtain ⟨k, _, _, _, hk⟩ := allocationGenerationZeroMember hp hX hg hw hDone
  have hBefore : k ≤ i := by
    by_contra hn
    exact CtaBarrier.not_generationZero_after_sync hX (by decide) (by omega) hWait hk.2.2
  exact ⟨hDone, k, by omega, hk⟩

end PTX.Kernels.TmlFa4Fwd.Mma
