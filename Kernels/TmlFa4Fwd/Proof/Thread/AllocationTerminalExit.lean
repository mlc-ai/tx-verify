-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierRelease
import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocatorExit
import Kernels.TmlFa4Fwd.Proof.AllocationBarrierGeneration
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
import Kernels.TmlFa4Fwd.Flow.Code.Part120
import Kernels.TmlFa4Fwd.Flow.Code.Part121
import Kernels.TmlFa4Fwd.Flow.Code.Part143
import Lemmas.Step.Issue
import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Prologue Epilogue Mma

noncomputable section

/-- A recorded allocator event yields the semantic deallocation observation. -/
theorem Deallocation.ofKind {X : Execution} {d : EvId} {e : Event}
    {group : CtaGroup} {dst : Option Loc} {base columns : Nat} (he : X.get d = some e)
    (hk : e.kind = .tc (.resource group dst (.dealloc base columns))) : Deallocation X d := by
  obtain ⟨site, kind⟩ := e
  cases hk
  exact Deallocation.of_decoded he

/-- The actual deallocation in a CTA means its exiting participant's final arrival has
already been recorded, so the arrival can return. -/
theorem FinalAllocationArrival.releasedOfDeallocation
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {d : EvId} (hArrival : FinalAllocationArrival X (g,j) .arrive)
    (hCta : g/l.block = d.1/l.block) (hLast : j+1 = (X.tr g).length)
    (hRelease : Deallocation X d) : Step.Released l X g := by
  obtain ⟨site, base, columns, group, dst, hd⟩ := hRelease.decoded
  obtain ⟨wait, _, key, _, _, hKey, hDone, hWait⟩ := deallocationFollowsFinalSync hp hX hd
  have hFinal : FinalAllocationArrival X (d.1,wait) .sync :=
    FinalAllocationArrival.of_decoded (by decide) hWait
  have hOrdinal := finalAllocationArrivalOrdinal hp hX hFinal
  let sources := allocationBarrierSources hp hX
  let shape := allocationBarrierShape hp
  have hKey' : key = 18 := by
    have h := sources.arrival_key hX shape hWait hKey.arrival
    change key = 2 + 16 * observedBarrierOrdinal X (d.1,wait) 2 at h
    rwa [hOrdinal] at h
  subst key
  have hRel : CtaBarrier.Released l.block (X.barriers (g/l.block)) 2
      (observedBarrierOrdinal X (g,j) 2) := by
    rw [finalAllocationArrivalOrdinal hp hX hArrival, hCta]
    exact hDone
  have hArrivalKey := barrierArrivalKeyOfReleased hX sources shape hArrival.arrival hRel
  obtain ⟨_,_,he⟩ := hArrival.decoded
  constructor
  intro site kind hGet _
  have hJ : (X.tr g).length - 1 = j := by omega
  rw [hJ] at hGet ⊢
  rw [he] at hGet
  cases hGet
  exact NamedBar.ready_of_arrivalK hX.ctaBar he hArrivalKey

/-- At a ready exit instruction the recorded trace in a maximal execution contains that exit. -/
theorem exitAtMaximalCursor {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) {g j : Nat} (hg : g < l.threads)
    (hPos : 0 < j) (hBound : j ≤ (X.tr g).length) {t u : TState} {o : Option TState}
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take j) (some t))
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop j) o)
    (hn : Next kernel Assumptions.all l g t u .exit)
    (hRelease : j = (X.tr g).length → Step.Released l X g) :
    X.get (g,j) = some ⟨u.pc,.exit⟩ := by
  have hMore : j < (X.tr g).length := by
    by_contra! hLe
    have hj := Nat.le_antisymm hBound hLe
    have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hj; omega
    rw [List.take_of_length_le hLe] at hPrefix
    have he : EStep kernel Assumptions.all l g u ⟨u.pc,.exit⟩ none := ⟨_,hn.stop,rfl,rfl⟩
    exact hMax.not_grows (Step.plain_counted_extension hMax.1 hg (.inl hStarted)
      (hRelease hj) hPrefix hn.steps he trivial rfl nofun nofun nofun rfl
      (hMax.1.tmemPairResult.snoc_not_wr nofun)
      (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl)))
  have hNonempty : (X.tr g).drop j ≠ [] :=
    fun h => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp h)
  have hs : Stops kernel Assumptions.all l g u := ⟨_,hn.stop⟩
  have hEvent : (X.tr g).drop j = [⟨u.pc,.exit⟩] := by
    generalize hEv : (X.tr g).drop j = events at hTail hNonempty ⊢
    cases hTail with
    | nil => exact (hNonempty rfl).elim
    | step hLocal he _ =>
      obtain rfl := stop_unique hLocal hn.steps (stops_of_estep he) hs
      obtain ⟨_, hOut, hFire⟩ := he
      rw [hn.stop] at hOut
      obtain rfl := Out.ev.inj hOut
      cases hFire.2
    | last hLocal he =>
      obtain rfl := stop_unique hLocal hn.steps (stops_of_estep he) hs
      obtain ⟨_, hOut, hFire⟩ := he
      rw [hn.stop] at hOut
      obtain rfl := Out.ev.inj hOut
      rw [hFire.1]
  have he : ((X.tr g).drop j)[0]? = some ⟨u.pc,.exit⟩ := by rw [hEvent]; rfl
  rwa [List.getElem?_drop, Nat.add_zero] at he

end
end PTX.Kernels.TmlFa4Fwd.Thread
