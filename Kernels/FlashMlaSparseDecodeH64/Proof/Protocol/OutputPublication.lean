-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierTrace
public import Lemmas.Protocol.NamedBarSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxBarriers

@[expose] public section

/-! # The output stage's generic-to-async publication -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputPublication

open PTX

private instance : Fact kernel.NoBarArrive := ⟨by
  unfold Kernel.NoBarArrive
  decide +kernel⟩

/-- The four softmax warps participate in the barrier that publishes output tiles. -/
def stagingWarps : Finset Nat := Finset.range 4

theorem shape {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    NamedBar.Shape L (some 128) stagingWarps 9 := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · rw [hpre.block]
    rfl
  · intro w hw
    rw [hpre.block]
    exact Finset.mem_range.mp hw |>.trans_le (by decide)

/-- All arrivals of the output staging barrier use its 128-thread operand in the four
softmax warps, including arrivals after a dismissal. -/
theorem actual_sources {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    NamedBar.Sources L X (some 128) stagingWarps 9 := by
  rintro ⟨g, k⟩ site count ⟨mode, he⟩ _
  obtain ⟨hw, hc, _⟩ := MachineTracking.actual_bar9 hpre hX hs he
  refine ⟨?_, hc⟩
  simpa only [stagingWarps, Finset.mem_range, warpOf, tidOf_eq hpre, hpre.block] using hw

/-- All arrivals of the output staging barrier use its 128-thread operand in the four softmax
warps. -/
theorem sources {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) :
    NamedBar.Sources L X (some 128) stagingWarps 9 := by
  rintro ⟨g, k⟩ site count ⟨mode, he⟩ hg
  obtain ⟨_, _, _, hw, hc, _⟩ := Wg0BarrierTrace.bar9_at hpre hX (hs g hg) ht he rfl
  refine ⟨?_, hc⟩
  simpa only [stagingWarps, Finset.mem_range, warpOf, tidOf_eq hpre, hpre.block] using hw

private theorem store_before_fence {L : Launch} {X : Execution} {writer store fence : Nat}
    (hf : X.IsProxyFence (writer, fence) (.async (some (.shared .cta))) none)
    (hbefore : store < fence) : baseCausality L X (writer, store) (writer, fence) := by
  obtain ⟨site, hf⟩ := hf
  have hlen : fence < (X.tr writer).length := (List.getElem?_eq_some_iff.mp hf).1
  apply Relation.TransGen.single
  apply Or.inl
  refine ⟨rfl, hbefore, hlen, ?_⟩
  simp [SameAccess, hf, Event.acc]

/-- The writer's proxy fence orders its staging write before the tensor issue after the matching
tile barrier on the issuer. Barrier matching uses the two actual source ordinals. -/
theorem proxyBefore {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {writer issuer store fence writerBar issuerBar issue site site' : Nat} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hcta : SameCta L writer issuer)
    (hl : l.space = .shared ∧ l.cta = writer / L.block)
    (hf : X.IsProxyFence (writer, fence) (.async (some (.shared .cta))) none)
    (hwb : X.IsBarrier (writer, writerBar) 9 (some 128) site)
    (hib : X.IsBarrier (issuer, issuerBar) 9 (some 128) site')
    (hordinal : ((X.tr writer).take writerBar).countP (Execution.isBarId 9) =
      ((X.tr issuer).take issuerBar).countP (Execution.isBarId 9))
    (hsf : store < fence) (hfb : fence < writerBar) (hbi : issuerBar + 1 < issue)
    (hi : issue < (X.tr issuer).length) : ProxyBefore L X (writer, store) (issuer, issue) l := by
  have hc : SameCluster L writer issuer :=
    ⟨hcta.1, hcta.2.1, congrArg L.clusterOfCta hcta.2.2⟩
  refine ⟨(writer, fence), some (.shared .cta), none, hf, hcta.1, hl, hc,
    store_before_fence hf hsf, ?_⟩
  exact (sources hpre hX hs ht).same_ordinal_baseCausality hX (shape hpre) hcta hwb hib
    (Nat.lt_trans hbi hi) hordinal hfb (by omega) hi

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputPublication
