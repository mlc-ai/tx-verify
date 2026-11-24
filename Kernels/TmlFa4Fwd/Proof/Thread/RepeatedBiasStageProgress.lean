-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasReturnProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasBarrierProgress
public import Kernels.TmlFa4Fwd.Proof.Protocol.NamedBarriers
public import Lemmas.Step.CtaBarFinishExit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction Thread

variable {p : Params}

/-- Once the stage's actual participants have arrived at the same Bias
generation, every pending lane can resume in one common maximal history. -/
theorem biasStageReleaseOfMaximal {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {cta : Nat}
    (hCta : cta < l.grid) (stage : Fin 2) (generation : Nat)
    (hArrivals : ∀ lane < l.block, lane / 32 ∈ biasParticipants stage →
      ∃ i, BarrierArrival X (cta*l.block+lane,i) (11+stage.val) (some 128) .sync ∧
        observedBarrierOrdinal X (cta*l.block+lane,i) (11+stage.val) = generation) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.objects = X.objects ∧
      Y.MemWrites = X.MemWrites ∧
      ∀ g < l.threads, g/l.block = cta →
        BarrierArrival X (g,(X.tr g).length-1) (11+stage.val) (some 128) .sync →
        observedBarrierOrdinal X (g,(X.tr g).length-1) (11+stage.val) = generation →
        Step.Released l Y g := by
  have hFault (Z) (hZ : Consistent l kernel Assumptions.all m Z) (_ : Z.tr = X.tr)
      (hWrites : Z.MemWrites = X.MemWrites) : ¬ CtaBarFault l Z := by
    apply Protocol.noActualNamedBarrierFault hp hZ
    intro i hi k hk ref a bytes hWrite
    exact (hFrame.metadataProtected hp).1 i hi k hk ref a bytes (hWrites ▸ hWrite)
  obtain ⟨Y,hY,hTrace,hWrites,hObjects,hRelease⟩ :=
    NamedBar.sync_generation_release_preserving_objects hMax Assumptions.wfStep.ctaHistory hFault
      (biasBarrierShape hp stage) (biasBarrierSources hp hMax.1 stage) hCta (G := generation)
      (by
        intro lane hLane hMember
        obtain ⟨index,⟨⟨pc,kind⟩,hEvent,hKind⟩,hRank⟩ := hArrivals lane hLane hMember
        change kind = _ at hKind
        subst kind
        exact ⟨index,pc,.sync,hEvent,hRank⟩)
  refine ⟨Y,hY,hTrace,hObjects,hWrites,?_⟩
  intro g hg hCta' ⟨⟨pc,kind⟩,hEvent,hKind⟩ hRank
  change kind = _ at hKind
  subst kind
  exact hRelease hg hCta' hEvent hRank

end PTX.Kernels.TmlFa4Fwd.Softmax
