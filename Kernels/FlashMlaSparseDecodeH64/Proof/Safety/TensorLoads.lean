-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Tensor
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorLoadSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputControl
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputTrace

@[expose] public section

/-! # Scalar values and accessible backing for the issued tensor transfers -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Wg0 MmaDataTrace

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem gather_fill {s : TensorCopy.Spec} {base count stride : Nat}
    {cls : TensorDescriptor.AllocationClass}
    (hDesc : (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨1, (encodeKv base count stride cls).fourRows⟩) :
    s.descriptor.fill = .zero ∧ s.descriptor.format = .u32 :=
  ⟨congrArg (fun (p : Σ n, TensorDescriptor.Descriptor n) => p.2.fill) hDesc,
    congrArg (fun (p : Σ n, TensorDescriptor.Descriptor n) => p.2.format) hDesc⟩

private theorem load_fill {g : Nat} {s : TensorCopy.Spec} (h : TensorLoadSources.Load P L g s) :
    s.descriptor.fill = .zero ∧ (s.descriptor.format = .bf16 ∨ s.descriptor.format = .u32) := by
  cases h with
  | query tile hSpec =>
    rw [hSpec]
    exact ⟨rfl, .inl rfl⟩
  | main hDesc =>
    obtain ⟨hm, hf⟩ := gather_fill hDesc
    exact ⟨hm, .inr hf⟩
  | extra _ hDesc =>
    obtain ⟨hm, hf⟩ := gather_fill hDesc
    exact ⟨hm, .inr hf⟩

/-- Every produced tensor-load byte has a scalar value, including gather zero fills. -/
theorem no_tensorUnsafe (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ TensorUnsafe X := by
  rintro ⟨⟨g, i⟩, o, slot, content, hObs, hw, hByte⟩
  obtain ⟨_, hIssue⟩ := (hX.tensor (g, i) o hObs).1
  obtain ⟨hFill, hFmt⟩ := load_fill (TensorLoadSources.load hpre hX hs ht hIssue)
  have hWrite := (hX.tensor (g, i) o hObs).2.1.writes slot content hw
  cases hAddr : o.spec.globalAddress slot with
  | some addr =>
    simp only [TensorCopy.source, hAddr] at hWrite
    obtain ⟨_, _, rfl⟩ := hWrite
    cases hByte
  | none =>
    simp only [TensorCopy.source, hAddr] at hWrite
    rw [hWrite, hFill] at hByte
    rcases hFmt with hFmt | hFmt <;>
      simp [hFmt, TensorCopy.Content.byte, TensorCopy.zeroValue] at hByte

private theorem gather_backing {s : TensorCopy.Spec} {base count stride : Nat}
    {cls : TensorDescriptor.AllocationClass}
    (hDesc : (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨1, (encodeKv base count stride cls).fourRows⟩)
    (hBacking : cls = .large → TensorLargeBacking L mem0 base)
    (hMissing : TensorBackingMissing L mem0 s.descriptor s.origin s.rows) : False := by
  have hClass : s.descriptor.allocationClass = cls :=
    congrArg (fun (p : Σ n, TensorDescriptor.Descriptor n) => p.2.allocationClass) hDesc
  have hBase : s.descriptor.base = base :=
    congrArg (fun (p : Σ n, TensorDescriptor.Descriptor n) => p.2.base) hDesc
  exact hMissing.2.2 (hBase ▸ hBacking (hClass.symm.trans hMissing.1))

/-- Query and output tiles are in bounds, and every enabled large-class gather has backing. -/
theorem no_tensorAllocationUnsafe (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ TensorAllocationUnsafe L mem0 X := by
  rintro ⟨⟨g, i⟩, ⟨address, s, hi, hMissing⟩ | ⟨address, s, hi, hMissing⟩ | ⟨address, s, hi, _⟩⟩
  · have hg := Frame.lt_of_get hX hi.choose_spec
    cases TensorLoadSources.load hpre hX hs ht hi with
    | query tile hSpec =>
      rw [hSpec] at hMissing
      exact query_no_oob hpre hg tile hMissing.2.1
    | main hDesc => exact gather_backing hDesc hpre.kvBacking hMissing
    | extra hExtra hDesc => exact gather_backing hDesc (hpre.extraKvBacking hExtra) hMissing
  · have he := hi.choose_spec
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, tile, hd, hSite⟩ := GlobalWrites.outputTile_site hs hX ht hi
    have hWarp := Wg0OutputControl.outputWarp hX (hs g hg).machine he hd hSite
    have hSpec := (Wg0OutputTrace.tileSpec hpre hX (hs g hg).machine hi hd hSite).2
    rw [hSpec] at hMissing
    exact output_no_oob hWarp (Wg1Mma.queryOf_lt hpre hg) (Wg1Mma.eOf_lt_b hpre) tile hMissing.2.1
  · exact TensorLoadSources.no_tensor_prefetch hX hi

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
