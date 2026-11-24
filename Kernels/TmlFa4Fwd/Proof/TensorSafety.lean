-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.InputCopies
public import Kernels.TmlFa4Fwd.Proof.LoaderInputDescriptors
public import Kernels.TmlFa4Fwd.Proof.MbarAddressClosure
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Lemmas.Flow.TcTmpl
public import Lemmas.TensorStore.TensorStoreThread
public import Kernels.TmlFa4Fwd.Proof.Thread.TensorForms
import Kernels.TmlFa4Fwd.Proof.OutputStoreFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow

/-- Loader copies all use whole writes. -/
theorem noMaskedRangeUnalloc {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) : ¬ MaskedRangeUnalloc m X := by
  apply not_maskedRangeUnalloc_of_none
  intro i s mask hi
  rw [(actualCopyShape hX hi).whole]
  intro h
  cases h

private theorem noTensorUnsafeOfFormat {l : Launch} {m : Mem0} {A : List Assumption}
    {X : Execution} (hX : Consistent l kernel A m X)
    (hFormat : ∀ i addr spec, X.TensorIssue i addr spec →
      spec.descriptor.fill = .zero ∧ spec.descriptor.format = .bf16) :
    ¬ TensorUnsafe X := by
  rintro ⟨i, o, slot, content, ho, hw, hBad⟩
  obtain ⟨⟨address, hi⟩, hok, _⟩ := hX.tensor i o ho
  obtain ⟨hFill, hFormat⟩ := hFormat i address o.spec hi
  have he := hok.writes slot content hw
  unfold TensorCopy.source at he
  cases hLoc : o.spec.globalAddress slot with
  | none =>
    simp only [hLoc, hFill, hFormat] at he
    subst content
    simp [TensorCopy.Content.byte, TensorCopy.zeroValue] at hBad
  | some a =>
    rw [hLoc] at he
    obtain ⟨b, _, rfl⟩ := he
    cases hBad

/-- Every actual input copy writes a scalar byte, both for backed operands and for zero fill. -/
theorem noActualTensorUnsafe {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) : ¬ TensorUnsafe X := by
  apply noTensorUnsafeOfFormat hX
  intro i addr s hi
  obtain ⟨site, _, hDesc, _⟩ := Loader.actualInputDescriptor hp hX hi
  have hFill := congrArg (fun d : (n : Nat) × TensorDescriptor.Descriptor n => d.2.fill) hDesc
  have hFmt := congrArg (fun d : (n : Nat) × TensorDescriptor.Descriptor n => d.2.format) hDesc
  change s.descriptor.fill = (Loader.inputMap p (Loader.inputSite site)).fill at hFill
  change s.descriptor.format = (Loader.inputMap p (Loader.inputSite site)).format at hFmt
  rw [hFill, hFmt]
  cases h : (Loader.inputSite site).bias <;> simp [Loader.inputMap, h, Params.qMap, Params.biasMap]

/-- The actual Q and Bias maps have the backing supplied by the launch. -/
theorem actualInputBacking {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {s : TensorCopy.Spec} (hi : X.TensorIssue i addr s) :
    ¬ TensorBackingMissing l m s.descriptor s.origin s.rows := by
  intro hBad
  obtain ⟨site, _, hDesc, _⟩ := Loader.actualInputDescriptor hp hX hi
  have hClass := congrArg
    (fun d : (n : Nat) × TensorDescriptor.Descriptor n => d.2.allocationClass) hDesc
  have hBase := congrArg (fun d : (n : Nat) × TensorDescriptor.Descriptor n => d.2.base) hDesc
  apply hBad.2.2
  change s.descriptor.base = (Loader.inputMap p (Loader.inputSite site)).base at hBase
  have hLarge := hBad.1
  change s.descriptor.allocationClass = (Loader.inputMap p (Loader.inputSite site)).allocationClass
    at hClass
  rw [hBase]
  rw [hClass] at hLarge
  cases h : (Loader.inputSite site).bias
  · have hMap := hp.maps 9 p.qMapAddress ⟨2, p.qMap⟩ (by simp)
    simpa [Loader.inputMap, h] using hMap.2.2.2.2.2
      (by simpa [Loader.inputMap, h] using hLarge)
  · have hMap := hp.maps 11 p.biasMapAddress ⟨2, p.biasMap⟩ (by simp)
    simpa [Loader.inputMap, h] using hMap.2.2.2.2.2
      (by simpa [Loader.inputMap, h] using hLarge)

/-- Both the ordinary KV copies and the O stores use plain write operations. -/
theorem noTensorStoreUnsafe {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) : ¬ TensorStoreUnsafe A X := by
  rintro (⟨i, o, red, _, _, ho, hRed, _⟩ | hCopy)
  · obtain ⟨⟨address, hi⟩, _⟩ := hX.store i o ho
    change o.spec.reduce = some red at hRed
    rw [(Thread.actualTensorStoreForm hX hi).2.2] at hRed
    cases hRed
  · exact TensorStore.not_copyReduceNoRule_of_none
      (fun i s hi red => by rw [(actualCopyShape hX hi).whole]; intro h; cases h) hCopy

/-- Every actual tensor transfer has its ABI map backing, even if a coordinate is out of bounds. -/
theorem noActualTensorAllocationUnsafe {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    ¬ TensorAllocationUnsafe l m X := by
  rintro ⟨i, ⟨address, s, hi, hBad⟩ | ⟨address, s, hi, hBad⟩ | ⟨address, s, hi, _⟩⟩
  · exact actualInputBacking hp hX hi hBad
  · obtain ⟨_, hDesc⟩ := OutputWarp.storeDescriptor hp hX hi
    have hClass := congrArg
      (fun d : (n : Nat) × TensorDescriptor.Descriptor n => d.2.allocationClass) hDesc
    have hBase := congrArg (fun d : (n : Nat) × TensorDescriptor.Descriptor n => d.2.base) hDesc
    have hLarge := hBad.1
    change s.descriptor.allocationClass = p.oMap.allocationClass at hClass
    rw [hClass] at hLarge
    apply hBad.2.2
    change s.descriptor.base = p.oMap.base at hBase
    rw [hBase]
    have hMap := hp.maps 10 p.oMapAddress ⟨3, p.oMap⟩ (by simp)
    exact hMap.2.2.2.2.2 hLarge
  · exact Thread.noTensorPrefetch hX hi

end PTX.Kernels.TmlFa4Fwd
