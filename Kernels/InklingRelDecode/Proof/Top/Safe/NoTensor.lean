-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
import Kernels.InklingRelDecode.Proof.Protocol.Shared.TileWriters

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

/-- Every KV element, including a descriptor fill, has a scalar byte. -/
theorem Safe.noTensor (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) : ¬ TensorUnsafe X := by
  rintro ⟨i,obs,slot,content,atIssue,wrote,missing⟩
  obtain ⟨⟨_,pc,event⟩,valid,_⟩ := hX.tensor i obs atIssue
  have descriptor := Protocol.Shared.tensor_map hp hX event
  have mode := congrArg (fun d : (n : Nat) × TensorDescriptor.Descriptor n =>
    (d.2.fill,d.2.format)) descriptor
  obtain ⟨fill,fmt⟩ := Prod.mk.inj mode
  change obs.spec.descriptor.fill=.zero at fill
  change obs.spec.descriptor.format=.bf16 at fmt
  have src := valid.writes slot content wrote
  unfold TensorCopy.source at src
  cases h : obs.spec.globalAddress slot with
  | some addr =>
    simp only [h] at src
    obtain ⟨_,_,rfl⟩ := src
    cases missing
  | none =>
    simp only [h,fill] at src
    subst content
    simp [TensorCopy.Content.byte,fmt,TensorCopy.zeroValue] at missing

end PTX.Kernels.InklingRelDecode.Proof.Top
