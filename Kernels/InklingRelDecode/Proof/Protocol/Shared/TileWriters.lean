-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.PairRead
public import Kernels.InklingRelDecode.Proof.Lib.TensorSites
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyFoot
import Kernels.InklingRelDecode.Proof.Prologue.Export.CopyFoot
import Lemmas.Flow.NotTensor
import Lemmas.Flow.NotBulk
import Lemmas.Flow.OpPcsFast

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Lib

/-- All twenty tensor load sites select the launch's KV descriptor. -/
theorem tensor_map {Q L m X g k pc addr sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨pc,.tensorIssue addr sp⟩) :
    (⟨sp.outer,sp.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨1,mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩ := by
  rcases tensor_issue_site hX he with preload|worker
  · exact (Prologue.Export.preload_map hp hX he preload).1
  · exact (Loader.Export.copy_map hp hX he worker).1

/-- A tensor byte in either publication region would have to originate
from one of the twelve preload sites. This includes all CTAs and map addresses. -/
theorem preload_writer {Q L m X l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (write : TensorByte X l)
    (lo : L.sharedBase+196608≤l.addr) (hi : l.addr<L.sharedBase+213340) :
    ∃ g k pc addr sp x y z, X.get (g,k)=some ⟨pc,.tensorIssue addr sp⟩ ∧ pc ∈ preloadPcs ∧
      TensorCopy.writeLoc sp x y z=some l := by
  obtain ⟨⟨g,k⟩,addr,sp,⟨pc,event⟩,x,y,z,byte⟩ := write
  rcases tensor_issue_site hX event with pro|worker
  · exact ⟨g,k,pc,addr,sp,x,y,z,event,pro,byte⟩
  · have miss := Loader.Export.copy_byte hp hX event worker byte
    omega

/-- Tensor-copy destinations of every CTA miss both shared publications. -/
theorem outside_tiles {Q L m X l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (lo : L.sharedBase+196608≤l.addr) (hi : l.addr<L.sharedBase+213340) : ¬TensorByte X l := by
  intro write
  obtain ⟨_,_,_,_,_,_,_,_,event,site,byte⟩ := preload_writer hp hX write lo hi
  have miss := (Prologue.Export.preload_byte hp hX event site byte).2
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
