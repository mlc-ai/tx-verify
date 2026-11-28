-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.Readers
public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX

/-- Each pending operand read already lies below the scratch words and
initializers. The descriptor fixes its address before an operand is observed. -/
theorem operand_byte {Q L m X i side j l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (foot : X.MmaFootprint i side j l) :
    l.space=.shared ∧ L.sharedBase≤l.addr ∧ l.addr<L.sharedBase+212992 := by
  rcases foot with ⟨dst,s,acc,mask,⟨pc,get⟩,byte⟩|⟨c,_,_,cp,_⟩
  · obtain ⟨g,k⟩ := i
    obtain ⟨_,tile⟩ := Mma.Export.operands hp hX hf get
    cases side
    · obtain ⟨sp,lo,hi⟩ := tile .a j l byte
      exact ⟨sp,by omega,hi⟩
    · obtain ⟨sp,lo,hi⟩ := tile .b j l byte
      exact ⟨sp,lo,by omega⟩
  · exact (Lib.no_cp hX i c cp).elim

/-- No memory intent, pending or performed, can overlap any of the initializer
bytes or the preceding alignment gap. -/
theorem arena_clear {Q L m X ref a w l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (intent : X.Intent ref a w) (cov : a.Covers l) (sp : l.space=.shared)
    (lo : L.sharedBase+213008≤l.addr) (hi : l.addr<L.sharedBase+213336) : False := by
  cases w with
  | true => exact no_arena_write hp hX intent cov sp lo hi
  | false =>
    obtain ⟨u,side,j,rfl⟩ := arena_reader hp hX intent cov sp lo hi
    obtain ⟨_,size,foot⟩ := intent
    have bounds := operand_byte hp hX hf foot
    obtain ⟨_,_,_,end'⟩ := cov
    omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
