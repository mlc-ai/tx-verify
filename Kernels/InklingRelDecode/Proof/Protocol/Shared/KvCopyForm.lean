-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.KvCopyForm
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.TensorSource
import Kernels.InklingRelDecode.Proof.Prologue.Export.PreloadSlab
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyOrigin
import Kernels.InklingRelDecode.Proof.Lib.TensorSites
import Lemmas.Tensor.TensorCompleteConsistentRead

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX

/-- **Every tensor load of the kernel is the copy of a box of a slab that exists**, into its own
CTA at a 1024-aligned destination: the 12 preloads of the prologue and the 8 copies of the
loader. -/
theorem kv_copy_form {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) : Iface.KvCopyForm Q L X := by
  intro g k pc a sp he
  have slab : Lib.KvSlab Q (g / L.block) sp := by
    rcases Lib.tensor_issue_site hX he with site | site
    · exact Prologue.Export.preload_slab hp hX hf he site
    · exact Loader.Export.copy_slab hp hX hf he site
  obtain ⟨dst, bar, r, s, kvh, isV, hh, hr, hs, hk, hV, hH, hD, rfl⟩ := slab
  exact ⟨r, s, kvh, isV, hh, dst, bar, hr, hs, hk, hV, hH, hD, rfl⟩

/-- **The source bytes of every tensor load are input bytes**: a source address of a slot of the
box is the address of an element of the slab's rows. -/
theorem tensor_input_bytes {Q L m X} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) : TensorInputBytes Q X := by
  rintro i addr s ⟨pc, he⟩ slot a hsrc
  obtain ⟨g, k⟩ := i
  obtain ⟨r, sl, kvh, isV, hh, dst, bar, hr, hs, hk, hV, hH, -, hsp⟩ := kv_copy_form hp hX hf he
  have hsp' : s = Lib.kvCopySpec Q (g / L.block) (kvh * Q.headCols + 128 * isV + 64 * hh)
    (Q.page r sl * Q.pageRows + kvh * Q.headRows) dst bar := hsp
  subst hsp'
  have loc : TensorCopy.readLoc (Lib.kvCopySpec Q (g / L.block)
      (kvh * Q.headCols + 128 * isV + 64 * hh)
      (Q.page r sl * Q.pageRows + kvh * Q.headRows) dst bar)
      slot.1.val slot.2.1.val slot.2.2.val = some ⟨.global, 0, a⟩ := by
    rw [TensorCopy.readLoc_source]
    rw [TensorCopy.slotAt_self slot]
    simp only [Option.bind_some]
    rw [hsrc]
  obtain ⟨-, -, h⟩ := Lib.kvCopy_readLoc_input hp hr hs hk hV hH loc
  exact h

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
