-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.ARead
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.QkStore
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PvStore
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccessInfo
import Kernels.InklingRelDecode.Proof.Lib.NoEvents

@[expose] public section

/-! # Tensor Memory reads are ordered with the writes of their cells

An accumulator read of an MMA is a write of the same cell (`mma_read_write`), so it is ordered
with every other write as the writes are (`Tmem.writes_safe`): the MMA's side of an order of two
writes is a read order (`ReadBefore .acc`). An A read is a PV MMA's of the probabilities
(`a_read_order`). The kernel has no `tcgen05.shift`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.TcMma

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- An MMA's write ordered before another write orders its accumulator read before it. -/
theorem acc_order {r w : EvId} {pc d s a mask} (hr : X.get r = some ⟨pc,.tc (.mma d s a mask)⟩)
    (h : WriteBefore L X r w) : ReadBefore L X .acc r w := by
  rcases h with (h | h) | ⟨⟨_,_,_,pc',h⟩,-⟩ | ⟨-,-,_,_,_,_,_,⟨pc',h⟩,-⟩
  · exact .inr (.inl h)
  · exact .inr (.inr h)
  · rw [hr] at h
    cases h
  · rw [hr] at h
    cases h

/-- **No Tensor Core read of a Tensor Memory cell is unordered with a write of it.** -/
public theorem reads_safe (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) : ¬ ReadsUnsafe L X := by
  have hws : WritesSafe L X := not_not.mp
    (writes_safe hp hX hf base (qk_store_order hp hX hf safe base rows init)
      (pv_store_order hp hX hf safe base rows init))
  refine fun hn => hn (readsSafe_iff.mpr ⟨fun r w cell hr hw => ?_,
    fun r w cell hr hw => a_read_order hp hX hf safe base rows init hr hw,
    fun r w cell hr _ => ?_⟩)
  · have hrw := mma_read_write hp hX hf base hr
    obtain ⟨d,s,mask,row,col,⟨pc,he⟩,-⟩ := hr
    rcases hws r w cell (.inl hrw) hw with h | h | h
    · exact .inl h
    · exact .inr (.inr (acc_order he h))
    · exact .inr (.inl h)
  · obtain ⟨sp,hsp,-⟩ := hr
    exact (no_shift hX _ _ hsp).elim

end PTX.Kernels.InklingRelDecode.Proof.Tmem
