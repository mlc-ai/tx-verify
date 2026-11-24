-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.OrdinaryAccessAllocation
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TensorAccessAllocation
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaAccessWindow
import Lemmas.Protocol.NamedBarSources

public section

/-! # Every memory access is allocated at launch -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {i : EvId} {a : Acc} {l : Loc}

private theorem mma_byte_allocated (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X)
    {isB : Bool} {index : Nat} (hf : X.MmaFootprint i isB index a.loc)
    (hSize : a.size = 1) (hc : a.Covers l) : mem0 l ≠ none := by
  obtain ⟨hg, hSpace, hOwner, hLo, hHi⟩ := MmaAccessWindow.footprint hpre hX hs ht hf
  obtain ⟨hsp, hcta, hlo, hhi⟩ := hc
  let off := l.addr - L.sharedBase
  have hOff : off < sharedBytes := by dsimp [off]; omega
  have hAddr : l.addr = L.sharedBase + off := by dsimp [off]; omega
  have hLoc : l = ⟨.shared, ctaOf L i.1, P.sharedBase + off⟩ := by
    rw [← hpre.sharedBase]
    cases l
    rw [Loc.mk.injEq]
    exact ⟨hsp.trans hSpace, hcta.trans hOwner, hAddr⟩
  rw [hLoc]
  exact hpre.sharedAllocated _ (NamedBar.cta_lt hg) _ hOff

private theorem async_allocated (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X)
    {p : AsyncCopy.Part} (hm : X.MemTouches (.async i p) a) (hc : a.Covers l) :
    mem0 l ≠ none := by
  have hf : X.AsyncFootprint i p a := by
    rcases hm with ⟨_, _, h⟩ | ⟨_, _, h, _⟩
    · exact h
    · cases h
  cases p <;> try contradiction
  case readCopy =>
    rcases hf with ⟨_, h, _⟩ | h
    · exact (GlobalWrites.no_copy hX h).elim
    · exact (GlobalWrites.no_bulk_prefetch hX h).elim
  case readLoad => exact tensor_load_read_allocated hpre hX hs ht hm hc
  case readStore => exact tensor_store_read_allocated hpre hX hs ht hm hc
  case readPrefetch => exact (tensor_prefetch_read_allocated hX hm).elim
  case writeCopy =>
    obtain ⟨_, h, _⟩ := hf
    exact (GlobalWrites.no_copy hX h).elim
  case writeLoad => exact tensor_load_write_allocated hpre hX hs ht hm hc
  case writeStore => exact tensor_store_write_allocated hpre hX hs ht hm hc
  case writeCta =>
    obtain ⟨_, _, h, _⟩ := hf
    exact (GlobalWrites.no_clc hX h).elim
  case writeElem =>
    obtain ⟨_, h, _⟩ := hf
    exact (GlobalWrites.no_copy hX h).elim
  case oldStore => exact tensor_store_old_allocated hpre hX hs ht hm hc
  case oldElem =>
    obtain ⟨_, _, h, _⟩ := hf
    exact (GlobalWrites.no_copy hX h).elim
  case mmaRead => exact mma_byte_allocated hpre hX hs ht hf.2 hf.1 hc

/-- No ordinary, asynchronous or barrier access touches an unallocated byte. -/
theorem no_unalloc (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ Unalloc mem0 X := by
  rintro (⟨ref, a, l, hm, hc, he⟩ | ⟨i, m, l, hu, hc, he⟩)
  · cases ref with
    | thread i => exact ordinary_access_allocated hpre hX hs ht hm hc he
    | async i p => exact async_allocated hpre hX hs ht hm hc he
  · exact mbar_allocated hpre hX hs ht hu hc he

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
