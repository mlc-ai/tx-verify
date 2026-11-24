-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.NoEvents
public import Lemmas.Protocol.RegionOrderExcept
public import Kernels.InklingRelDecode.Proof2.Lib.Regions

@[expose] public section

/-!
# The memory of the kernel, region by region, and allocation

A CTA's shared window (`sharedBytes = 213340` bytes from `L.sharedBase`) holds, by offset:

* `[0, 4)`: the Tensor Memory base word. `tcgen05.alloc` writes it, every thread reads it, and
  then K slot 0 is overwritten.
* `[4, 196608)`: the K ring (`[0, 98304)`, three slots of 32768) and the V ring (`[98304, 196608)`).
  TMA copies write it, MMAs read it.
* `[196608, 212992)`: the Q tile (16384). Default-partition stores write it, MMAs read it.
* `[212992, 213000)`: `(num_pre, num_iters)`. Default-partition stores write it, the loader and the
  MMA warp read it.
* `[213000, 213008)`: the second half of the softmax region's min-exchange scratch. The scratch
  is four words, `[212992, 213008)`: the warp `w` of the default partition stores its minimum at
  word `w` (`Sm.Site.store10`) and every default thread reads word `tid % 4` (`Sm.Site.ldL`). Its
  first two words are the pair above, so the accesses to those bytes are the scratch's and the
  pair's, and `SharedOrder.count` orders all of them.
* `[213216, 213336)`: the mbarriers. Only mbarrier operations touch them.
* `[213336, 213340)`: the role table. Default-partition stores write it, workers read a byte.

The base word shares its first bytes with K slot 0: the allocation's store and the threads' loads
of it come before the first copy into slot 0 (the `bar.sync 0` pair of the common start), so the
word has its own region, and the K ring region begins after it.

Global memory holds the inputs the kernel reads (`Params.reads`) and the two output arrays.

`Placed` and `GlobalPlaced` say every byte an access touches is in one of these; they are facts
of the thread layer (a classification of every read and write; a row of "thread-layer gaps").
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Mbarrier placement (the regions and the placements: `Proof2/Lib/Regions.lean`) -/

/-- **Mbarrier placement**: every mbarrier an instruction names is one of the kernel's twelve, of
a launched CTA. -/
def MbarPlaced (L : Launch) (X : Execution) : Prop :=
  ∀ e m, X.UsesMbar e m → ∃ (b : EvD.Bar) (cta : Nat), cta < L.grid ∧ m = b.loc L cta

/-! ### Allocation -/

/-- A byte of a region of a launched CTA is allocated. -/
theorem region_allocated (hpre : Pre Q L mem0) {l : Loc} (hc : l.cta < L.grid)
    (h : InRegions L l) : mem0 l ≠ none := by
  have hw : l.space = .shared ∧ L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + sharedBytes := by
    unfold InRegions InBase InKv InQ InCount InScratch InRole at h
    unfold sharedBytes
    rcases h with h | h | h | h | h | h <;> exact ⟨h.1, by omega, by omega⟩
  have hh := hpre.sharedAllocated l.cta hc (l.addr - L.sharedBase) (by omega)
  obtain ⟨sp, cta, addr⟩ := l
  obtain ⟨hs, hlo, -⟩ := hw
  simp only at hs hlo hh
  subst hs
  rwa [show L.sharedBase + (addr - L.sharedBase) = addr by omega] at hh

/-- An input byte is allocated: it is an initialized launch byte. -/
theorem input_allocated (hpre : Pre Q L mem0) {l : Loc} (h : InInput Q l) : mem0 l ≠ none := by
  obtain ⟨hs, hc, hr⟩ := h
  obtain ⟨c, hc'⟩ := reads_mem0 hpre hr
  obtain ⟨sp, cta, addr⟩ := l
  simp only at hs hc hr
  subst hs hc
  rw [hc']
  simp

/-- An output byte is allocated. -/
theorem output_allocated (hpre : Pre Q L mem0) {l : Loc} (h : InOut Q l) : mem0 l ≠ none := by
  obtain ⟨hs, hc, ho | hl⟩ := h
  · have hh := hpre.oAllocated (l.addr - Q.oBase) (by omega)
    obtain ⟨sp, cta, addr⟩ := l
    simp only at hs hc ho hh
    subst hs hc
    rwa [show Q.oBase + (addr - Q.oBase) = addr by omega] at hh
  · have hh := hpre.lseAllocated (l.addr - Q.lseBase) (by omega)
    obtain ⟨sp, cta, addr⟩ := l
    simp only at hs hc hl hh
    subst hs hc
    rwa [show Q.lseBase + (addr - Q.lseBase) = addr by omega] at hh

/-- **Every named mbarrier's eight bytes are allocated**: they are inside the shared window. -/
theorem mbar_allocated (hpre : Pre Q L mem0) (hm : MbarPlaced L X) :
    ∀ e m l, X.UsesMbar e m → Acc.Covers { loc := m, size := 8 } l → mem0 l ≠ none := by
  intro e m l hu hc
  obtain ⟨b, cta, hcta, rfl⟩ := hm e m hu
  obtain ⟨hs, hc2, hlo, hhi⟩ := hc
  have hoff := b.off_lt
  simp only [EvD.Bar.loc] at hs hc2 hlo hhi
  have hh := hpre.sharedAllocated cta hcta (l.addr - L.sharedBase) (by omega)
  obtain ⟨sp, c, addr⟩ := l
  simp only at hs hc2 hlo hhi hh
  subst hs hc2
  rwa [show L.sharedBase + (addr - L.sharedBase) = addr by omega] at hh

/-- **Every touched byte is allocated.** -/
theorem no_unalloc (hpre : Pre Q L mem0) (hsh : SharedPlaced L X) (hgl : GlobalPlaced Q X)
    (hmb : MbarPlaced L X) : ¬ Unalloc mem0 X := by
  rintro (⟨e, a, l, ht, hc, hn⟩ | ⟨e, m, l, hu, hc, hn⟩)
  · by_cases hsp : l.space = .shared
    · obtain ⟨hcta, hr⟩ := hsh e a l ht hc hsp
      exact region_allocated hpre hcta hr hn
    · rcases hgl e a l ht hc hsp with h | h
      · exact input_allocated hpre h hn
      · exact output_allocated hpre h hn
  · exact mbar_allocated hpre hmb e m l hu hc hn

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
