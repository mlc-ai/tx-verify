-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.InitFirst
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Global
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NcAlloc
import Lemmas.Kernel.Safety.Classes
import Lemmas.Protocol.NamedBarSources

@[expose] public section

/-! # ERR-UNALLOCATED: every access is to allocated memory

The safety class of Core's `Unsafe` this file owns (`Unalloc`). `Safe.noUnalloc` proves it from
the shared window (`Pre.sharedAllocated`) and the launch's inputs:

* a thread's shared access is a shared read or write of its CTA between the shared base and the
  first mbarrier (`mem_noMbar`); its global access is the LSE store, inside the LSE output
  (`thread_global`, `Pre.lseAllocated`);
* an asynchronous stage's shared byte is a byte of its issuer's CTA below the first mbarrier
  (`async_below`); its global byte is an in-bounds byte of a tensor map, an input or an allocated
  output (`async_global`);
* an mbarrier operand is a family's object of the issuer's CTA (`mbar_use`, `use_cta`), whose 8
  bytes lie below `sharedBytes` (`MbarFam.off_range`);
* a non-coherent read is a length load, the sink's load or an index pair's load of its role,
  whose bytes `Pre` allocates (`nc_alloc`), the idle code's two length loads among them
  (`wg1_ncAlloc`). Nothing is open. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- A byte of a launched CTA's shared window is allocated. -/
private theorem sh_alloc (hp : Pre P L mem0) {c : Nat} (hc : c < L.grid) {l : Loc}
    (hs : l.space = .shared) (hcta : l.cta = c) (hlo : L.sharedBase ≤ l.addr)
    (hhi : l.addr < L.sharedBase + sharedBytes) : mem0 l ≠ none := by
  have h := hp.sharedAllocated c hc (l.addr - L.sharedBase) (by omega)
  obtain ⟨s, c', x⟩ := l
  simp only at hs hcta hlo hhi
  subst hs hcta
  rw [← hp.sharedBase, show L.sharedBase + (x - L.sharedBase) = x by omega] at h
  exact h

/-- A thread's shared byte is allocated (`access_place`). -/
private theorem thread_shared (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) {g k : Nat}
    {a : Acc} {w : Bool} {l : Loc} (hI : X.Access (g, k) a w) (hc : a.Covers l)
    (hs : l.space = .shared) : mem0 l ≠ none := by
  obtain ⟨hcs, hcc, hlo, hhi⟩ := hc
  rcases access_place hp hX hFw hI with hgl | ⟨-, hc', hb, hb'⟩
  · rw [hs, hgl] at hcs
    cases hcs
  · obtain ⟨ev, hget, -⟩ := Frame.intent_issuer (show X.Intent (.thread (g, k)) a w from hI)
    refine sh_alloc hp (NamedBar.cta_lt (Frame.lt_of_get hX (g := g) (k := k) hget)) hs
      (hcc.trans hc') (by omega) ?_
    simp only [sharedBytes, Region.lo] at hb' ⊢
    omega

/-- **ERR-UNALLOCATED**: every access is to allocated memory. -/
theorem Safe.noUnalloc (hp : Pre P L mem0) (hIn : Inputs P L mem0)
    {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ¬ Unalloc mem0 X := by
  rintro (⟨r, a, l, ht, hc, hn⟩ | ⟨e, o, l, hu, hc, hn⟩)
  · rcases ht with ⟨w, hi⟩ | ⟨i, bs, -, hr⟩
    swap
    · obtain ⟨pc, he⟩ := hr
      exact (nc_alloc hp hX hFw hnu he rfl l hc).alloc hn
    by_cases hs : l.space = .shared
    swap
    · cases r with
      | thread e =>
        obtain ⟨g, k⟩ := e
        exact thread_global hp hX hFw hi hc hs hn
      | async i p =>
        obtain ⟨g, k⟩ := i
        exact async_global hp hX hFw hi hc hs hn
    cases r with
    | thread e =>
      obtain ⟨g, k⟩ := e
      exact thread_shared hp hX hFw hi hc hs hn
    | async i p =>
      obtain ⟨g, k⟩ := i
      obtain ⟨h1, h2, h3⟩ := async_below hp hX hFw hi hc hs
      have h3' : l.addr < L.sharedBase + sharedBytes := by
        simp only [sharedBytes, Region.lo] at h3 ⊢; omega
      refine sh_alloc hp (NamedBar.cta_lt ?_) hs h1 h2 h3' hn
      obtain ⟨ev, he, -⟩ := Frame.intent_issuer hi
      exact Frame.lt_of_get hX (g := g) (k := k) he
  · obtain ⟨ev, he, hm⟩ := Frame.usesMbar_mbarOf hu
    obtain ⟨g, k⟩ := e
    have hg := Frame.lt_of_get hX he
    obtain ⟨f, rfl⟩ := use_cta (mbar_use (hIn.mbar hp X hX hFw) hg he hm)
    have hoff := MbarFam.off_range f
    obtain ⟨hs, hcc, hlo, hhi⟩ := hc
    simp only [MbarRow.loc, mbarLoc] at hs hcc hlo hhi
    exact sh_alloc hp (NamedBar.cta_lt hg) hs hcc (by omega)
      (by simp only [sharedBytes]; omega) hn

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
