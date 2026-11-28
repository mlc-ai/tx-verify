-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Lse
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid

@[expose] public section

/-! # The global bytes of the threads' accesses

The only global access of a thread is warpgroup 0's LSE store (`global_write`); its lane has a
thread index below 64 (`wg0_lseLane`), so its word lies in the LSE output, which `Pre` allocates
(`thread_global`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A global write is the LSE store**: of a lane of warpgroup 0, at its word. -/
theorem global_write (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} {a : Acc} {bs : List Byte}
    (hg : g < L.threads) (he : X.get (g, k) = some e) (hk : e.kind = .wr a bs)
    (hs : a.loc.space = .global) : Wg0At L g e.pc ∧ MemRow.Wg0Lse P L g e.pc a := by
  have hm : MemRow.MemEvent e := .inr (.inr (.inl ⟨a, bs, hk⟩))
  have hR := mem_rows hp hX hFw
  have key : ∀ a' : Acc, ((∃ bs', e.kind = .rd a' bs') ∨ ∃ bs', e.kind = .wr a' bs') →
      a'.loc.space = .shared → False := by
    rintro a' (⟨_, h⟩ | ⟨_, h⟩) hs' <;> rw [hk] at h <;> cases h
    rw [hs] at hs'
    cases hs'
  have nc : ∀ (a' : Acc) (bs' : List (Option Byte)), e.kind = .nc a' bs' → False := by
    intro a' bs' h; rw [hk] at h; cases h
  rcases hR.place hg he hm with h | h | h | h | h | h | h
  · obtain ⟨a', hk', hs', -⟩ := startup_mem_noMbar hp hX hFw hg he h hm
    exact (key a' hk' hs').elim
  · rcases wg0_mem_region hp hX hFw hg he h hm with ⟨a', bs', hk'⟩ | ⟨a', bs', hk', hl⟩ |
      ⟨a', r, hk', -, hsh⟩
    · exact (nc a' bs' hk').elim
    · rw [hk] at hk'
      cases hk'
      exact ⟨h, hl⟩
    · exact (key a' hk' hsh.1).elim
  · obtain ⟨a', bs', hk'⟩ := hR.wg1 hg he h hm
    exact (nc a' bs' hk').elim
  · obtain ⟨a', bs', hk'⟩ := hR.mma hg he h hm
    exact (nc a' bs' hk').elim
  · rcases tma_mem_noMbar hp hX hFw hg he h hm with ⟨a', bs', hk'⟩ | ⟨a', hk', hs', -⟩
    · exact (nc a' bs' hk').elim
    · exact (key a' (.inl hk') hs').elim
  · rcases ix_mem_noMbar hp hX hFw hg he h hm with ⟨a', bs', hk'⟩ | ⟨a', hk', hs', -⟩
    · exact (nc a' bs' hk').elim
    · exact (key a' (.inr hk') hs').elim
  · rcases dq_mem_noMbar hp hX hFw hg he h hm with ⟨a', bs', hk'⟩ | ⟨a', hk', hs', -⟩
    · exact (nc a' bs' hk').elim
    · exact (key a' hk' hs').elim

/-- **A thread's global access is the LSE store**: a global access of a thread is a write, the
event of a lane of warpgroup 0 at its LSE word. -/
theorem global_access (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {a : Acc} {w : Bool} (hI : X.Access (g, k) a w)
    (hgl : a.loc.space = .global) : w = true ∧ ∃ pc bs, X.get (g, k) = some ⟨pc, .wr a bs⟩ ∧
      Wg0At L g pc ∧ MemRow.Wg0Lse P L g pc a := by
  obtain ⟨ev, hget, hk, hm⟩ := access_event hI
  have hg := Frame.lt_of_get hX hget
  rcases hk with ⟨bs, hk⟩ | ⟨bs, hk⟩ | ⟨o, n, hk⟩
  · exfalso
    rcases mem_noMbar hp hX hFw hg hget (.inl ⟨a, bs, hk⟩) with ⟨a', bs', h⟩ | ⟨a', bs', h, -⟩ |
      ⟨a', h, hs', -⟩
    · rw [hk] at h; cases h
    · rw [hk] at h; cases h
    · rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [hk] at h <;> cases h
      rw [hs'] at hgl
      cases hgl
  · obtain ⟨hat, hl⟩ := global_write hp hX hFw hg hget hk hgl
    obtain ⟨pc, kd⟩ := ev
    simp only at hk
    subst hk
    rcases hI with ⟨bs', ⟨pc', h'⟩, hw⟩ | ⟨bs', ⟨pc', h'⟩, hw⟩ | ⟨o', n', pc', h'⟩
    · rw [hget] at h'
      cases h'
    · exact ⟨hw, pc, bs, hget, hat, hl⟩
    · rw [hget] at h'
      cases h'
  · exact absurd hk (mem_use (mem_rows hp hX hFw) hg hget)

/-- **A thread's global byte is allocated**: a byte a thread access covers outside shared memory
is a byte of the LSE output (`Pre.lseAllocated`). -/
theorem thread_global (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {a : Acc} {w : Bool}
    (hI : X.Access (g, k) a w) {l : Loc} (hc : a.Covers l) (hs : l.space ≠ .shared) :
    m l ≠ none := by
  have hgl : a.loc.space = .global := by
    rcases access_place hp hX hFw hI with h | ⟨h, -⟩
    · exact h
    · exact absurd (hc.1.trans h) hs
  obtain ⟨-, pc, bs, hget, hat, hl⟩ := global_access hp hX hFw hI hgl
  have hg := Frame.lt_of_get hX hget
  have hk : (⟨pc, .wr a bs⟩ : Event).kind = .wr a bs := rfl
  obtain ⟨hx, hy⟩ := ctaid_lt hp g
  have ht := wg0_lseLane hp hX hFw hget hat hk hl.1
  obtain ⟨-, -, hr⟩ := hp.tensorRange
  obtain ⟨-, hlo, hhi⟩ := MemRow.wg0Lse_in hr hy hx ht hl
  have hct : a.loc.cta = 0 := by rw [hl.2.1]
  obtain ⟨hcs, hcc, hlo', hhi'⟩ := hc
  obtain ⟨sp, c, ad⟩ := l
  simp only at hcs hcc hlo' hhi'
  rw [hgl] at hcs
  rw [hct] at hcc
  subst hcs hcc
  have := hp.lseAllocated (ad - P.lseBase) (by omega)
  rwa [show P.lseBase + (ad - P.lseBase) = ad by omega] at this

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
