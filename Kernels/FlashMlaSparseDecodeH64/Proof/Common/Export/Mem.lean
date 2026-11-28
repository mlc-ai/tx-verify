-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Place
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Mem

@[expose] public section

/-! # The memory rows of every role, and what they give

`MemRows P L X` bundles the rows of `Iface/MemRows/`; `mem_rows` proves them all from the roles'
exports (`memRow_<role>`, `memRow_place`). `mem_use` is what they give without addresses: a
memory event of a launched lane is a read, a non-coherent read or a write, never a
read-modify-write (the kernel issues no atomic). `mem_noMbar` combines the roles' footprint
lemmas (`<role>_mem_noMbar`): every memory event of a launched lane is a non-coherent read, a
global write, or a shared read or write of the lane's CTA ending below the mbarriers. The
regions of the shared accesses are the rows' (see each row's note). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

/-- **The memory rows of every role.** -/
structure MemRows (P : Params) (L : Launch) (X : Execution) : Prop where
  startup : MemRow.Startup P L X
  wg0 : MemRow.Wg0 P L X
  wg1 : MemRow.Wg1 P L X
  mma : MemRow.Mma P L X
  tma : MemRow.Tma P L X
  index : MemRow.Index P L X
  dequant : MemRow.Dequant P L X
  place : MemRow.Place P L X

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The rows hold** under `Follow`. -/
theorem mem_rows (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MemRows P L X :=
  ⟨memRow_startup hp hX hFw, memRow_wg0 hp hX hFw, memRow_wg1 hp hX hFw, memRow_mma hp hX hFw,
    memRow_tma hp hX hFw, memRow_index hp hX hFw, memRow_dequant hp hX hFw,
    memRow_place hp hX hFw⟩

/-- **No read-modify-write**: a memory event of a launched lane is never a `rmw`. -/
theorem mem_use (hR : MemRows P L X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) {a : Acc} {o : List (Option Byte)}
    {n : Option (List Byte)} :
    e.kind ≠ .rmw a o n := by
  intro hk
  have hm : MemRow.MemEvent e := .inr (.inr (.inr ⟨a, o, n, hk⟩))
  rcases hR.place hg he hm with h | h | h | h | h | h | h
  · obtain ⟨-, ⟨_, _, h1, -⟩ | ⟨-, _, _, h1, -⟩⟩ := hR.startup hg he h hm <;> rw [hk] at h1 <;>
      cases h1
  · rcases hR.wg0 hg he h hm with ⟨_, _, h1⟩ | ⟨_, _, h1, -⟩ | ⟨_, _, h1, -⟩ | ⟨_, _, h1, -⟩ <;>
      rw [hk] at h1 <;> cases h1
  · obtain ⟨_, _, h1⟩ := hR.wg1 hg he h hm; rw [hk] at h1; cases h1
  · obtain ⟨_, _, h1⟩ := hR.mma hg he h hm; rw [hk] at h1; cases h1
  · rcases hR.tma hg he h hm with ⟨_, _, h1⟩ | ⟨_, _, h1, -⟩ <;> rw [hk] at h1 <;> cases h1
  · rcases hR.index hg he h hm with ⟨_, _, h1⟩ | ⟨_, _, h1, -⟩ <;> rw [hk] at h1 <;> cases h1
  · rcases hR.dequant hg he h hm with ⟨_, _, h1⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, _, _, _, h1, -⟩ <;>
      rw [hk] at h1 <;> cases h1

/-- **No memory access of a launched lane reaches the mbarriers**: a memory event is a
non-coherent read, a global write, or a shared read or write of the lane's CTA ending below the
mbarriers. -/
theorem mem_noMbar (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hm : MemRow.MemEvent e) :
    (∃ a bs, e.kind = .nc a bs) ∨ (∃ a bs, e.kind = .wr a bs ∧ a.loc.space = .global) ∨
      ∃ a : Acc, ((∃ bs, e.kind = .rd a bs) ∨ ∃ bs, e.kind = .wr a bs) ∧ a.loc.space = .shared ∧
        a.loc.cta = g / L.block ∧ L.sharedBase ≤ a.loc.addr ∧
          a.loc.addr + a.size ≤ L.sharedBase + Region.mbars.lo := by
  have hR := mem_rows hp hX hFw
  rcases hR.place hg he hm with h | h | h | h | h | h | h
  · exact .inr (.inr (startup_mem_noMbar hp hX hFw hg he h hm))
  · exact wg0_mem_noMbar hp hX hFw hg he h hm
  · exact .inl (hR.wg1 hg he h hm)
  · exact .inl (hR.mma hg he h hm)
  · rcases tma_mem_noMbar hp hX hFw hg he h hm with h1 | ⟨a, hk, h2⟩
    · exact .inl h1
    · exact .inr (.inr ⟨a, .inl hk, h2⟩)
  · rcases ix_mem_noMbar hp hX hFw hg he h hm with h1 | ⟨a, hk, h2⟩
    · exact .inl h1
    · exact .inr (.inr ⟨a, .inr hk, h2⟩)
  · rcases dq_mem_noMbar hp hX hFw hg he h hm with h1 | h2
    · exact .inl h1
    · exact .inr (.inr h2)

/-- **The event of a thread access**: a read, a write or a read-modify-write of the access, a
memory event. -/
theorem access_event {g k : Nat} {a : Acc} {w : Bool} (hI : X.Access (g, k) a w) :
    ∃ ev, X.get (g, k) = some ev ∧ ((∃ bs, ev.kind = .rd a bs) ∨ (∃ bs, ev.kind = .wr a bs) ∨
      ∃ o n, ev.kind = .rmw a o n) ∧ MemRow.MemEvent ev := by
  rcases hI with ⟨bs, ⟨pc, h⟩, -⟩ | ⟨bs, ⟨pc, h⟩, -⟩ | ⟨o, n, pc, h⟩
  · exact ⟨_, h, .inl ⟨bs, rfl⟩, .inl ⟨a, bs, rfl⟩⟩
  · exact ⟨_, h, .inr (.inl ⟨bs, rfl⟩), .inr (.inr (.inl ⟨a, bs, rfl⟩))⟩
  · exact ⟨_, h, .inr (.inr ⟨o, n, rfl⟩), .inr (.inr (.inr ⟨a, o, n, rfl⟩))⟩

/-- **A thread access's place**: a global access, or a shared access of the lane's CTA between the
shared base and the first mbarrier (`mem_noMbar`; an access is no non-coherent read). -/
theorem access_place (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {a : Acc} {w : Bool} (hI : X.Access (g, k) a w) :
    a.loc.space = .global ∨ (a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧
      L.sharedBase ≤ a.loc.addr ∧ a.loc.addr + a.size ≤ L.sharedBase + Region.mbars.lo) := by
  obtain ⟨ev, hget, hk, hm⟩ := access_event hI
  have hsz : ∀ a', ((∃ bs, ev.kind = .rd a' bs) ∨ ∃ bs, ev.kind = .wr a' bs) → a' = a := by
    rintro a' (⟨_, h⟩ | ⟨_, h⟩) <;> rcases hk with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, _, h'⟩ <;>
      rw [h'] at h <;> cases h <;> rfl
  rcases mem_noMbar hp hX hFw (Frame.lt_of_get hX hget) hget hm with ⟨a', bs', h⟩ |
    ⟨a', bs', h, hgl⟩ | ⟨a', h, hb⟩
  · rcases hk with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, _, h'⟩ <;> rw [h'] at h <;> cases h
  · obtain rfl := hsz a' (.inr ⟨bs', h⟩)
    exact .inl hgl
  · obtain rfl := hsz a' h
    exact .inr hb

/-- **A thread's shared access is in its CTA's workspace below the mbarriers**: a shared byte a
memory access of a thread covers is a byte of the thread's CTA between the shared base and the
first mbarrier (the thread half of `async_below`, from `access_place`). -/
theorem access_below (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {a : Acc} {w : Bool} (h : X.Access (g, k) a w) {b : Loc}
    (hc : a.Covers b) (hs : b.space = .shared) :
    b.cta = g / L.block ∧ L.sharedBase ≤ b.addr ∧ b.addr < L.sharedBase + Region.mbars.lo := by
  obtain ⟨hbs, hbc, hlo, hhi⟩ := hc
  have hbs' : b.space = a.loc.space := hbs
  rcases access_place hp hX hFw h with hg | ⟨-, hc', hb0, hb1⟩
  · rw [hs, hg] at hbs'
    cases hbs'
  · have hbc' : b.cta = a.loc.cta := hbc
    have hlo' : a.loc.addr ≤ b.addr := hlo
    have hhi' : b.addr < a.loc.addr + a.size := hhi
    exact ⟨hbc'.trans hc', by omega, by omega⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
