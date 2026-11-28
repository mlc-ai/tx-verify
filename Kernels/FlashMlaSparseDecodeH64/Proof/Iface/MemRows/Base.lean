-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # The memory classification rows: vocabulary

The words the rows of `Iface/MemRows/<Role>.lean` are written in. A row has the form "every
memory event of a lane of the role at a role pc is one of: …", each alternative an event kind
with the access's location described by the regions of `Iface/Regions.lean`:

* `MemEvent e`: `e` touches memory (a read, a non-coherent read, a write or a read-modify-write);
* `SharedIn L cta r a`: access `a` lies, all its bytes, in region `r` of CTA `cta`'s workspace;
* `LocIn L cta r l`: byte `l` lies in region `r` of CTA `cta`'s workspace;
* `wsAcc L cta off n a`: access `a` is the `n` bytes at offset `off` of CTA `cta`'s workspace
  (an exact address, for rows whose addresses are fixed by the code). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

namespace MemRow

/-- The event touches memory. -/
def MemEvent (e : Event) : Prop :=
  (∃ a bs, e.kind = .rd a bs) ∨ (∃ a bs, e.kind = .nc a bs) ∨ (∃ a bs, e.kind = .wr a bs) ∨
    ∃ a o n, e.kind = .rmw a o n

/-- Access `a` lies in region `r` of CTA `cta`'s shared workspace. -/
def SharedIn (L : Launch) (cta : Nat) (r : Region) (a : Acc) : Prop :=
  a.loc.space = .shared ∧ a.loc.cta = cta ∧ L.sharedBase + r.lo ≤ a.loc.addr ∧
    a.loc.addr + a.size ≤ L.sharedBase + r.lo + r.size

/-- Byte `l` lies in region `r` of CTA `cta`'s shared workspace (an asynchronous footprint's
byte). -/
def LocIn (L : Launch) (cta : Nat) (r : Region) (l : Loc) : Prop :=
  l.space = .shared ∧ l.cta = cta ∧ L.sharedBase + r.lo ≤ l.addr ∧
    l.addr < L.sharedBase + r.lo + r.size

/-- Access `a` is the `n` bytes at offset `off` of CTA `cta`'s shared workspace. -/
def WsAcc (L : Launch) (cta off n : Nat) (a : Acc) : Prop := a.loc = wsLoc L cta off ∧ a.size = n

/-- An exact access of a region is in it. -/
theorem wsAcc_in {L : Launch} {cta off n : Nat} {r : Region} {a : Acc} (h : WsAcc L cta off n a)
    (hlo : r.lo ≤ off) (hhi : off + n ≤ r.lo + r.size) : SharedIn L cta r a := by
  obtain ⟨hl, rfl⟩ := h
  refine ⟨by rw [hl]; rfl, by rw [hl]; rfl, ?_, ?_⟩ <;> rw [hl] <;> dsimp only [wsLoc] <;> omega

end MemRow

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
