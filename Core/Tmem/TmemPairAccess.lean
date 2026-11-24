-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaRead

@[expose] public section

namespace PTX.Tmem.Pair
noncomputable section

/-! ## ERR-TMEM-ACCESS-LIFETIME — allocation and completion of every Tensor Memory access
Statement: Every Tensor Memory access must touch cells that a completed allocation of the cell's CTA
  covers for it, through the allocation's own event or its paired peer allocation. For every
  allocation that covers the access and every release attempt of that allocation, the access must
  complete before the release attempt, or a fresh allocation of the cell must lie between them; an
  execution that breaks either condition is unsafe.

Defs: Tmem.Pair.Access, Tmem.Pair.AccessSafe, Tmem.Pair.AccessUnsafe

Source:
- §9.7.18.1.2 (Tensor Memory is allocated before use)
- §9.7.18.7.1: "taddr must point to a previous Tensor Memory allocation"
- §9.7.18.6.4 (completion before cross-thread synchronization)
- DEP-TC-FENCE
- EXT-TCACQUIRE
- EXT-TC-EXEC-ORDER
- OBJ-TMEM-PUBLICATION
- EXT-PAIR-ALLOC-ORDER

Direction: reading

Applies: Every MMA destination write and potential accumulator read, and every Tensor Memory load
  and store register, copied word and word a shift reads or writes, of either CTA group

Premises: Each access names its physical cell. A completed allocation of that cell's CTA covers it
  and is published to the access. Every release attempt of every covering allocation is checked,
  even if no joint release has completed. The release attempts of an allocation are, in each lane of
  its warp, the first matching deallocation after it, every matching deallocation by another warp of
  its CTA, and the same release attempts of the peer CTA's allocation when the allocation is paired.
  For each of them, the access must have completed before it (an MMA or copy by an observed commit,
  a load by its thread's `wait::ld`, a store by its thread's `wait::st`), that completion ordered
  before the release by a fenced chain or, under EXT-TCACQUIRE, by causality, or a fresh allocation
  must separate the access from that lifetime. The text has the peer warps synchronize their
  accesses before they attempt a collective deallocation.

Effect: AccessUnsafe enters Unsafe. Coverage is `Tmem.Pair.Covers` (OBJ-TMEM-LIFETIME): an
  allocation paired with a `cta_group::2` allocation of the peer CTA also covers the events that the
  peer warp's allocation happens before (OBJ-TMEM-PUBLICATION, EXT-PAIR-ALLOC-ORDER), both in the
  allocated-before-access check and in the release check, so a record covering an access only
  through its peer is still released after the access completes. This is the only check that a
  Tensor Memory access is allocated. The
  direction is `reading` because acceptance rests on named readings: EXT-TCACQUIRE and, through the
  fenced chains of DEP-TC-FENCE, EXT-TC-EXEC-ORDER; every other path is stricter than the text.
-/

/-- Event `e` accesses Tensor Memory cell `cell`: an MMA its written and accumulator cells, a
load or store the cells of its registers, a copy the cells of its copied words. -/
def Access (L : Launch) (X : Execution) (e : EvId) (cell : TcMma.Cell) : Prop :=
  X.MmaAccess e cell ∨ (∃ j, TcMma.LoadCell L X e j cell) ∨ TcMma.StoreCell L X e cell ∨
    TcMma.CpCell X e cell ∨ TcMma.ShiftCell X e cell ∨ TcMma.ShiftReadCell X e cell

/-- Every Tensor Memory access is allocated before it, and completes before each release of an
allocation covering it unless a fresh allocation separates them. Coverage (`Covers`) includes
the paired peer allocation (EXT-PAIR-ALLOC-ORDER), and its releases are then checked too. -/
def AccessSafe (L : Launch) (X : Execution) : Prop :=
  ∀ e cell, Access L X e cell →
    (∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r cell.cta e cell.column) ∧
    ∀ cta r, r ∈ X.tmemHistory cta → Covers L X r cell.cta e cell.column →
      ∀ d, ReleaseOf L X r d →
        TcMma.CompletedBefore L X e d ∨ FreshAfter L X d e cell.cta cell.column

/-- Some Tensor Memory access is unallocated or may still be in flight at a release attempt. -/
def AccessUnsafe (L : Launch) (X : Execution) : Prop := ¬ AccessSafe L X

end
end PTX.Tmem.Pair
