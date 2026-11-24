-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Role
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionSound
public import Kernels.FlashAttn4Fwd.Proof.Thread.Softmax
public import Lemmas.Flow.Compose

@[expose] public section

/-! # The entries of the composed roles

The dispatch reaches a role's `setmaxnreg` with the prologue's registers live there, valued by
the prologue's table for the thread's warp (`Prologue.dispatch`). A role values the registers
it inherits by its own table: the loader and the store warp fall back to the prologue's table,
the MMA warp to the registers its first state carries (`Mma.D.pro`, the prologue's). On every
register live at the entry the role's table and the prologue's agree, so the prologue's facts
there are the facts of the role's first state (`Loader.entry`, `Mma.entry`, `Store.entry`),
which satisfies the role's invariant (the store warp's holds from its first event on). The
correction warps' first state values every register by its own table (`Correction.entry`); the
softmax warps' entry (`Softmax.entry`) is ready for their composition. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {t : TState}

/-- The loader's entry. -/
theorem Loader.entry (hw : warpOf L g = 14)
    (h : At t RoleKind.loader.entry
      (Prologue.factsAt L g (warpOf L g) (rankOf L g) RoleKind.loader.entry)) :
    At t Loader.Site.setMaxReg.pc (Loader.facts L g ⟨.setMaxReg, 0, 0, 0, 1, 1⟩) ∧
      Loader.Inv L g ⟨.setMaxReg, 0, 0, 0, 1, 1⟩ := by
  rw [hw] at h
  refine ⟨at_congr h ?_, ⟨by decide, by decide, by decide, nofun, nofun, nofun, ?_⟩⟩
  · show ∀ r ∈ Flow.live_194, _
    simp only [Flow.live_194]
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true, Loader.valueOf, Loader.table, PTX.Flow.lookupLit, Option.getD_none]
  · intro u j h; rcases h with h | h <;> cases h

/-- The MMA warp's entry: its first state carries the prologue's registers of warp 12. -/
theorem Mma.entry (hw : warpOf L g = 12)
    (h : At t RoleKind.mma.entry
      (Prologue.factsAt L g (warpOf L g) (rankOf L g) RoleKind.mma.entry)) :
    At t Mma.Site.setMaxReg.pc
        (Mma.facts L g ⟨.setMaxReg, 0, 0, b32 0, Prologue.valueOf L g 12 (rankOf L g)⟩) ∧
      Mma.Inv L g ⟨.setMaxReg, 0, 0, b32 0, Prologue.valueOf L g 12 (rankOf L g)⟩ := by
  rw [hw] at h
  refine ⟨at_congr h ?_, ⟨.inl rfl, nofun, trivial⟩⟩
  show ∀ r ∈ Flow.live_541, _
  simp only [Flow.live_541]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, PTX.Flow.lookupLit,
    Option.getD_none, Option.getD_some]
  simp only [Prologue.valueOf, Prologue.values, PTX.Flow.lookupLit, Option.getD_some,
    Prologue.sb, Nat.add_zero, Mma.rank, rankOf, ctaOf, and_self]

/-- The store warp's entry. Its invariant holds from its first event on (`Store.Inv` asks
for an item, which the first state may not have). -/
theorem Store.entry (hw : warpOf L g = 13)
    (h : At t RoleKind.store.entry
      (Prologue.factsAt L g (warpOf L g) (rankOf L g) RoleKind.store.entry)) :
    At t Store.Site.setMaxReg.pc (Store.facts L g ⟨.setMaxReg, 0⟩) := by
  rw [hw] at h
  refine at_congr h ?_
  show ∀ r ∈ Flow.live_1130, _
  simp only [Flow.live_1130]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true, Store.valueOf, Store.table, PTX.Flow.lookupLit, Option.getD_none,
    Option.getD_some]
  simp only [Prologue.valueOf, Prologue.values, PTX.Flow.lookupLit, Option.getD_some,
    and_self]

/-- The correction warps' entry. -/
theorem Correction.entry
    (h : At t RoleKind.corr.entry
      (Prologue.factsAt L g (warpOf L g) (rankOf L g) RoleKind.corr.entry)) :
    At t Correction.Site.setMaxReg.pc
        (Correction.facts L g ⟨.setMaxReg, 0, 0, b32 0, 0, []⟩) ∧
      Correction.Inv L g ⟨.setMaxReg, 0, 0, b32 0, 0, []⟩ := by
  refine ⟨at_congr h ?_, ?_⟩
  · show ∀ r ∈ Flow.live_3754 ++ [], _
    simp only [Flow.live_3754]
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true, Correction.valueOf, Correction.values, Correction.chunkValues,
      Correction.loadValues, PTX.Flow.lookupLit, Option.getD_some, List.append_assoc,
      List.append_nil]
    simp only [Prologue.valueOf, Prologue.values, PTX.Flow.lookupLit, Option.getD_some,
      Prologue.sb, Correction.sb, Correction.work, Nat.zero_mul, Nat.add_zero, and_self]
  · constructor <;> simp [Correction.Site.inItem, Correction.Site.inTrip,
      Correction.Site.rescale]

/-- The softmax warps' entry (for their composition). -/
theorem Softmax.entry (hw : warpOf L g < 8)
    (h : At t RoleKind.softmax.entry
      (Prologue.factsAt L g (warpOf L g) (rankOf L g) RoleKind.softmax.entry)) :
    At t Softmax.start.site.pc (Softmax.facts L g Softmax.start) ∧
      Softmax.Inv L g Softmax.start := by
  refine ⟨at_congr h ?_, ?_⟩
  · show ∀ r ∈ Flow.live_1206 ++ [], _
    simp only [Flow.live_1206]
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true, Softmax.valueOf, Softmax.ctrlValues, Softmax.floatValues, Softmax.start,
      PTX.Flow.lookupLit, Option.getD_none, List.append_nil]
  · constructor <;> simp [Softmax.start, Softmax.Site.inItem, Softmax.Site.inTrip,
      Softmax.Site.tile0, hw, b32, Value.bytes]

end
end PTX.Kernels.FlashAttn4Fwd.Proof
