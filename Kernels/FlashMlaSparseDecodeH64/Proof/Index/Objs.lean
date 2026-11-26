-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # The index warp's mbarrier words as the named objects

The shared words of the role's mbarrier registers (`Ev.lean`) are the mbarriers of the families
of `Iface/Objects.lean` in the thread's CTA (`MbarRow.loc`): per ring slot `s` the slot's
`coordFree s` (the polls) and `coordReady s` (the arrivals). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A slot's word `c` bytes above the slot's barrier base names the object at `c + 8 s`. -/
theorem smLoc_slot (hp : Pre P L m) (s : Fin 4) {c : Nat} (hc : c ≤ 222872) :
    smLoc L g (addi (ixSlotB L s) c) 0 =
      ⟨.shared, g / L.block, L.sharedBase + (c + 8 * s.val)⟩ := by
  have h3 := sharedBase_lt hp
  fin_cases s <;>
  simp only [smLoc, ixSlotB, ixSlotW, shl, addi, add32, r32, i32, sbw, truncBits,
    BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt, Loc.mk.injEq, true_and] <;>
  simp <;> omega

theorem free_loc (hp : Pre P L m) (c : IxCtl) :
    smLoc L g (freeW L c) 0 = MbarRow.loc L g (.coordFree c.slot) :=
  smLoc_slot hp c.slot (by decide)

theorem ready_loc (hp : Pre P L m) (c : IxCtl) :
    smLoc L g (readyW L c) 0 = MbarRow.loc L g (.coordReady c.slot) :=
  smLoc_slot hp c.slot (by decide)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
