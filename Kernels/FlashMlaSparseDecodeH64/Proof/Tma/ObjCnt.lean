-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Objs

@[expose] public section

/-! # The TMA warp's counts on the named objects

The reference invariant's counts (`cntAt`, `Tma/Ref.lean`) at a block's place on the named
mbarriers of `Iface/Objects.lean` (`MbarRow.loc`): the ring's and the tile's polls, arrivals and
gathers per slot, and the prologue's polls. For the role's exports (`Tma/Export/{Mbar,Count}`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0}

theorem loc_eq_iff {g : Nat} {f f' : MbarFam} : loc L g f = loc L g f' ↔ f = f' := by
  constructor
  · intro h
    simp only [loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at h
    exact MbarFam.off_inj h
  · rintro rfl
    rfl

/-- A CTA's object named by the lane's own name is the lane's CTA's, of the same family. -/
theorem loc_fam {g c : Nat} {f f' : MbarFam} (h : mbarLoc L c f = loc L g f') :
    c = g / L.block ∧ f = f' := by
  simp only [loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at h
  exact ⟨h.1, MbarFam.off_inj h.2⟩

section
variable {g : Nat} (hp : Pre P L m)
include hp

theorem o_qUt : (objs L g).qUt = loc L g .qUtccp := qUt_loc hp
theorem o_last : (objs L g).last = loc L g .lastStoreDone := last_loc hp
theorem o_ready {b : Nat} (hb : b < 4) :
    (objs L g).ready b = loc L g (.coordReady ⟨b, hb⟩) := ready_loc hp ⟨b, hb⟩
theorem o_free {b : Nat} (hb : b < 2) :
    (objs L g).free b = loc L g (.rawFree ⟨b, hb⟩) := free_loc hp ⟨b, hb⟩
theorem o_raw {b : Nat} (hb : b < 2) :
    (objs L g).raw b = loc L g (.rawReady ⟨b, hb⟩) := raw_loc hp ⟨b, hb⟩
theorem o_cfree {b : Nat} (hb : b < 4) :
    (objs L g).cfree b = loc L g (.coordFree ⟨b, hb⟩) := cfree_loc hp ⟨b, hb⟩

/-! The counts of a block's place on the ring's and the tile's objects. -/

theorem tcnt_ready (r i rd gs : Nat) (b : Fin 4) :
    cntAt (objs L g) 3 r i rd gs false (.acq (loc L g (.coordReady b))) =
      useAt 4 b r i 1 := by
  fin_cases b <;>
    simp [cntAt, proCnt, loopCnt, o_qUt hp, o_last hp, o_ready hp, o_free hp,
      loc_eq_iff, ind]

theorem tcnt_free (r i rd gs : Nat) (b : Fin 2) :
    cntAt (objs L g) 3 r i rd gs false (.acq (loc L g (.rawFree b))) =
      useAt 2 b r i 2 := by
  fin_cases b <;>
    simp [cntAt, proCnt, loopCnt, o_qUt hp, o_last hp, o_ready hp, o_free hp,
      loc_eq_iff, ind]

theorem tcnt_raw (r i rd gs : Nat) (b : Fin 2) :
    cntAt (objs L g) 3 r i rd gs false (.arrive (loc L g (.rawReady b))) =
      useAt 2 b r i 3 := by
  fin_cases b <;>
    simp [cntAt, proCnt, loopCnt, o_raw hp, o_cfree hp, loc_eq_iff, ind]

theorem tcnt_cfree (r i rd gs : Nat) (b : Fin 4) :
    cntAt (objs L g) 3 r i rd gs false (.arrive (loc L g (.coordFree b))) =
      ringUses 4 b r := by
  fin_cases b <;>
    simp [cntAt, proCnt, loopCnt, o_raw hp, o_cfree hp, loc_eq_iff, ind]

/-- The prologue's counts on the two set-up objects at places 1 and 2. -/
theorem tcnt_pro0 :
    cntAt (objs L g) 1 0 0 0 0 false (.acq (loc L g .qUtccp)) = 0 := by
  simp [cntAt, proCnt, loopCnt, useAt, ringUses, o_qUt hp, o_last hp,
    o_ready hp, o_free hp, loc_eq_iff, ind]

theorem tcnt_pro1 :
    cntAt (objs L g) 2 0 0 0 0 false (.acq (loc L g .lastStoreDone)) = 0 := by
  simp [cntAt, proCnt, loopCnt, useAt, ringUses, o_qUt hp, o_last hp,
    o_ready hp, o_free hp, loc_eq_iff, ind]

theorem tcnt_gather (r i rd gs : Nat) (b : Fin 2) :
    cntAt (objs L g) 3 r i rd gs false (.gather (loc L g (.rawReady b))) =
      16 * ringUses 2 b r + ind (r % 2 = b.val) * gs := by
  fin_cases b <;>
    simp [cntAt, proCnt, loopCnt, o_raw hp, loc_eq_iff, ind]
end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
