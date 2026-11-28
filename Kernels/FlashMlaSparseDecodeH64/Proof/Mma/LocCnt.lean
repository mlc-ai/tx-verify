-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Objs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.RefStep

@[expose] public section

/-! # The MMA lane's counts on its named objects

The role's objects are the CTA's mbarriers (`obj_*`), and the counts `cntAt` of a block's place
on a stage's objects are the ring's uses (`cnt_ready`, `cnt_so`, `cnt_qk`, `cnt_sv`) and the
prologue's on the query's objects (`cnt_pro0`, `cnt_pro1`). For the role's trace-level exports
(`Mma/Export/Mbar.lean`, `Mma/Export/Time.lean`, `Mma/Export/Count.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0}

theorem mloc_eq_iff {g : Nat} {f f' : MbarFam} : loc L g f = loc L g f' ↔ f = f' := by
  constructor
  · intro h
    simp only [loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at h
    exact MbarFam.off_inj h
  · rintro rfl
    rfl

/-- A CTA's object named by the lane's own name is the lane's CTA's, of the same family. -/
theorem mloc_fam {g c : Nat} {f f' : MbarFam} (h : mbarLoc L c f = loc L g f') :
    c = g / L.block ∧ f = f' := by
  simp only [loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at h
  exact ⟨h.1, MbarFam.off_inj h.2⟩

section
variable {g : Nat} (hp : Pre P L m)
include hp

theorem obj_qTma : (objs L g).qTma = loc L g .qTma := qTma_eq.trans (qTma_loc hp)
theorem obj_qUt : (objs L g).qUt = loc L g .qUtccp := qUt_eq.trans (qUt_loc hp)
theorem obj_ready {b : Nat} (hb : b < 2) :
    (objs L g).ready b = loc L g (.dequantReady ⟨b, hb⟩) :=
  (ready_eq b).trans (ready_loc hp ⟨b, hb⟩)
theorem obj_qk {b : Nat} (hb : b < 2) : (objs L g).qk b = loc L g (.qkDone ⟨b, hb⟩) :=
  (qk_eq b).trans (qk_loc hp ⟨b, hb⟩)
theorem obj_so {b : Nat} (hb : b < 2) : (objs L g).so b = loc L g (.soReady ⟨b, hb⟩) :=
  (so_eq b).trans (so_loc hp ⟨b, hb⟩)
theorem obj_sv {b : Nat} (hb : b < 2) : (objs L g).sv b = loc L g (.svDone ⟨b, hb⟩) :=
  (sv_eq b).trans (sv_loc hp ⟨b, hb⟩)

/-! The counts of a block's place on a stage's objects. -/

theorem cnt_ready (r i : Nat) (b : Fin 2) :
    cntAt (objs L g) 31 r i false (.acq (loc L g (.dequantReady b))) =
      useAt b r i 1 := by
  fin_cases b <;>
    simp [cntAt, proCnt, loopCnt, obj_qTma hp, obj_qUt hp, obj_ready hp, obj_so hp,
      mloc_eq_iff, ind]

theorem cnt_so (r i : Nat) (b : Fin 2) :
    cntAt (objs L g) 31 r i false (.acq (loc L g (.soReady b))) = useAt b r i 20 := by
  fin_cases b <;>
    simp [cntAt, proCnt, loopCnt, obj_qTma hp, obj_qUt hp, obj_ready hp, obj_so hp,
      mloc_eq_iff, ind]

theorem cnt_qk (r i : Nat) (b : Fin 2) :
    cntAt (objs L g) 31 r i false (.commit (loc L g (.qkDone b))) = useAt b r i 19 := by
  fin_cases b <;>
    simp [cntAt, proCnt, loopCnt, obj_qUt hp, obj_qk hp, obj_sv hp, mloc_eq_iff, ind]

theorem cnt_sv (r i : Nat) (b : Fin 2) :
    cntAt (objs L g) 31 r i false (.commit (loc L g (.svDone b))) = ringUses 2 b r := by
  fin_cases b <;>
    simp [cntAt, proCnt, loopCnt, obj_qUt hp, obj_qk hp, obj_sv hp, mloc_eq_iff, ind]

/-- The prologue's counts on the query's objects at places 10 and 29. -/
theorem cnt_pro0 : cntAt (objs L g) 10 0 0 false (.acq (loc L g .qTma)) = 0 := by
  simp [cntAt, proCnt, loopCnt, useAt, ringUses, obj_qTma hp, obj_qUt hp,
    obj_ready hp, obj_so hp, mloc_eq_iff, ind]

theorem cnt_pro1 :
    cntAt (objs L g) 29 0 0 false (.acq (loc L g .qUtccp)) = 0 := by
  simp [cntAt, proCnt, loopCnt, useAt, ringUses, obj_qTma hp, obj_qUt hp,
    obj_ready hp, obj_so hp, mloc_eq_iff, ind]
end


end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
