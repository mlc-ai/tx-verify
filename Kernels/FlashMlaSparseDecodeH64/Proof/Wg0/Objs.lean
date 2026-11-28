-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefNext
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # Warpgroup 0's mbarrier words as the named objects

The shared words of the role's mbarrier registers (`Ev.lean`) and the reference invariant's
objects (`Ref.lean`) are the mbarriers of the families of `Iface/Objects.lean` in the thread's CTA
(`MbarRow.loc`): `arrW` the last-store barrier, the valid-mask ring's slot `j` (`vReadyW`,
`vFreeW`) `coordReady j` and `coordFree j`, the score ring's slot `b` (`qkW`, `soW`, `svW`)
`qkDone b`, `soReady b` and `svDone b`. A site that is none of the six mbarrier sites fires no
event that names an mbarrier (`evK_noMbarOf`); the parity words read as their parity (`parW_W`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A word `c` bytes above the shared base names the object at offset `c`. -/
theorem smLoc_base (hp : Pre P L m) {c : Nat} (hc : c ≤ 222944) :
    smLoc L g (addi (sbw L) c) 0 = ⟨.shared, g / L.block, L.sharedBase + c⟩ := by
  have hb := sharedBase_lt hp
  simp only [smLoc, addi, r32, i32, sbw, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt, Loc.mk.injEq, true_and]
  omega

/-- Slot `j`'s word `c` bytes above the shared base names the object at offset `c + 8 j`. -/
theorem smLoc_slotW (hp : Pre P L m) {j c : Nat} (hj : j < 4) (hc : c + 8 * j ≤ 222944) :
    smLoc L g (slotW L (W j) c) 0 = ⟨.shared, g / L.block, L.sharedBase + (c + 8 * j)⟩ := by
  have hb := sharedBase_lt hp
  interval_cases j <;>
  simp only [smLoc, slotW, addi, add32, shl, r32, i32, sbw, W, truncBits, BitVec.toNat_ofNat,
    BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_shiftLeft, Loc.mk.injEq, true_and] <;>
  simp <;> omega

theorem arr_loc (hp : Pre P L m) : smLoc L g (arrW L) 0 = loc L g .lastStoreDone :=
  smLoc_base hp (by decide)

theorem vReady_loc (hp : Pre P L m) (j : Fin 4) :
    smLoc L g (slotW L (W j.val) 222840) 0 = loc L g (.coordReady j) :=
  smLoc_slotW (c := 222840) hp j.isLt (by omega)

theorem vFree_loc (hp : Pre P L m) (j : Fin 4) :
    smLoc L g (slotW L (W j.val) 222872) 0 = loc L g (.coordFree j) :=
  smLoc_slotW (c := 222872) hp j.isLt (by omega)

theorem qk_loc (hp : Pre P L m) (b : Fin 2) :
    smLoc L g (slotW L (W b.val) 222904) 0 = loc L g (.qkDone b) :=
  smLoc_slotW (c := 222904) hp (by omega) (by omega)

theorem so_loc (hp : Pre P L m) (b : Fin 2) :
    smLoc L g (slotW L (W b.val) 222920) 0 = loc L g (.soReady b) :=
  smLoc_slotW (c := 222920) hp (by omega) (by omega)

theorem sv_loc (hp : Pre P L m) (b : Fin 2) :
    smLoc L g (slotW L (W b.val) 222936) 0 = loc L g (.svDone b) :=
  smLoc_slotW (c := 222936) hp (by omega) (by omega)

/-! ### The reference invariant's objects -/

theorem o_last (hp : Pre P L m) : (objs L g).last = loc L g .lastStoreDone :=
  last_eq.trans (arr_loc hp)
theorem o_vReady (hp : Pre P L m) {j : Nat} (hj : j < 4) :
    (objs L g).vReady j = loc L g (.coordReady ⟨j, hj⟩) :=
  (vReady_eq j).trans (vReady_loc hp ⟨j, hj⟩)
theorem o_vFree (hp : Pre P L m) {j : Nat} (hj : j < 4) :
    (objs L g).vFree j = loc L g (.coordFree ⟨j, hj⟩) :=
  (vFree_eq j).trans (vFree_loc hp ⟨j, hj⟩)
theorem o_qk (hp : Pre P L m) {b : Nat} (hb : b < 2) :
    (objs L g).qk b = loc L g (.qkDone ⟨b, hb⟩) :=
  (qk_eq b).trans (qk_loc hp ⟨b, hb⟩)
theorem o_so (hp : Pre P L m) {b : Nat} (hb : b < 2) :
    (objs L g).so b = loc L g (.soReady ⟨b, hb⟩) :=
  (so_eq b).trans (so_loc hp ⟨b, hb⟩)
theorem o_sv (hp : Pre P L m) {b : Nat} (hb : b < 2) :
    (objs L g).sv b = loc L g (.svDone ⟨b, hb⟩) :=
  (sv_eq b).trans (sv_loc hp ⟨b, hb⟩)

/-! ### Sites and parities -/

/-- The objects of two families are equal only for the same family. -/
theorem loc_inj {f f' : MbarFam} : loc L g f = loc L g f' ↔ f = f' := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  simp only [loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at h
  exact MbarFam.off_inj h

/-- **A site that is none of the six mbarrier sites fires no event naming an mbarrier.** -/
theorem evK_noMbarOf {w : BitVec 64} {d : D} {e : Event} {l : Loc} (hs : d.site.mb = false)
    (hu : ∀ f, e.kind ≠ .ub f) (hev : EvK P L g w d e) : ¬ Frame.MbarOf e l := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, k⟩ := e
  simp only at hu
  cases s <;> simp only [Site.mb, Bool.true_eq_false] at hs <;>
    simp only [EvK, GWrAt, RdAt, WrAt, GenWrAt, NcEv, TcLdEv, TcStEv] at hev <;>
    (try casesm* _ ∨ _, _ ∧ _, Exists _) <;> subst_vars <;> simp_all [Frame.MbarOf]

/-- The parity word of parity `q` reads as `q`. -/
theorem parW_W {q : Nat} (hq : q < 2) : (truncBits 32 (parW (W q))).toNat % 2 = q := by
  interval_cases q <;> decide

section
variable (hp : Pre P L m)
include hp

/-! ### The counts of a place on the ring objects -/

theorem acq_ready (r i : Nat) (j : Fin 4) :
    acqCnt (objs L g) r i none (loc L g (.coordReady j)) = use 4 j r i 1 := by
  fin_cases j <;>
    simp [acqCnt, o_vReady hp, o_qk hp, loc_inj, ind]

theorem acq_qk (r i : Nat) (b : Fin 2) :
    acqCnt (objs L g) r i none (loc L g (.qkDone b)) = use 2 b r i 2 := by
  fin_cases b <;>
    simp [acqCnt, o_vReady hp, o_qk hp, loc_inj, ind]

theorem arr_free (a : Bool) (r i : Nat) (j : Fin 4) :
    arrCnt (objs L g) a r i (loc L g (.coordFree j)) = use 4 j r i 3 := by
  fin_cases j <;> cases a <;>
    simp [arrCnt, o_last hp, o_vFree hp, o_so hp, loc_inj, ind]

theorem arr_so (a : Bool) (r i : Nat) (b : Fin 2) :
    arrCnt (objs L g) a r i (loc L g (.soReady b)) = ringUses 2 b r := by
  fin_cases b <;> cases a <;>
    simp [arrCnt, o_last hp, o_vFree hp, o_so hp, loc_inj, ind]
end


end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
