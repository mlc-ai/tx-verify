-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Lemmas.Flow.Arith32WordW

@[expose] public section

/-! # The TMA warp's mbarrier words as the named objects

The role's objects (`objs`, `Tma/Ref.lean`) are the mbarriers of the families of
`Iface/Objects.lean` in the thread's CTA (`MbarRow.loc`): `bar_q_utccp`, `bar_last_store_done`,
and per slot `b` (the word `W b`) the ring's `coordReady b`, `coordFree b` and the tile's
`rawReady b`, `rawFree b`. The free word of the ring cancels the quadruples' offset
(`mad32 (W b) (-248)` after `mad32 (W b) 248`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A 32-bit word names the shared object at its number. -/
theorem smLoc_W {x : Nat} (hx : x < 2 ^ 32) :
    smLoc L g (W x) 0 = ⟨.shared, g / L.block, x⟩ := by
  simp only [smLoc, W, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt,
    Loc.mk.injEq, true_and]
  omega

/-- The shared base word. -/
theorem sbw_W (hp : Pre P L m) : sbw L = W L.sharedBase := by
  have h3 := sharedBase_lt hp
  apply BitVec.eq_of_toNat_eq
  simp only [sbw, W, truncBits, BitVec.toNat_ofNat]
  omega

/-- A slot's base word. -/
theorem slotB_W (hp : Pre P L m) {b : Nat} (hb : b < 4) :
    add32 (sbw L) (shl (W b) 3) = W (L.sharedBase + 8 * b) := by
  have h3 := sharedBase_lt hp
  rw [sbw_W hp, show (3 : Int) = ((3 : Nat) : Int) from rfl,
    shl_W (k := 3) (by decide) (by omega), add32_W (by omega)]
  congr 1
  omega

/-- A slot's word `c` bytes above the slot's base names the object at offset `c + 8 b`. -/
theorem smLoc_slot (hp : Pre P L m) {b : Nat} (hb : b < 4) {c : Nat} (hc : c ≤ 222920) :
    smLoc L g (addi (add32 (sbw L) (shl (W b) 3)) c) 0 =
      ⟨.shared, g / L.block, L.sharedBase + (c + 8 * b)⟩ := by
  have h3 := sharedBase_lt hp
  rw [slotB_W hp hb, addi_W (by omega) (by omega), smLoc_W (by omega)]
  congr 1
  omega

/-- `mad.lo` by `-248` after `mad.lo` by `248` on one slot word cancels. -/
theorem mad_cancel {b y : Nat} (hb : b < 4) (hy : y + 248 * b < 2 ^ 32) :
    mad32 (W b) (i32 (-248)) (mad32 (W b) (i32 248) (W y)) = W y := by
  have hn : i32 (-248) = W 4294967048 := by decide
  rw [hn, show (248 : Int) = ((248 : Nat) : Int) from rfl, i32_W (n := 248) (by decide),
    mad32_W (by omega) (by decide) (by omega)]
  apply BitVec.eq_of_toNat_eq
  interval_cases b <;>
    simp only [mad32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_mul,
      BitVec.toNat_add, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.zero_mod, Nat.zero_mul,
      Nat.zero_add] <;> omega

/-- The ring's free word: the quadruples' offset cancels. -/
theorem smLoc_cfree (hp : Pre P L m) {b : Nat} (hb : b < 4) :
    smLoc L g (addi (mad32 (W b) (i32 (-248)) (mad32 (W b) (i32 248)
      (add32 (sbw L) (shl (W b) 3)))) 222872) 0 =
      ⟨.shared, g / L.block, L.sharedBase + (222872 + 8 * b)⟩ := by
  have h3 := sharedBase_lt hp
  rw [slotB_W hp hb, mad_cancel hb (by omega),
    show (222872 : Int) = ((222872 : Nat) : Int) from rfl,
    addi_W (n := 222872) (by decide) (by omega), smLoc_W (by omega)]
  congr 1
  omega

/-- A word `c` bytes above the shared base names the object at offset `c`. -/
theorem smLoc_base (hp : Pre P L m) {c : Nat} (hc : c ≤ 222944) :
    smLoc L g (addi (sbw L) c) 0 = ⟨.shared, g / L.block, L.sharedBase + c⟩ := by
  have h3 := sharedBase_lt hp
  rw [sbw_W hp, addi_W (by omega) (by omega), smLoc_W (by omega)]

theorem qUt_loc (hp : Pre P L m) : (objs L g).qUt = MbarRow.loc L g .qUtccp := by
  simp only [objs, qUtL, qUtW, MbarRow.loc, mbarLoc, MbarFam.off]
  exact smLoc_base hp (c := 222784) (by decide)

theorem last_loc (hp : Pre P L m) : (objs L g).last = MbarRow.loc L g .lastStoreDone := by
  simp only [objs, lastL, lastW, MbarRow.loc, mbarLoc, MbarFam.off]
  exact smLoc_base hp (c := 222768) (by decide)

theorem qUtW_loc (hp : Pre P L m) : smLoc L g (qUtW L) 0 = MbarRow.loc L g .qUtccp := by
  have h := qUt_loc hp (g := g)
  simp only [objs, qUtL] at h
  exact h

theorem lastW_loc (hp : Pre P L m) : smLoc L g (lastW L) 0 = MbarRow.loc L g .lastStoreDone := by
  have h := last_loc hp (g := g)
  simp only [objs, lastL] at h
  exact h

theorem ready_loc (hp : Pre P L m) (b : Fin 4) :
    (objs L g).ready b.val = MbarRow.loc L g (.coordReady b) := by
  simp only [objs, readyL, MbarRow.loc, mbarLoc, MbarFam.off]
  exact smLoc_slot hp b.isLt (by decide)

theorem free_loc (hp : Pre P L m) (b : Fin 2) :
    (objs L g).free b.val = MbarRow.loc L g (.rawFree b) := by
  simp only [objs, freeL, MbarRow.loc, mbarLoc, MbarFam.off]
  exact smLoc_slot hp (by omega) (by decide)

theorem raw_loc (hp : Pre P L m) (b : Fin 2) :
    (objs L g).raw b.val = MbarRow.loc L g (.rawReady b) := by
  simp only [objs, rawL, MbarRow.loc, mbarLoc, MbarFam.off]
  exact smLoc_slot hp (by omega) (by decide)

theorem cfree_loc (hp : Pre P L m) (b : Fin 4) :
    (objs L g).cfree b.val = MbarRow.loc L g (.coordFree b) := by
  simp only [objs, cfreeL, MbarRow.loc, mbarLoc, MbarFam.off]
  exact smLoc_cfree hp b.isLt

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
