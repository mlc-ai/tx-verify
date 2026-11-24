-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Regs
import Lemmas.Flow.LoadShared
import Lemmas.Flow.UbFree
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Weak accesses whose effective address is aligned are not undefined behaviour (library
candidate)

`storeAl_ok`: element `t.sub` of a weak store under THREAD-ACCESS whose effective address is
aligned to the access, whose source is a register holding a value of the element's size, is not
undefined behaviour. `stShared_ok` and `stGlobal_ok` are its two address forms: a shared address
from a 32-bit register (the address is truncated to 32 bits, so a 32-bit word plus an offset
that are both multiples of the access size give an aligned address whether or not the sum wraps)
and a global address from a 64-bit register. `ldShared_ok` and `ldGlobal_ok'` are the same for
weak loads (`loadTmpl_ok`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- **A weak store at an aligned effective address of a source of the element's size is no
undefined behaviour.** -/
theorem storeAl_ok {a : MemAccess} {sp : Space} {base w r : Nat} {loc : Loc} {v : Value}
    (hrule : a.rule = some .threadAccess) (hs : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .store) (hsem : a.sem = .weak)
    (hea : effAddr L g t sp base a.addr.off = .ok loc) (hw : a.elem.width / 8 ≠ 0)
    (hal : loc.addr % (a.elem.width / 8 * a.srcs.length) = 0)
    (hsrc : a.srcs[t.sub]? = some (.reg r)) (hv : t.regs r = some v)
    (hby : v.bytes = a.elem.width / 8) (f : Fault) : eventTmpl A L g t (.mem a) ≠ .ub f := by
  rw [eventTmpl, memTmpl_store hrule hs hb hk hsem]
  simp only [storeTmpl, hea, elemAcc, hw, hal, bind, Except.bind, false_or, ne_eq,
    not_true_eq_false, ↓reduceIte, pure, Except.pure, hsrc]
  simp [readValue, readReg, hv, pure, Except.pure, storeValue_of_bytes hby]

/-- A shared store through a 32-bit register: aligned when the register's word and the offset
are multiples of the access size, which divides `2 ^ 32`. -/
theorem stShared_ok {a : MemAccess} {base : Nat} {x : BitVec 64} {n : Nat}
    (hrule : a.rule = some .threadAccess) (hs : a.locSpace? = some .shared)
    (hb : a.addr.base = .reg base 32) (hk : a.kind = .store) (hsem : a.sem = .weak)
    (hn : a.elem.width / 8 * a.srcs.length = n) (hn0 : n ≠ 0) (hdvd : n ∣ 2 ^ 32)
    (hr : t.regs base = some (.bits 32 x)) (hx : x.toNat % n = 0) (ho : a.addr.off % n = 0)
    (hsrc : ∃ r v, a.srcs[t.sub]? = some (.reg r) ∧ t.regs r = some v ∧
      v.bytes = a.elem.width / 8) (f : Fault) : eventTmpl A L g t (.mem a) ≠ .ub f := by
  obtain ⟨r, v, hsrc, hv, hby⟩ := hsrc
  have hw : a.elem.width / 8 ≠ 0 := by
    intro h; rw [h, Nat.zero_mul] at hn; exact hn0 hn.symm
  refine storeAl_ok hrule hs hb hk hsem (effAddr_shared32 hr) hw ?_ hsrc hv hby f
  rw [hn]
  have h64 : n ∣ 2 ^ 64 := hdvd.trans (by decide)
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  simp only [Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ h64]
  have hn' : (n : Int) ∣ ((2 ^ 64 : Nat) : Int) := Int.natCast_dvd_natCast.mpr h64
  have hoff : ((a.addr.off % ((2 ^ 64 : Nat) : Int)).toNat : Int) % n = 0 := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)), Int.emod_emod_of_dvd _ hn']
    exact ho
  have hoff' : (a.addr.off % ((2 ^ 64 : Nat) : Int)).toNat % n = 0 := by exact_mod_cast hoff
  rw [Nat.add_mod]
  simp only [Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ h64, hx, hoff', Nat.zero_add,
    Nat.zero_mod]

/-- A global store through a 64-bit register: aligned when the register's address and the
offset are multiples of the access size, which divides `2 ^ 64`. -/
theorem stGlobal_ok {a : MemAccess} {base : Nat} {x : BitVec 64} {n : Nat}
    (hrule : a.rule = some .threadAccess) (hs : a.locSpace? = some .global)
    (hb : a.addr.base = .reg base 64) (hk : a.kind = .store) (hsem : a.sem = .weak)
    (hn : a.elem.width / 8 * a.srcs.length = n) (hn0 : n ≠ 0) (hdvd : n ∣ 2 ^ 64)
    (hr : t.regs base = some (.bits 64 x)) (hx : x.toNat % n = 0) (ho : a.addr.off % n = 0)
    (hsrc : ∃ r v, a.srcs[t.sub]? = some (.reg r) ∧ t.regs r = some v ∧
      v.bytes = a.elem.width / 8) (f : Fault) : eventTmpl A L g t (.mem a) ≠ .ub f := by
  obtain ⟨r, v, hsrc, hv, hby⟩ := hsrc
  have hw : a.elem.width / 8 ≠ 0 := by
    intro h; rw [h, Nat.zero_mul] at hn; exact hn0 hn.symm
  refine storeAl_ok hrule hs hb hk hsem (effAddr_global_bits hr) hw ?_ hsrc hv hby f
  rw [hn]
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  simp only [Nat.mod_mod_of_dvd _ hdvd]
  have hn' : (n : Int) ∣ ((2 ^ 64 : Nat) : Int) := Int.natCast_dvd_natCast.mpr hdvd
  have hoff : ((a.addr.off % ((2 ^ 64 : Nat) : Int)).toNat : Int) % n = 0 := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)), Int.emod_emod_of_dvd _ hn']
    exact ho
  have hoff' : (a.addr.off % ((2 ^ 64 : Nat) : Int)).toNat % n = 0 := by exact_mod_cast hoff
  rw [Nat.add_mod]
  simp only [Nat.mod_mod_of_dvd _ hdvd, hx, hoff', Nat.zero_add, Nat.zero_mod]

/-- A weak shared load through a 32-bit register: aligned when the register's word and the offset
are multiples of the access size, which divides `2 ^ 32`. -/
theorem ldShared_ok {a : MemAccess} {base : Nat} {x : BitVec 64} {n : Nat}
    (hrule : a.rule = some .threadAccess) (hs : a.locSpace? = some .shared)
    (hb : a.addr.base = .reg base 32) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = false) (hn : a.elem.width / 8 * a.regs.length = n) (hn0 : n ≠ 0)
    (hdvd : n ∣ 2 ^ 32) (hr : t.regs base = some (.bits 32 x)) (hx : x.toNat % n = 0)
    (ho : a.addr.off % n = 0) (f : Fault) : eventTmpl A L g t (.mem a) ≠ .ub f := by
  have hw : a.elem.width / 8 ≠ 0 := by
    intro h; rw [h, Nat.zero_mul] at hn; exact hn0 hn.symm
  rw [eventTmpl, memTmpl_load hrule hs hb hk hsem, hnc]
  refine loadTmpl_ok (effAddr_shared32 hr) hw ?_ f
  rw [hn]
  have h64 : n ∣ 2 ^ 64 := hdvd.trans (by decide)
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  simp only [Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ h64]
  have hn' : (n : Int) ∣ ((2 ^ 64 : Nat) : Int) := Int.natCast_dvd_natCast.mpr h64
  have hoff : ((a.addr.off % ((2 ^ 64 : Nat) : Int)).toNat : Int) % n = 0 := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)), Int.emod_emod_of_dvd _ hn']
    exact ho
  have hoff' : (a.addr.off % ((2 ^ 64 : Nat) : Int)).toNat % n = 0 := by exact_mod_cast hoff
  rw [Nat.add_mod]
  simp only [Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ h64, hx, hoff', Nat.zero_add,
    Nat.zero_mod]

/-- A weak global load through a 64-bit register whose effective address (the register's bits plus
the offset, modulo `2 ^ 64`) is a multiple of the access size. -/
theorem ldGlobal_ok' {a : MemAccess} {base : Nat} {x : BitVec 64}
    (hrule : a.rule = some .threadAccess) (hs : a.locSpace? = some .global)
    (hb : a.addr.base = .reg base 64) (hk : a.kind = .load) (hsem : a.sem = .weak)
    (hnc : a.nc = false) (hw : a.elem.width / 8 ≠ 0) (hr : t.regs base = some (.bits 64 x))
    (hal : (truncBits 64 x + BitVec.ofInt 64 a.addr.off).toNat %
      (a.elem.width / 8 * a.regs.length) = 0) (f : Fault) :
    eventTmpl A L g t (.mem a) ≠ .ub f := by
  rw [eventTmpl, memTmpl_load hrule hs hb hk hsem, hnc]
  exact loadTmpl_ok (effAddr_global_bits hr) hw hal f

/-- **The footprint of a weak local access through a 64-bit register** is its element at the
register's address plus the offset (modulo `2 ^ 64`), when that address is aligned to the
access. -/
theorem accessAcc_local64 {a : MemAccess} {base : Nat} {x : BitVec 64}
    (hsp : a.space = some .local) (hb : a.addr.base = .reg base 64)
    (hr : t.regs base = some (.bits 64 x)) (hnc : a.nc = false)
    (hgo : a.hints.globalOnly = false) (hv : a.vec = 1) (hsem : a.sem = .weak)
    (hw : a.elem.width / 8 ≠ 0) (hal : wrapAddr 64 x a.addr.off % (a.elem.width / 8) = 0) :
    ∃ acc, accessAcc L g t a = .ok acc := by
  rw [accessAcc_of_weak hsem]
  have hloc : accessLoc L g t a = .ok ⟨.local, g, wrapAddr 64 x a.addr.off⟩ := by
    have hx : x.toNat % 18446744073709551616 = x.toNat := Nat.mod_eq_of_lt x.isLt
    unfold accessLoc
    rw [hsp, hb]
    simp [readBits, readReg, hr, bind, Except.bind, pure, Except.pure, truncBits, hx]
  simp only [hloc, hnc, hgo, hv, bind, Except.bind]
  simp [elemAcc, hw, hal, pure, Except.pure]

/-- **A store through THREAD-ACCESS that is not located directly** (`accessTmpl`), with a
footprint and a source of the element's size, is no undefined behaviour. -/
theorem accessStore_ok {a : MemAccess} {acc : Acc}
    (hrule : a.rule = some .threadAccess) (hd : a.locSpace? = none) (hk : a.kind = .store)
    (hacc : accessAcc L g t a = .ok acc)
    (hsrc : ∃ r v, a.srcs[t.sub]? = some (.reg r) ∧ t.regs r = some v ∧
      v.bytes = a.elem.width / 8) (f : Fault) : eventTmpl A L g t (.mem a) ≠ .ub f := by
  obtain ⟨r, v, hsrc, hv, hby⟩ := hsrc
  rw [eventTmpl]
  unfold memTmpl
  rw [hrule, hd]
  simp only [↓reduceIte, accessTmpl, hk, hacc, hsrc]
  simp [readValue, readReg, hv, bind, Except.bind, pure, Except.pure, storeValue_of_bytes hby]

/-- **An mbarrier initialization at a register plus an offset**, 8-aligned, with a register count
in range, is no undefined behaviour (`mbarInit_ok` with an offset). -/
theorem mbarInit_off_ok {base c a n off : Nat} (hr : t.regs base = some (b32 a))
    (ha : a + off < 2 ^ 32) (h8 : (a + off) % 8 = 0) (hc : t.regs c = some (b32 n)) (hn : 0 < n)
    (hn' : n < 2 ^ 20) (f : Fault) :
    eventTmpl A L g t (.mbarInit base (off : Int) (.reg c)) ≠ .ub f := by
  have hm : mbarLoc L g t base (off : Int) = .ok ⟨.shared, g / L.block, a + off⟩ := by
    simp [mbarLoc, effAddr_b32_off hr ha, h8, bind, Except.bind, pure, Except.pure]
  have h20 : n < 1048576 := hn'
  have h32 : n < 4294967296 := by omega
  have h64 : n < 18446744073709551616 := by omega
  simp [eventTmpl, tmaTmpl, hm, readBits_b32' hc, truncBits, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64, hn, h20, ofExec, widenMbarScope, bind, Except.bind,
    pure, Except.pure]

/-- `mbarInit_off_ok` with the registers' words as bits. -/
theorem mbarInit_bits_ok {base c off : Nat} {x y : BitVec 64}
    (hr : t.regs base = some (.bits 32 x)) (ha : x.toNat + off < 2 ^ 32)
    (h8 : (x.toNat + off) % 8 = 0) (hc : t.regs c = some (.bits 32 y)) (hn : 0 < y.toNat)
    (hn' : y.toNat < 2 ^ 20) (f : Fault) :
    eventTmpl A L g t (.mbarInit base (off : Int) (.reg c)) ≠ .ub f := by
  have hr' : t.regs base = some (b32 x.toNat) := by
    rw [hr]; simp only [b32, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hc' : t.regs c = some (b32 y.toNat) := by
    rw [hc]; simp only [b32, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact mbarInit_off_ok hr' ha h8 hc' hn hn' f

/-- **An mbarrier initialization through a 32-bit register at an 8-aligned word plus an 8-aligned
offset**, with a register count in range, is no undefined behaviour (the shared address is
truncated to 32 bits, so the sum is aligned whether or not it wraps). -/
theorem mbarInit_al_ok {base c : Nat} {off : Int} {x y : BitVec 64}
    (hr : t.regs base = some (.bits 32 x)) (h8 : x.toNat % 8 = 0) (ho : off % 8 = 0)
    (hc : t.regs c = some (.bits 32 y)) (hn : 0 < y.toNat) (hn' : y.toNat < 2 ^ 20)
    (f : Fault) : eventTmpl A L g t (.mbarInit base off (.reg c)) ≠ .ub f := by
  have hal : (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat % 8 = 0 := by
    have h64 : (8 : Nat) ∣ 2 ^ 64 := by decide
    have h32 : (8 : Nat) ∣ 2 ^ 32 := by decide
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
    simp only [Nat.mod_mod_of_dvd _ h32, Nat.mod_mod_of_dvd _ h64]
    have hn8 : (8 : Int) ∣ ((2 ^ 64 : Nat) : Int) := Int.natCast_dvd_natCast.mpr h64
    have hoff : ((off % ((2 ^ 64 : Nat) : Int)).toNat : Int) % 8 = 0 := by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)), Int.emod_emod_of_dvd _ hn8]
      exact ho
    have hoff' : (off % ((2 ^ 64 : Nat) : Int)).toNat % 8 = 0 := by exact_mod_cast hoff
    rw [Nat.add_mod]
    simp only [Nat.mod_mod_of_dvd _ h32, Nat.mod_mod_of_dvd _ h64, h8, hoff', Nat.zero_add,
      Nat.zero_mod]
  have hm : mbarLoc L g t base off =
      .ok ⟨.shared, g / L.block, (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat⟩ := by
    simp only [mbarLoc, effAddr_shared32 hr, hal, bind, Except.bind, pure, Except.pure,
      ↓reduceIte]
  have hc' : t.regs c = some (b32 y.toNat) := by
    rw [hc]; simp only [b32, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h20 : y.toNat < 1048576 := hn'
  have h32 : y.toNat < 4294967296 := by omega
  simp [eventTmpl, tmaTmpl, hm, readBits_b32' hc', truncBits, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h32, hn, h20, ofExec, widenMbarScope, bind, Except.bind,
    pure, Except.pure]

end

end PTX.Flow
