-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.UbStop
public import Lemmas.Flow.TmplOkSync

@[expose] public section

/-! # Templates that are not undefined behaviour

A proof tool, generic over the kernel (promoted from the tml-fa4 softmax lane,
`Proof2/Lib/UbFree.lean`): event templates of instructions whose operands the facts give and that
are therefore never undefined behaviour. They complement `Lemmas/Flow/UbStop.lean`
(`plainOk_tmpl`, `elect_ok`, `warpBar_ok`, `tcLd_ok`, `ld_ok`) and `Lemmas/Flow/TmplOkSync.lean`
(`elect_imm_ok`, an election with an immediate mask): a `bar.arrive` with immediate operands, the
implicit waits of a `tcgen05.ld` and a `tcgen05.st` an assumption selects, a Tensor Memory load
whose address register holds a word, and a weak load of any width and vector count at an aligned
address in global or shared memory. With `fires_ub`, a site whose template is none of these faults
fires no undefined-behaviour event. -/

namespace PTX.Flow

open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- A `bar.arrive` with an immediate barrier below 16 and a nonzero immediate count that is a
multiple of 32 is not undefined behaviour. -/
theorem barArrive_imm_ok {id n : Nat} {al : Bool} (hid : id < 16) (hn : n < 2 ^ 31)
    (hn32 : n % 32 = 0) (hn0 : n ≠ 0) (f : Fault) :
    eventTmpl A L g t (.barArrive (.imm id) (.imm n) al) ≠ .ub f := by
  have h1 : (truncBits 32 (BitVec.ofInt 64 (id : Int))).toNat = id := by
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  have h2 : (truncBits 32 (BitVec.ofInt 64 (n : Int))).toNat = n := by
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  simp only [eventTmpl, barTmpl, readBits, pure, Except.pure, h1, h2,
    show ¬ 16 ≤ id by omega, ↓reduceIte, hn32, true_and]
  simp [hn0]

/-- The implicit wait of a `tcgen05.ld` an assumption selects (a sub-step other than 0) is not
undefined behaviour. -/
theorem tcLd_wait_ok {ds : List Nat} {ta : Nat} {sh : TcShape}
    (hw : A.any (·.tcLdWait t.pc) = true) (hs : t.sub ≠ 0) (f : Fault) :
    eventTmpl A L g t (.tcLd ds ta sh) ≠ .ub f := by
  simp only [eventTmpl, tcLdTmpl, hw, hs, ↓reduceIte]
  intro h; cases h

/-- The implicit wait before a `tcgen05.st` an assumption selects (sub-step 0) is not undefined
behaviour in a launch of whole warps. -/
theorem tcSt_wait_ok {ta : Nat} {ss : List Opnd} {sh : TcShape} (hb : L.block % 32 = 0)
    (hw : A.any (·.tcStWaitLd t.pc) = true) (hs : t.sub = 0) (f : Fault) :
    eventTmpl A L g t (.tcSt ta ss sh) ≠ .ub f := by
  simp only [eventTmpl, tcStTmpl, hw, hs, hb, ↓reduceIte]
  intro h; cases h

/-- A Tensor Memory load whose address register holds a supported word is not undefined
behaviour. -/
theorem tcLd_word_ok {ds : List Nat} {ta : Nat} {sh : TcShape} {x : BitVec 64}
    (hb : L.block % 32 = 0) (hn : sh.countOk ds.length = true)
    (hr : t.regs ta = some (.bits 32 x)) (ha : x.toNat < 2 ^ 32)
    (hs : tcDataAddressOk L g sh x.toNat = true) (f : Fault) :
    eventTmpl A L g t (.tcLd ds ta sh) ≠ .ub f := by
  have hr' : t.regs ta = some (b32 x.toNat) := by
    rw [hr]; simp only [b32, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact tcLd_ok hb hn hr' ha hs f

/-- A weak load whose effective address is aligned to the access is not undefined behaviour. -/
theorem loadTmpl_ok {sp : Space} {w : Nat} {ds : List Nat} {base : Nat} {off : Int} {loc : Loc}
    (hea : effAddr L g t sp base off = .ok loc) (hw : w / 8 ≠ 0)
    (hal : loc.addr % (w / 8 * ds.length) = 0) (f : Fault) :
    loadTmpl A L g t sp false w ds base off ≠ .ub f := by
  simp only [loadTmpl, hea, elemAcc, hw, hal, bind, Except.bind, false_or, ne_eq,
    not_true_eq_false, ↓reduceIte, pure, Except.pure, Bool.false_eq_true]
  intro h; cases h

/-- The effective address of a global access through a 64-bit register. -/
theorem effAddr_global_bits {base : Nat} {off : Int} {x : BitVec 64}
    (hr : t.regs base = some (.bits 64 x)) :
    effAddr L g t .global base off =
      .ok ⟨.global, 0, (truncBits 64 x + BitVec.ofInt 64 off).toNat⟩ := by
  simp [effAddr, readBits, readReg, hr, bind, Except.bind, pure, Except.pure]

/-- The effective address of a shared access through a 32-bit register. -/
theorem effAddr_shared32 {base : Nat} {off : Int} {x : BitVec 64}
    (hr : t.regs base = some (.bits 32 x)) :
    effAddr L g t .shared base off =
      .ok ⟨.shared, g / L.block, (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat⟩ := by
  simp [effAddr, sharedEffAddr, readBits, readReg, hr, bind, Except.bind, pure, Except.pure]

/-- A weak global load of one 32-bit word through a 64-bit register holding a 4-aligned address
(plus a 4-aligned offset) is not undefined behaviour. -/
theorem ldGlobal_ok {d base : Nat} {off : Int} {x : BitVec 64}
    (hr : t.regs base = some (.bits 64 x))
    (hal : ((truncBits 64 x).toNat + (off % 4).toNat) % 4 = 0)
    (f : Fault) : loadTmpl A L g t .global false 32 [d] base off ≠ .ub f := by
  refine loadTmpl_ok (effAddr_global_bits hr) (by decide) ?_ f
  simp only [List.length_singleton, Nat.reduceDiv, Nat.reduceMul, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  rw [Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2 ^ 64)]
  simp only [Nat.reducePow, Nat.cast_ofNat]
  omega

/-- A weak shared load of four 32-bit words through a 32-bit register holding a 16-aligned address
(plus a 16-aligned offset) is not undefined behaviour. -/
theorem ldShared4_ok {d₀ d₁ d₂ d₃ base : Nat} {off : Int} {x : BitVec 64}
    (hr : t.regs base = some (.bits 32 x)) (hal : (x.toNat + (off % 16).toNat) % 16 = 0)
    (f : Fault) : loadTmpl A L g t .shared false 32 [d₀, d₁, d₂, d₃] base off ≠ .ub f := by
  refine loadTmpl_ok (effAddr_shared32 hr) (by decide) ?_ f
  simp only [List.length_cons, List.length_nil, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul,
    truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  rw [Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)]
  simp only [Nat.reducePow, Nat.cast_ofNat]
  omega

end

end PTX.Flow
