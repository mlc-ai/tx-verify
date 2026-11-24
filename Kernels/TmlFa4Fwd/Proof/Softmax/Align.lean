-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
import Lemmas.Flow.UbFree
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Address facts of the softmax warps' memory and Tensor Memory accesses

The facts the safety of the softmax sites needs (`Safe.lean`): the score loads' Tensor Memory
addresses (`tmS` and its column offsets) lie in the warp's lane chunk (`tm_ok`, decided over the
512 threads of a CTA); the bias loads' swizzled shared addresses are 16-aligned (`lo_bAddr`,
`lo_bAddr0`, through the low four bits of each word operation and the 1024-aligned shared base);
the scheduler's and the request's global addresses (`addrU`, `addrS` of a 4-aligned input base)
are 4-aligned (`addrU_al`, `addrS_al`), so their loads are no undefined behaviour (`ldG_ok`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ori)
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 add32 addi andi shl shru xor32 scmpi sel)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The thread index word of a lane of a one-dimensional CTA. -/
theorem tidW_eq (hp : Pre p L m) : tidW L g = BitVec.ofNat 64 (g % L.block) := by
  simp only [tidW]
  rw [Launch.oneDim_tidOf hp.cluster.2.2]
  have : g % L.block < 2 ^ 32 := by
    have := Nat.mod_lt g (show 0 < L.block by rw [hp.block]; decide)
    rw [hp.block] at this ⊢; omega
  apply BitVec.eq_of_toNat_eq
  simp [Dim3.get, truncBits, BitVec.toNat_ofNat]
  omega

/-- The score column base of a thread `i` of the CTA, from its warp `i / 32`. -/
abbrev tmI (i : Nat) : BitVec 64 :=
  or32 (sel (scmpi .gt .s (BitVec.ofNat 64 (i / 32)) 3) (i32 128) (i32 0))
    (andi (shl (BitVec.ofNat 64 i) 16) 6291456)

/-- The lane field check of `.32x32b` for thread `i` of a CTA of 512 threads. -/
abbrev laneOkI (i a : Nat) : Bool :=
  true && (decide (0 < 32) && (decide (a / 2 ^ 16 + 32 ≤ 32) ||
    (decide (i / 32 % 4 * 32 ≤ a / 2 ^ 16) && decide (a / 2 ^ 16 + 32 ≤ i / 32 % 4 * 32 + 32))))

set_option maxRecDepth 100000 in
theorem tm_lanes : ∀ i < 512, laneOkI i (tmI i).toNat = true ∧ laneOkI i (ori (tmI i) 32).toNat ∧
    laneOkI i (ori (tmI i) 64).toNat ∧ laneOkI i (ori (tmI i) 96).toNat := by
  decide +kernel

theorem tcAddr_eq (a : Nat) :
    tcDataAddressOk L g .s32x32b a = laneOkI (g % L.block) a := by
  rfl

/-- The score loads' Tensor Memory addresses are in the warp's lane chunk. -/
theorem tm_ok (hp : Pre p L m) :
    tcDataAddressOk L g .s32x32b (tmS L g).toNat = true ∧
    tcDataAddressOk L g .s32x32b (ori (tmS L g) 32).toNat = true ∧
    tcDataAddressOk L g .s32x32b (ori (tmS L g) 64).toNat = true ∧
    tcDataAddressOk L g .s32x32b (ori (tmS L g) 96).toNat = true := by
  have hi : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  simp only [tcAddr_eq, tmS, stg, warpW, tidW_eq hp]
  exact tm_lanes _ hi

theorem lo_trunc32 (x : BitVec 64) : (truncBits 32 x).toNat % 16 = x.toNat % 16 := by
  simp only [truncBits, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64),
    Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 32)]

theorem lo_add (x y : BitVec 64) : (x + y).toNat % 16 = (x.toNat % 16 + y.toNat % 16) % 16 := by
  rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64), Nat.add_mod]

theorem lo_and (x y : BitVec 64) : (x &&& y).toNat % 16 = x.toNat % 16 &&& y.toNat % 16 := by
  rw [BitVec.toNat_and]; exact Nat.and_mod_two_pow (n := 4)

theorem lo_xor (x y : BitVec 64) : (x ^^^ y).toNat % 16 = x.toNat % 16 ^^^ y.toNat % 16 := by
  rw [BitVec.toNat_xor]; exact Nat.xor_mod_two_pow (n := 4)

theorem lo_or (x y : BitVec 64) : (x ||| y).toNat % 16 = x.toNat % 16 ||| y.toNat % 16 := by
  rw [BitVec.toNat_or]; exact Nat.or_mod_two_pow (n := 4)

theorem lo_ofInt (n : Int) : (BitVec.ofInt 64 n).toNat % 16 = (n % 16).toNat := by
  rw [BitVec.toNat_ofInt]; omega

theorem lo_ofNat (n : Nat) : (BitVec.ofNat 64 n).toNat % 16 = n % 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)]

theorem lo_shl7 (x : BitVec 64) : (x <<< 7).toNat % 16 = 0 := by
  rw [BitVec.toNat_shiftLeft, Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64), Nat.shiftLeft_eq]
  omega

/-- The swizzle keeps the low four bits. -/
theorem lo_swz (x : BitVec 64) :
    (Proof.Softmax.swz x).toNat % 16 = x.toNat % 16 := by
  simp only [swz, xor32, andi, shru, r32, i32, lo_xor, lo_and, lo_trunc32, lo_ofInt]
  simp

theorem lo_rowSb (hp : Pre p L m) : (rowSb L g).toNat % 16 = 0 := by
  have hs := hp.shared.1
  simp only [rowSb, add32, andi, shl, r32, i32, Mma.sbW, lo_trunc32, lo_add, lo_and, lo_ofNat,
    lo_ofInt]
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by decide)), lo_trunc32,
    show (truncBits 32 (BitVec.ofInt 64 7)).toNat = 7 by decide, lo_shl7]
  simp; omega

theorem lo_bOff : (bOff L g).toNat % 16 = 0 := by
  simp only [bOff, sel]; split <;> decide

theorem lo_addi (x : BitVec 64) (n : Int) (hn : n % 16 = 0) :
    (addi x n).toNat % 16 = x.toNat % 16 := by
  simp only [addi, r32, i32, lo_trunc32, lo_add, lo_ofInt]
  omega

theorem lo_bAddr (hp : Pre p L m) {n : Int} (hn : n % 16 = 0) : (bAddr L g n).toNat % 16 = 0 := by
  simp only [bAddr, lo_swz, lo_addi _ _ hn, add32, r32, lo_trunc32, lo_add, lo_rowSb hp, lo_bOff]

theorem lo_bAddr0 (hp : Pre p L m) : (bAddr0 L g).toNat % 16 = 0 := by
  simp only [bAddr0, add32, r32, lo_trunc32, lo_add, lo_swz,
    lo_addi _ _ (by decide : (166912 : Int) % 16 = 0),
    lo_rowSb hp, lo_bOff]

theorem lo4_trunc64 (x : BitVec 64) : (truncBits 64 x).toNat % 4 = x.toNat % 4 := by
  simp only [truncBits, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2 ^ 64), Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2 ^ 64)]

/-- The payload of a 4-aligned base plus four times a word (`addrU`) is 4-aligned. -/
theorem addrU_al {base : Nat} (hb : base % 4 = 0) {i x : BitVec 64}
    (h : Epilogue.addrU base i = .bits 64 x) : (truncBits 64 x).toNat % 4 = 0 := by
  simp only [Epilogue.addrU, Value.bits.injEq, true_and] at h
  subst h
  rw [show (i32 4).toNat = 4 by decide]
  simp only [lo4_trunc64, BitVec.toNat_add]
  rw [Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2 ^ 64), Nat.add_mod, lo4_trunc64, lo4_trunc64,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2 ^ 64),
    Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2 ^ 64)]
  omega

/-- The payload of a 4-aligned base plus four times a signed word (`addrS`) is 4-aligned. -/
theorem addrS_al {base : Nat} (hb : base % 4 = 0) {i x : BitVec 64}
    (h : Epilogue.addrS base i = .bits 64 x) : (truncBits 64 x).toNat % 4 = 0 := by
  simp only [Epilogue.addrS, Value.bits.injEq, true_and] at h
  subst h
  rw [show toSigned 32 (i32 4) = 4 by decide, show 2 * 32 = 64 by rfl]
  simp only [lo4_trunc64, BitVec.toNat_add]
  rw [Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2 ^ 64), Nat.add_mod, lo4_trunc64, lo4_trunc64,
    lo4_trunc64, BitVec.toNat_ofNat, BitVec.toNat_ofInt,
    Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2 ^ 64)]
  simp only [Nat.reducePow, Nat.cast_ofNat]
  omega


/-- A global load of one word through a register holding a 4-aligned 64-bit address. -/
theorem ldG_ok {A : List Assumption} {t : TState} {d r : Nat} {off : Int} {x : BitVec 64}
    (hr : t.regs r = some (.bits 64 x)) (h4 : (truncBits 64 x).toNat % 4 = 0)
    (ho : off % 4 = 0) (f : Fault) : loadTmpl A L g t .global false 32 [d] r off ≠ .ub f :=
  PTX.Flow.ldGlobal_ok hr (by omega) f

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
