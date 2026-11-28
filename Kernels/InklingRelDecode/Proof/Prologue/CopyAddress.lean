-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Route
public import Kernels.InklingRelDecode.Proof.Lib.AddBase
import Lemmas.Flow.Bits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

noncomputable section

def copyBase (L : Launch) (v : Value) :=
  add32 (W (L.sharedBase%2^32)) (shl (andi (Lib.word v) 1) 14)

def copyOffset (b : Fin 3) (j : Fin 4) := 32768*b.val+98304*(j.val%2)+8192*(j.val/2)

theorem offset_bound (b : Fin 3) (j : Fin 4) : copyOffset b j≤172032 := by
  revert b j; decide +kernel

/-- The low bit of an arbitrary broadcast selects one of the two half tiles. -/
theorem copy_base_value {L : Launch} (v : Value) (room : L.sharedBase+213340≤2^18) :
    copyBase L v=BitVec.ofNat 64 (L.sharedBase+16384*((Lib.word v).toNat%2)) := by
  unfold copyBase
  generalize Lib.word v=z
  rw [show z=BitVec.ofNat 64 z.toNat by simp]
  nf_simp [add32,r32,shl,andi,i32,W,Nat.and_one_is_mod]
  omega

theorem copy_interval {L : Launch} (v : Value) (b : Fin 3) (j : Fin 4)
    (room : L.sharedBase+213340≤2^18) :
    let dst := (addi (copyBase L v) (copyOffset b j : Int)).toNat
    L.sharedBase≤dst ∧ dst+8192≤L.sharedBase+196608 := by
  dsimp only
  rw [copy_base_value v room]
  have maxOff := offset_bound b j
  generalize copyOffset b j=off at maxOff ⊢
  nf_simp [addi,add32,r32,i32]
  rw [Int.emod_eq_of_lt (by omega : 0≤(off : Int)) (by omega : (off : Int)<18446744073709551616)]
  simp only [Int.toNat_natCast]
  omega

/-- A preload box starts at the half tile of the broadcast's low bit plus the site's offset. -/
theorem copy_dest_value {L : Launch} (v : Value) (b : Fin 3) (j : Fin 4)
    (room : L.sharedBase+213340≤2^18) :
    (addi (copyBase L v) (copyOffset b j : Int)).toNat =
      L.sharedBase+16384*((Lib.word v).toNat%2)+copyOffset b j := by
  rw [copy_base_value v room]
  have maxOff := offset_bound b j
  generalize copyOffset b j=o at maxOff ⊢
  nf_simp [addi,add32,r32,i32]
  rw [Int.emod_eq_of_lt (by omega : 0≤(o : Int)) (by omega : (o : Int)<18446744073709551616)]
  simp only [Int.toNat_natCast]
  have hw : (Lib.word v).toNat%2<2 := Nat.mod_lt _ (by omega)
  generalize (Lib.word v).toNat%2=w at hw ⊢
  rw [Nat.mod_eq_of_lt (by omega : L.sharedBase+16384*w<4294967296),
    Nat.mod_eq_of_lt (by omega : o<4294967296),
    Nat.mod_eq_of_lt (by omega : L.sharedBase+16384*w+o<4294967296)]

/-- A preload box lies in the K tile or the V tile of its slot. -/
theorem copy_slot_interval {L : Launch} (v : Value) (b : Fin 3) (j : Fin 4)
    (room : L.sharedBase+213340≤2^18) :
    let dst := (addi (copyBase L v) (copyOffset b j : Int)).toNat
    (L.sharedBase+32768*b.val≤dst ∧ dst+8192≤L.sharedBase+32768*(b.val+1)) ∨
      (L.sharedBase+98304+32768*b.val≤dst ∧
        dst+8192≤L.sharedBase+98304+32768*(b.val+1)) := by
  dsimp only
  rw [copy_base_value v room]
  have maxOff := offset_bound b j
  have jb := j.isLt
  have bb := b.isLt
  have off : copyOffset b j=32768*b.val+98304*(j.val%2)+8192*(j.val/2) := rfl
  generalize copyOffset b j=o at maxOff off ⊢
  nf_simp [addi,add32,r32,i32]
  rw [Int.emod_eq_of_lt (by omega : 0≤(o : Int)) (by omega : (o : Int)<18446744073709551616)]
  simp only [Int.toNat_natCast]
  have hw : (Lib.word v).toNat%2<2 := Nat.mod_lt _ (by omega)
  generalize (Lib.word v).toNat%2=w at hw ⊢
  rw [Nat.mod_eq_of_lt (by omega : L.sharedBase+16384*w<4294967296),
    Nat.mod_eq_of_lt (by omega : o<4294967296),
    Nat.mod_eq_of_lt (by omega : L.sharedBase+16384*w+o<4294967296)]
  have hj : j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 := by omega
  have hb : b.val=0 ∨ b.val=1 ∨ b.val=2 := by omega
  rcases hj with h|h|h|h <;> rcases hb with h'|h'|h' <;> simp only [h,h'] at off ⊢ <;> omega

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
