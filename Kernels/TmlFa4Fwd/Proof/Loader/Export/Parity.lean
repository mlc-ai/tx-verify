-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape

@[expose] public section

/-! # The parity of the loader's polls of the K/V empty barriers

At a poll of an empty slot, for packet `j` (`pkOf per v k` at a `slot` site, `A + j` at the
drain's `dw j`), the poll's parity is `(j / 3 + 1) % 2` (`slot_par`, `dw_par`): the first block's
polls pass parity 1 on the fresh barriers, the later ones read the ring's parity word, which the
reference invariant states (`SlotIs`: `slot = j % 3`, `par = (j / 3 + 1) % 2`), or its successor
(`npar`). With the empty polls' count `j / 3` of slot `j % 3` before it, the parity is the count
plus one. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32 r32)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {g w : Nat}

theorem npar_eq : ∀ a < 3, ∀ b < 2,
    npar (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) =
      BitVec.ofNat 64 (if a = 2 then 1 - b else b) := by
  decide

theorem nslot_eq : ∀ a < 3, nslot (BitVec.ofNat 64 a) = BitVec.ofNat 64 ((a + 1) % 3) := by
  decide

theorem trunc_small {n : Nat} (h : n < 2) : (truncBits 32 (BitVec.ofNat 64 n)).toNat % 2 = n := by
  simp only [truncBits, BitVec.toNat_ofNat]
  omega

/-- The ring's parity word for packet `j`. -/
theorem slotIs_par {v : V} {j : Nat} (h : SlotIs v j) :
    (truncBits 32 v.par).toNat % 2 = (j / 3 + 1) % 2 := by
  rw [h.2]; exact trunc_small (by omega)

/-- Its successor: the parity word for packet `j + 1`. -/
theorem slotIs_npar {v : V} {j : Nat} (h : SlotIs v j) :
    npar v.slot v.par = BitVec.ofNat 64 (((j + 1) / 3 + 1) % 2) := by
  rw [h.1, h.2, npar_eq _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))]
  congr 1
  split <;> omega

theorem slotIs_nslot {v : V} {j : Nat} (h : SlotIs v j) :
    nslot v.slot = BitVec.ofNat 64 ((j + 1) % 3) := by
  rw [h.1, nslot_eq _ (Nat.mod_lt _ (by decide))]
  congr 1
  omega

/-- The parity word for packet `j + 2`. -/
theorem slotIs_npar2 {v : V} {j : Nat} (h : SlotIs v j) :
    npar (nslot v.slot) (npar v.slot v.par) = BitVec.ofNat 64 (((j + 2) / 3 + 1) % 2) := by
  rw [slotIs_nslot h, slotIs_npar h, npar_eq _ (Nat.mod_lt _ (by decide)) _
    (Nat.mod_lt _ (by decide))]
  congr 1
  split <;> omega

/-- The ring's count at slot `s` among `n` packets. -/
theorem ringCnt_eq (n s : Nat) (hs : s < 3) :
    ringCnt n s = n / 3 + if s < n % 3 then 1 else 0 := by
  induction n with
  | zero => simp [ringCnt]
  | succ n ih =>
    rw [ringCnt_succ, ih]
    split_ifs <;> omega

theorem ringCnt_mod (n : Nat) : ringCnt n (n % 3) = n / 3 := by
  rw [ringCnt_eq n _ (Nat.mod_lt _ (by decide))]
  simp

set_option maxHeartbeats 4000000 in
/-- **The parity of a poll of an empty slot** at a `slot` site of packet `pkOf per v k`. -/
theorem slot_par {per : Per} {vv : Bool} {v : V} {kk : Fin 2} {k A : Nat}
    (hR : RefRing p L g w ⟨.slot per vv, v, kk⟩ k A) :
    (truncBits 32 (rv p L g w ⟨.slot per vv, v, kk⟩ (waitRegs (.slot per vv)).2)).toNat % 2 =
      (pkOf per vv k / 3 + 1) % 2 := by
  obtain ⟨-, hR⟩ := hR
  cases per <;> cases vv <;> simp only [ringCls, RingWords] at hR
  · have hv : rv p L g w ⟨.slot .prime false, v, kk⟩ (waitRegs (.slot .prime false)).2 = i32 1 :=
      rfl
    rw [hv, show (truncBits 32 (i32 1)).toNat % 2 = 1 from by decide]
    simp [pkOf]
  · have hv : rv p L g w ⟨.slot .prime true, v, kk⟩ (waitRegs (.slot .prime true)).2 = i32 1 :=
      rfl
    rw [hv, show (truncBits 32 (i32 1)).toNat % 2 = 1 from by decide]
    simp [pkOf]
  · have hv : rv p L g w ⟨.slot .warm false, v, kk⟩ (waitRegs (.slot .warm false)).2 = v.par :=
      rfl
    rw [hv]
    simpa [pkOf] using slotIs_par hR.1.1
  · have hv : rv p L g w ⟨.slot .warm true, v, kk⟩ (waitRegs (.slot .warm true)).2 =
        npar v.slot v.par :=
      rfl
    rw [hv]
    rw [slotIs_npar hR.1.1]
    simpa [pkOf] using trunc_small (n := ((k + 1) / 3 + 1) % 2) (by omega)
  · have hv : rv p L g w ⟨.slot .steady false, v, kk⟩ (waitRegs (.slot .steady false)).2 = v.par :=
      rfl
    rw [hv]
    simpa [pkOf] using slotIs_par hR.1
  · have hv : rv p L g w ⟨.slot .steady true, v, kk⟩ (waitRegs (.slot .steady true)).2 =
        npar v.slot v.par :=
      rfl
    rw [hv]
    rw [slotIs_npar hR.1]
    simpa [pkOf] using trunc_small (n := ((k + 1) / 3 + 1) % 2) (by omega)

set_option maxHeartbeats 4000000 in
/-- **The parity of a drain poll of an empty slot** at `dw j`, for packet `A + j`. -/
theorem dw_par {j : Fin 3} {v : V} {kk : Fin 2} {k A : Nat}
    (hR : RefRing p L g w ⟨.dw j, v, kk⟩ k A) :
    (truncBits 32 (rv p L g w ⟨.dw j, v, kk⟩ (waitRegs (.dw j)).2)).toNat % 2 =
      ((A + j.val) / 3 + 1) % 2 := by
  obtain ⟨-, hR⟩ := hR
  simp only [ringCls, RingWords] at hR
  fin_cases j <;> simp only [Fin.isValue, Fin.reduceFinMk, Fin.val_zero, Fin.val_one,
    Fin.val_two, Nat.add_zero]
  · have hv : rv p L g w ⟨.dw 0, v, kk⟩ (waitRegs (.dw 0)).2 = v.par := rfl
    rw [hv]
    simpa using slotIs_par hR
  · have hv : rv p L g w ⟨.dw 1, v, kk⟩ (waitRegs (.dw 1)).2 = npar v.slot v.par := rfl
    rw [hv, slotIs_npar hR]
    simpa using trunc_small (n := ((A + 1) / 3 + 1) % 2) (by omega)
  · have hv : rv p L g w ⟨.dw 2, v, kk⟩ (waitRegs (.dw 2)).2 =
        npar (nslot v.slot) (npar v.slot v.par) := rfl
    rw [hv, slotIs_npar2 hR]
    simpa using trunc_small (n := ((A + 2) / 3 + 1) % 2) (by omega)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
