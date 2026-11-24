-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteRegs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Lse

@[expose] public section

/-! # The LSE address calculation independent of the numeric LSE value -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame
open Wg0 (eOf qOf)

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The immutable pointer and lane coordinates used to compute a row's LSE address. -/
def lseAddressFacts (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(2991, .ptr 64 false (.param (param "0")) 0),
    (460, b32 (eOf L g)), (459, b32 (qOf L g)), (463, b32 (tidOf L g % 128))]

/-- A local scalar-parameter load keeps the existing independent register facts. -/
theorem lse_param_vector (hpre : Pre P L mem0) {pc off w dst : Nat} {t : TState}
    {F : List (Nat × Value)} (ha : AtVector t pc F t.sub t.acc)
    (hnew : ∀ q ∈ F, q.1 ≠ dst)
    (hc : kernel.code[pc]? = some ⟨none, .mem (Thread.paramLoad (.int .b w) off 2991 dst)⟩)
    (hptr : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0))
    (hsup : ParamSupplied L (param "0") off (w / 8))
    (hsize : off + w / 8 ≤ 304)
    (hal : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ (8 : Nat) % (w / 8) = 0)
    (hNoAdd : pc ∉ paramAdds) (hNoPrefetch : pc ∉ prefetchTensorMapSites)
    (hrule : (Thread.paramLoad (.int .b w) off 2991 dst).rule = some .threadMove) :
    ∃ u, run kernel Assumptions.all L g 1 t = some u ∧
      AtVector u (pc + 1) ((dst, paramElem w w (paramNat L (param "0") off (w / 8))) :: F)
        t.sub t.acc := by
  have hl : ∀ a ∈ Assumptions.all,
      a.localRule L g t (.mem (Thread.paramLoad (.int .b w) off 2991 dst)) = none := by
    exact Thread.asms_localRule_mem (t := t) (by rw [ha.1]; exact hNoAdd)
      (by rw [ha.1]; exact hNoPrefetch)
  have hsf : Assumption.SegFreePc Assumptions.all t.pc := fun a ha l i state _ =>
    asms_segment_free (L := l) (g := i) state a ha
  let x := paramElem w w (paramNat L (param "0") off (w / 8))
  let u := PTX.next (setReg t dst x)
  have hExec := Thread.exec_ldParamReg (A := Assumptions.all) (L := L) (g := g)
    (w := w) (off := off) (r := 2991) (d := dst) (t := t) (p := param "0") (ty := .int .b w)
    (decl := scalarsParam) (base := P.param0Base) hptr hpre.param0Object
    ⟨by omega, hsize⟩ hal hsup hsf hl rfl hrule
  have hLocal : (Op.mem (Thread.paramLoad (.int .b w) off 2991 dst)).isLocal = true := rfl
  refine ⟨u, ?_, ?_⟩
  · simp only [run, tauStep, out, ha.1, ha.2.2.2.1, hc, guardHolds, hLocal, ↓reduceIte, hExec, u, x]
    rfl
  · refine ⟨by change t.pc + 1 = pc + 1; rw [ha.1], rfl, rfl, ha.2.2.2.1, ?_, ?_⟩
    · simp [u, x, PTX.next, setReg]
    · exact holds_update ha.2.2.2.2 hnew

private theorem lse_signed {a : Nat} (ha : a < 2 ^ 31) :
    toSigned 32 (truncBits 32 (BitVec.ofNat 64 a)) = (a : Int) := by
  have h32 : a < 2 ^ 32 := by omega
  have h64 : a < 2 ^ 64 := by omega
  rw [truncBits_ofNat h32 (by decide)]
  rw [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32]
  change (if a < 2 ^ 31 then (a : Int) else (a : Int) - 2 ^ 32) = (a : Int)
  rw [ite_eq_left ha]

/-- The concrete LSE store's address lies within the launch's LSE allocation. -/
theorem lse_loc_extent (_hpre : Pre P L mem0) (hb : eOf L g < P.b) (hq : qOf L g < P.s_q) :
    P.lseBase ≤ (Wg0.lseLocOf P L g).addr ∧
      (Wg0.lseLocOf P L g).addr + 4 ≤ P.lseBase + lseBytes P := by
  have hrow : eOf L g * P.s_q + qOf L g < P.b * P.s_q := calc
    _ < eOf L g * P.s_q + P.s_q := Nat.add_lt_add_left hq _
    _ = (eOf L g + 1) * P.s_q := by simp [Nat.add_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hb
  have hh := Wg0.head_lt L g
  change P.lseBase ≤ P.lseBase + 4 * ((eOf L g * P.s_q + qOf L g) * 64 + Wg0.head L g) ∧
    P.lseBase + 4 * ((eOf L g * P.s_q + qOf L g) * 64 + Wg0.head L g) + 4 ≤
      P.lseBase + lseBytes P
  rw [lseBytes, show 4 * P.b * P.s_q * 64 = 4 * ((P.b * P.s_q) * 64) by ac_rfl]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Executing the address-only epilogue code yields the actual LSE destination register. -/
theorem lse_address_vector (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (hFirst : tidOf L g % 128 < 64) {t : TState}
    (ha : AtVector t 1167 (lseAddressFacts L g) t.sub t.acc) :
    ∃ u, run kernel Assumptions.all L g 11 t = some u ∧
      AtVector u 1178 [(3574, b64 (Wg0.lseLocOf P L g).addr)] t.sub t.acc := by
  have hHead : Wg0.head L g = tidOf L g % 128 := by
    rw [Wg0.head_tid, Nat.mod_eq_of_lt hFirst]
  have hSum : eOf L g * (P.s_q * 64) + tidOf L g % 128 + qOf L g * 64 =
      (eOf L g * P.s_q + qOf L g) * 64 + Wg0.head L g := by
    simp only [← Nat.mul_assoc, Nat.add_mul, hHead, Nat.add_right_comm]
  have hExtent := (lse_loc_extent hpre hb hq).2
  have hMem := hpre.tensorRange.2.2
  have hFull : (Wg0.lseLocOf P L g).addr < 2 ^ 64 := by omega
  change P.lseBase + 4 * ((eOf L g * P.s_q + qOf L g) * 64 + Wg0.head L g) < 2 ^ 64 at hFull
  have hAddr : P.lseBase + 4 * (eOf L g * (P.s_q * 64) + tidOf L g % 128 + qOf L g * 64)
      < 2 ^ 64 := hSum.symm ▸ hFull
  have hBase : P.lseBase < 2 ^ 64 := by omega
  have hs : P.s_q * 64 < 2 ^ 31 := by have hh := hpre.qoBatchStrideRange; omega
  have he : eOf L g < 2 ^ 31 := lt_trans hb hpre.bLt
  have hq31 : qOf L g < 2 ^ 31 := lt_trans hq hpre.sqLt
  have hewide : eOf L g * (P.s_q * 64) < 2 ^ 64 := by omega
  have hqwide : qOf L g * 64 < 2 ^ 64 := by omega
  have hp96 : paramElem 64 64 (paramNat L (param "0") 96 8) = b64 P.lseBase := by
    change b64 (Thread.paramWord L 96 8) = b64 P.lseBase
    rw [Thread.paramWord_eight (fun i hi => hpre.paramLse i hi), Nat.mod_eq_of_lt hBase]
  have hp180 : paramElem 32 32 (paramNat L (param "0") 180 4) = b32 (P.s_q * 64) := by
    change b32 (Thread.paramWord L 180 4) = b32 (P.s_q * 64)
    rw [Thread.paramWord_four (fun i hi => hpre.paramStrideLseB i hi),
      Nat.mod_eq_of_lt (by omega : P.s_q * 64 < 2 ^ 32)]
  have hp184 : paramElem 32 32 (paramNat L (param "0") 184 4) = b32 64 := by
    change b32 (Thread.paramWord L 184 4) = b32 64
    rw [Thread.paramWord_four (fun i hi => hpre.paramStrideLseSq i hi)]
    rfl
  obtain ⟨t1, h1, ht1⟩ := lse_param_vector (g := g) (dst := 3566) hpre ha
    (by simp [lseAddressFacts]) Flow.code_1167 ha.2.2.2.2.1
    (Wg0.supplied_ptr hpre.paramLse (by decide)) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) rfl
  rw [hp96] at ht1
  obtain ⟨t2, h2, ht2⟩ : ∃ u, run kernel Assumptions.all L g 1 t1 = some u ∧
      AtVector u 1169 ((3567, b64 P.lseBase) :: lseAddressFacts L g) t.sub t.acc := by
    simp only [lseAddressFacts] at ht1 ⊢
    seg_fp ht1 using norm_bits []
  have ht2' : AtVector t2 1169 ((3567, b64 P.lseBase) :: lseAddressFacts L g) t2.sub t2.acc :=
    ⟨ht2.1, rfl, rfl, ht2.2.2.2.1, ht2.2.2.2.2⟩
  obtain ⟨t3, h3, ht3⟩ := lse_param_vector (g := g) (dst := 1734) hpre ht2'
    (by simp [lseAddressFacts]) Flow.code_1169 ht2.2.2.2.2.2.1
    (Wg0.supplied_int hpre.paramStrideLseB (by decide)) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) rfl
  rw [hp180] at ht3
  obtain ⟨t4, h4, ht4⟩ : ∃ u, run kernel Assumptions.all L g 1 t3 = some u ∧
      AtVector u 1171 ((3568, b64 (eOf L g * (P.s_q * 64))) :: (3567, b64 P.lseBase) ::
        lseAddressFacts L g) t2.sub t2.acc := by
    simp only [lseAddressFacts] at ht3 ⊢
    seg_fp ht3 using
      (change Value.bits 64 (truncBits 64 (BitVec.ofInt 64
        (toSigned 32 (truncBits 32 (BitVec.ofNat 64 (P.s_q * 64))) *
          toSigned 32 (truncBits 32 (BitVec.ofNat 64 (eOf L g)))))) =
        b64 (eOf L g * (P.s_q * 64)))
      (rw [lse_signed hs, lse_signed he, ← Int.natCast_mul, BitVec.ofInt_natCast,
        Nat.mul_comm (P.s_q * 64) (eOf L g), truncBits_ofNat hewide (by decide)]; rfl)
  have ht4' : AtVector t4 1171 ((3568, b64 (eOf L g * (P.s_q * 64))) ::
      (3567, b64 P.lseBase) :: lseAddressFacts L g) t4.sub t4.acc :=
    ⟨ht4.1, rfl, rfl, ht4.2.2.2.1, ht4.2.2.2.2⟩
  obtain ⟨t5, h5, ht5⟩ := lse_param_vector (g := g) (dst := 1735) hpre ht4'
    (by simp [lseAddressFacts]) Flow.code_1171 ht4.2.2.2.2.2.2.1
    (Wg0.supplied_int hpre.paramStrideLseSq (by decide)) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) rfl
  rw [hp184] at ht5
  obtain ⟨u, h6, hu⟩ : ∃ u, run kernel Assumptions.all L g 6 t5 = some u ∧
      AtVector u 1178 [(3574, b64 (Wg0.lseLocOf P L g).addr)] t4.sub t4.acc := by
    simp only [lseAddressFacts] at ht5
    seg_fp ht5 using
      (change _ = b64 (P.lseBase + 4 * ((eOf L g * P.s_q + qOf L g) * 64 + Wg0.head L g)))
      (rw [← hSum])
      (norm_signed [])
  refine ⟨u, run_comp (run_comp (run_comp (run_comp (run_comp h1 h2) h3) h4) h5) h6, ?_⟩
  exact ⟨hu.1, hu.2.1.trans (ht4.2.1.trans ht2.2.1),
    hu.2.2.1.trans (ht4.2.2.1.trans ht2.2.2.1), hu.2.2.2.1, hu.2.2.2.2⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
