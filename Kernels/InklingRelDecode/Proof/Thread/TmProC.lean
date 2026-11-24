-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmCopy
public import Kernels.InklingRelDecode.Proof.Thread.ShapeCopyEvent

@[expose] public section

/-! # The prologue's tensor copies are not undefined behaviour

The twelve K/V copies of the preload (`ptcSite i`, sites `ptc0_0` … `ptc2_3`), by `kvCopy_ok`:

* the map register `%rd1` is the inherited pointer to `param_1` (`dt.pro.rest 1949`);
* the destination is `sharedBase + 16384 h + 32768 (i / 4) + 98304 (i % 2) +
  8192 (i % 4 / 2)` with `h = half dt (i / 4) < 2` (`copyDst_form`), a multiple of 128
  (`Pre.sharedAlignment`) for either half;
* the barrier is `kv_ready (i / 4)`, 8-aligned;
* the box column is `(64 h + 128 (i % 2) + head_cols · kvh) % 2 ^ 32` (`copyX_form`), a
  multiple of 8 when `head_cols` is (`Pre.headColsAlign`, through `dt.pro.w70`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Tm
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-- The map operand of the tensor copy at `pc`. -/
def ptcMap (pc : Nat) : Opnd :=
  match kernel.code[pc]? with
  | some ⟨_, .cpTensor _ _ _ _ map _ _ _ _ _ _⟩ => map
  | _ => .imm 0

theorem ptc_map : ∀ i < 12, ptcMap (ptcSite i).pc = .reg 1949 ∧
    1949 ∈ Flow.live (ptcSite i).pc := by decide +kernel

/-- **A prologue copy is not undefined behaviour.** -/
theorem ptc_ok (hpre : Pre Q L mem0) (hg : g < L.threads) {i : Nat} (hi : i < 12) {dt : Dat}
    {ins : Instr}
    (hrd1 : dt.pro.rest 1949 = .ptr 64 true (.param (param "1")) 0)
    (hw70 : dt.pro.w70 % 8 = 0) (hH : Holds t.regs (facts L g ⟨ptcSite i, dt⟩))
    (hc : kernel.code[(ptcSite i).pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hsa := hpre.sharedAlignment
  have hsr := hpre.sharedRange
  unfold sharedBytes at hsr
  have hS : SbRoom L := by unfold SbRoom; omega
  obtain ⟨p, map, hcode⟩ := isPtc_spec (ptc_isPtc i hi)
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  obtain ⟨hm1, hml⟩ := ptc_map i hi
  have hmap' : map = .reg 1949 := by
    rw [← hm1]
    simp [ptcMap, hcode]
  subst hmap'
  obtain ⟨⟨xd, hxd, hxdl⟩, ⟨xx, hxx, hxxl⟩, ⟨xy, hxy, hxyl⟩⟩ := ptc_bits L g dt i hi
  obtain ⟨hl1, hl2, hl3, hl4⟩ := ptc_live i hi
  have hmap : t.regs 1949 = some (.ptr 64 true (.param (param "1")) 0) :=
    holds_reg hH hml (by rw [valueOf_1949, hrd1])
  have hr1 : t.regs (ptcDst (ptcSite i).pc) = some (b32 xd.toNat) := by
    rw [← bits32_eq xd hxdl]
    exact holds_reg hH hl1 hxd
  have hr2 : t.regs (ptcCoord (ptcSite i).pc 0) = some (b32 xx.toNat) := by
    rw [← bits32_eq xx hxxl]
    exact holds_reg hH hl2 hxx
  have hr3 : t.regs (ptcCoord (ptcSite i).pc 1) = some (b32 xy.toNat) := by
    rw [← bits32_eq xy hxyl]
    exact holds_reg hH hl3 hxy
  have hoff : (kvReadyOf (i / 4)).off = 213216 + 8 * (i / 4 % 3) := rfl
  have hr4 : t.regs (ptcMb (ptcSite i).pc) =
      some (b32 ((L.sharedBase + (kvReadyOf (i / 4)).off) % 2 ^ 32)) := by
    refine holds_reg hH hl4 ?_
    rw [ptc_mb i hi, val_init L g dt (2 * (i / 4)) (by omega), ptc_initBar i hi]
  have hcd : copyDst L g dt i = xd.toNat := by simp [copyDst, wordOf, hxd]
  have hcx : copyX L g dt i = xx.toNat := by simp [copyX, wordOf, hxx]
  have hdf := copyDst_form L g dt hS hi
  have hxf := copyX_form L g dt hi
  have := half_lt dt (i / 4)
  rw [hcd] at hdf
  rw [hcx] at hxf
  have hm8 : dt.pro.w70 * (cta L g .y % 2 ^ 32) % 8 = 0 := by
    rw [Nat.mul_mod, hw70, Nat.zero_mul, Nat.zero_mod]
  have hcta : g / L.block < L.grid := by
    rw [Launch.threads] at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  have h3 : i / 4 % 3 < 3 := Nat.mod_lt _ (by decide)
  refine kvCopy_ok hpre hcta hmap hr1 hr4 hr2 hr3 hxdl (Nat.mod_lt _ (by decide)) hxxl hxyl
    ?_ ?_ ?_ f
  · rw [hdf]
    omega
  · rw [hoff]
    omega
  · rw [hxf]
    unfold colOf
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
