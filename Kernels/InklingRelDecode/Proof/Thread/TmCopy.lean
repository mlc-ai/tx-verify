-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmBase
public import Kernels.InklingRelDecode.Proof.Geometry
public import Lemmas.Flow.TcTmpl

@[expose] public section

/-! # A K/V tensor copy is not undefined behaviour

The kernel's tensor copies (`cp.async.bulk.tensor.2d.shared::cta.global.tile`, the loader's eight
and the prologue's twelve) have one form: the map is the parameter `param_1` (`%rd1`, register
1949), the destination and the barrier are 32-bit shared registers, the box origin is two 32-bit
coordinate registers `(col, row)`, no multicast and no cache policy. `kvCopy_ok`: the template
is not undefined behaviour when

* `%rd1` is the generic address of `param_1` (the map `kv_desc`: `Pre.paramKv`,
  `Pre.mapAlignment`, `Pre.mapRange`, `Pre.mapKvBind`, valid by `mapKv_valid`),
* the destination is 128-aligned and the barrier 8-aligned,
* the column is a multiple of 8 (`bf16` elements: the box start is 16-byte aligned,
  `TensorDescriptor.BoxAligned`); the row is any 32-bit word,
* the copy stays in the issuer's CTA (`TensorRoute` of a non-cluster `cta_group::1` copy).

The coordinates are read as signed 32-bit integers; a multiple of 8 below `2 ^ 32` stays a
multiple of 8 as such. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {A : List Assumption} {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-- The signed reading of a 32-bit multiple of 8 is a multiple of 8. -/
theorem toInt_mul8 {c : Nat} (hc : c < 2 ^ 32) (h8 : c % 8 = 0) :
    (BitVec.ofNat 32 (BitVec.ofNat 64 c).toNat).toInt * 2 % 16 = 0 := by
  have h64 : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [h64, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  split <;> omega

/-- **A K/V tensor copy into the CTA's window is not undefined behaviour.** -/
theorem kvCopy_ok (hpre : Pre Q L mem0) (hcta : g / L.block < L.grid)
    {dst mb rc rr dv bv cv rv : Nat}
    (hmap : t.regs 1949 = some (.ptr 64 true (.param (param "1")) 0))
    (hd : t.regs dst = some (b32 dv)) (hb : t.regs mb = some (b32 bv))
    (hcr : t.regs rc = some (b32 cv)) (hr : t.regs rr = some (b32 rv))
    (hdv : dv < 2 ^ 32) (hbv : bv < 2 ^ 32) (hcv : cv < 2 ^ 32) (hrv : rv < 2 ^ 32)
    (h128 : dv % 128 = 0) (h8 : bv % 8 = 0) (hcol : cv % 8 = 0) (f : Fault) :
    eventTmpl A L g t (.cpTensor false false dst 0 (.reg 1949) [.reg rc, .reg rr] mb 0 none
      .tile none) ≠ .ub f := by
  have hal := hpre.mapAlignment
  have hrg := hpre.mapRange
  have hma : tensorMapAddress L g t (.reg 1949) = .ok Q.kvMap := by
    simp only [tensorMapAddress, readValue, readReg, hmap, hpre.paramKv, bind, Except.bind,
      pure, Except.pure]
    simp [mapParam, ParamObjectDecl.bytes]
    omega
  have hval := mapKv_valid hpre.kvAlign hpre.slotStridePos hpre.slotStrideAlign
    hpre.slotStrideRange hpre.rowsPos hpre.rowsRange
  have hm : tensorMap L g t (.reg 1949) [.reg rc, .reg rr] .tile =
      .ok (Q.kvMap, ⟨1, mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩) := by
    simp [tensorMap, hma, hpre.mapKvBind, hval, bind, Except.bind, pure, Except.pure]
    omega
  have hsh : sharedEffAddr L g t false dst 0 = .ok ⟨.shared, g / L.block, dv⟩ := by
    have := effAddr_b32 (L := L) (g := g) (t := t) hd hdv
    simpa [effAddr] using this
  have hmb : mbarLoc L g t mb 0 = .ok ⟨.shared, g / L.block, bv⟩ := by
    simp [mbarLoc, effAddr_b32 (L := L) (g := g) (t := t) hb hbv, h8, bind, Except.bind, pure,
      Except.pure]
  have hvs : [Opnd.reg rc, .reg rr].mapM (readBits L g t 32) =
      .ok [BitVec.ofNat 64 cv, BitVec.ofNat 64 rv] := by
    simp [readBits_b32 (L := L) (g := g) hcr hcv, readBits_b32 (L := L) (g := g) hr hrv, bind,
      Except.bind, pure, Except.pure]
  have hbox : requireBoxAligned (mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass)
      (fun axis => (BitVec.ofNat 32 ([BitVec.ofNat 64 cv, BitVec.ofNat 64 rv].getD axis.val
        0).toNat).toInt) = .ok () := by
    refine (requireBoxAligned_eq_ok _ _).2 ?_
    unfold TensorDescriptor.BoxAligned
    exact toInt_mul8 hcv hcol
  have hin : CtaInCluster L (g / L.block) (g / L.block) := ⟨hcta, hcta, rfl⟩
  have hroute : TensorRoute L (g / L.block) false .one ⟨.shared, g / L.block, dv⟩
      ⟨.shared, g / L.block, bv⟩ := by
    refine ⟨hpre.launchValid.1, rfl, rfl, hin, hin, fun _ => ⟨rfl, rfl⟩, ?_⟩
    rw [sameCtaGroup_iff]
    exact ⟨hin, rfl⟩
  have h128' : (⟨.shared, g / L.block, dv⟩ : Loc).addr % 128 = 0 := h128
  simp only [eventTmpl, tensorTmpl, cachePolicyRead, tensorLoadCopy, hm, hsh, hmb, hvs, hbox,
    h128', TensorMode.transfer, TensorMode.rowCoordinates, bind, Except.bind, pure, Except.pure,
    ↓reduceIte, Bool.false_eq_true]
  simp [hroute, ofExec]

end
end PTX.Kernels.InklingRelDecode.Proof.Tm
