-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.Regs
import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Lemmas.Flow.TcTmpl
import Lemmas.Flow.TensorLoadFacts
import Lemmas.Flow.Events
import Lemmas.Flow.TmplOkSync
import Lemmas.Flow.TensorStoreOrigin
import Lemmas.Flow.Step.ShapeClasses
import Lemmas.Flow.Next

@[expose] public section

/-! # A K/V tensor copy into the CTA's window is not undefined behaviour

The loader's eight and the prologue's twelve copies have one form: the map is the parameter
`param_1` (register 1949), the destination and the box origin are 32-bit shared registers, no
multicast and no cache policy. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof

noncomputable section
set_option maxRecDepth 100000

variable {A : List Assumption} {Q : Params} {L : Launch} {m : Mem0} {g : Nat} {t : TState}

theorem toInt_mul8 {c : Nat} (hc : c < 2 ^ 32) (h8 : c % 8 = 0) :
    (BitVec.ofNat 32 (BitVec.ofNat 64 c).toNat).toInt * 2 % 16 = 0 := by
  have h64 : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [h64, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  split <;> omega

/-- **A K/V tensor copy into the CTA's window is not undefined behaviour**: the map is the
parameter, the destination is 128-aligned, the barrier is a location of the CTA, the column is a
multiple of 8. -/
theorem cp_ok (hp : Pre Q L m) (hcta : g / L.block < L.grid) {dst mb rc rr dv cv rv bv : Nat}
    (hmap : t.regs 1949 = some (.ptr 64 true (.param (param "1")) 0))
    (hd : t.regs dst = some (b32 dv)) (hcr : t.regs rc = some (b32 cv))
    (hr : t.regs rr = some (b32 rv)) (hdv : dv < 2 ^ 32) (hcv : cv < 2 ^ 32) (hrv : rv < 2 ^ 32)
    (h128 : dv % 128 = 0) (hcol : cv % 8 = 0)
    (hmb : mbarLoc L g t mb 0 = .ok ⟨.shared, g / L.block, bv⟩) (f : Fault) :
    eventTmpl A L g t (.cpTensor false false dst 0 (.reg 1949) [.reg rc, .reg rr] mb 0 none
      .tile none) ≠ .ub f := by
  have hal := hp.mapAlignment
  have hrg := hp.mapRange
  have hma : tensorMapAddress L g t (.reg 1949) = .ok Q.kvMap := by
    simp only [tensorMapAddress, readValue, readReg, hmap, hp.paramKv, bind, Except.bind,
      pure, Except.pure]
    simp [mapParam, ParamObjectDecl.bytes]
    omega
  have hval := mapKv_valid hp.kvAlign hp.slotStridePos hp.slotStrideAlign
    hp.slotStrideRange hp.rowsPos hp.rowsRange
  have hm : tensorMap L g t (.reg 1949) [.reg rc, .reg rr] .tile =
      .ok (Q.kvMap, ⟨1, mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩) := by
    simp [tensorMap, hma, hp.mapKvBind, hval, bind, Except.bind, pure, Except.pure]
    omega
  have hsh : sharedEffAddr L g t false dst 0 = .ok ⟨.shared, g / L.block, dv⟩ :=
    sharedEffAddr_b32 hd hdv
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
    refine ⟨hp.launchValid.1, rfl, rfl, hin, hin, fun _ => ⟨rfl, rfl⟩, ?_⟩
    rw [sameCtaGroup_iff]
    exact ⟨hin, rfl⟩
  have h128' : (⟨.shared, g / L.block, dv⟩ : Loc).addr % 128 = 0 := h128
  simp only [eventTmpl, tensorTmpl, cachePolicyRead, tensorLoadCopy, hm, hsh, hmb, hvs, hbox,
    h128', TensorMode.transfer, TensorMode.rowCoordinates, bind, Except.bind, pure, Except.pure,
    ↓reduceIte, Bool.false_eq_true]
  simp [hroute, ofExec]

end
end PTX.Kernels.InklingRelDecode.Proof.Lib
