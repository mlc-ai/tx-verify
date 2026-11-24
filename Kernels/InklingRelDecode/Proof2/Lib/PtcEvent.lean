-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDProCopy
public import Kernels.InklingRelDecode.Proof.Thread.EvWBase
public import Kernels.InklingRelDecode.Proof.Thread.ShapeProCopy

@[expose] public section

/-!
# A prologue copy names the `kv_desc` map, from its map register

The prologue's twelve `cp.async.bulk.tensor` read their map operand from `%rd1` (register 1949,
`ptc_mapReg`, an audit by `decide +kernel`). Given that the register holds the pointer to the
kernel parameter `kv_desc`, which `Pre.paramKv` ties to `Q.kvMap`, the event is the tensor issue of
`Q.kvMap` with `EvW.kvCopySpec` (`ptc_event_map`). Moved from the first tree's
`Thread/ShapeCopyEvent.lean`, whose `ptc_event` names the startup's inherited registers; the
second tree's prologue states carry the register through their reference (`ProA.PRef.pro`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The instruction at `pc` is a tensor copy whose map operand is `%rd1` (register 1949). -/
def isMapReg (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨_, .cpTensor _ _ _ _ (.reg 1949) _ _ _ _ _ _⟩ => true
  | _ => false

theorem ptc_mapReg : ∀ i < 12, isMapReg (ProA.ptcSite i).pc = true := by decide +kernel

theorem ptc_live1949 : ∀ i < 12, 1949 ∈ Flow.live (ProA.ptcSite i).pc := by decide +kernel

theorem isMapReg_spec {pc : Nat} (h : isMapReg pc = true) {ins : Instr}
    (hc : kernel.code[pc]? = some ins) {ca grp : Bool} {dst : Nat} {off : Int} {map : Opnd}
    {cs : List Opnd} {mb : Nat} {moff : Int} {mc : Option (Nat × Opnd)} {lm : TensorMode}
    {pol : Option Opnd}
    (hop : ins.op = .cpTensor ca grp dst off map cs mb moff mc lm pol) : map = .reg 1949 := by
  unfold isMapReg at h
  rw [hc] at h
  obtain ⟨gd, op⟩ := ins
  simp only at hop
  subst hop
  cases map with
  | reg r =>
    by_cases hr : r = 1949
    · rw [hr]
    · exfalso
      revert h
      simp [hr]
  | _ => simp at h

theorem valueOf_1949 (dt : ProA.Dat) : ProA.valueOf L g dt 1949 = dt.pro.rest 1949 := by
  unfold ProA.valueOf
  have : (ProA.table L g dt).lookup 1949 = none := by rfl
  rw [this]
  rfl

/-- **A prologue copy is the tensor issue of `Q.kvMap`.** At the copy site `i`, given that the
inherited `%rd1` (register 1949) is the pointer to `kv_desc`, the event is the tensor issue of
the `kv_desc` map with `EvW.kvCopySpec` at the box origin `(copyX, copyY)` (words), the
destination `copyDst` and the barrier `kv_ready (i / 4)` of the thread's CTA. -/
theorem ptc_event_map (hpre : Pre Q L mem0) {d : ProA.D} {e : Event} {u : TState} {i : Nat}
    (hi : i < 12) (hmap : d.dt.pro.rest 1949 = .ptr 64 true (.param (param "1")) 0)
    (hF : ProA.Fired L g d e (some u)) (hs : d.site = ProA.ptcSite i) :
    e = ⟨ProA.evPc d.site, .tensorIssue Q.kvMap
      (EvW.kvCopySpec Q (g / L.block) (ProA.copyX L g d.dt i) (ProA.copyY L g d.dt i)
        (ProA.copyDst L g d.dt i) ((EvD.kvReadyOf (i / 4)).loc L (g / L.block)))⟩ := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := ProA.fired_unpack hF
  have hpc : d.site.pc = (ProA.ptcSite i).pc := by rw [hs]
  obtain ⟨p, map, hcode⟩ := ProA.isPtc_spec (ProA.ptc_isPtc i hi)
  rw [hpc] at hc hf
  have hins := Option.some.inj (hc.symm.trans hcode)
  have hop : ins.op = .cpTensor false false (ProA.ptcDst (ProA.ptcSite i).pc) 0 map
      [.reg (ProA.ptcCoord (ProA.ptcSite i).pc 0), .reg (ProA.ptcCoord (ProA.ptcSite i).pc 1)]
      (ProA.ptcMb (ProA.ptcSite i).pc) 0 none .tile none := congrArg Instr.op hins
  have hm1949 : map = .reg 1949 := isMapReg_spec (ptc_mapReg i hi) hcode rfl
  rw [hm1949] at hop
  rw [hop] at hf
  obtain ⟨⟨xd, hxd, hxdl⟩, ⟨xx, hxx, hxxl⟩, ⟨xy, hxy, hxyl⟩⟩ := ProA.ptc_bits L g d.dt i hi
  obtain ⟨hl1, hl2, hl3, hl4⟩ := ProA.ptc_live i hi
  have hr1 : t.regs (ProA.ptcDst (ProA.ptcSite i).pc) = some (b32 xd.toNat) := by
    rw [ProA.reg_at h (by rw [hpc]; exact hl1), hxd, ProA.bits32_eq xd hxdl]
  have hr2 : t.regs (ProA.ptcCoord (ProA.ptcSite i).pc 0) = some (b32 xx.toNat) := by
    rw [ProA.reg_at h (by rw [hpc]; exact hl2), hxx, ProA.bits32_eq xx hxxl]
  have hr3 : t.regs (ProA.ptcCoord (ProA.ptcSite i).pc 1) = some (b32 xy.toNat) := by
    rw [ProA.reg_at h (by rw [hpc]; exact hl3), hxy, ProA.bits32_eq xy hxyl]
  have hr4 : t.regs (ProA.ptcMb (ProA.ptcSite i).pc) =
      some (b32 ((L.sharedBase + (EvD.kvReadyOf (i / 4)).off) % 2 ^ 32)) := by
    rw [ProA.reg_at h (by rw [hpc]; exact hl4), ProA.ptc_mb i hi]
    have := ProA.val_init L g d.dt (2 * (i / 4)) (by omega)
    rw [this, ProA.ptc_initBar i hi]
  have hrm : t.regs 1949 = some (.ptr 64 true (.param (param "1")) 0) := by
    rw [ProA.reg_at h (by rw [hpc]; exact ptc_live1949 i hi)]
    rw [valueOf_1949, hmap]
  have hS := ProA.sharedOk_of_pre hpre
  have hmod : (L.sharedBase + (EvD.kvReadyOf (i / 4)).off) % 2 ^ 32 =
      L.sharedBase + (EvD.kvReadyOf (i / 4)).off := by
    apply Nat.mod_eq_of_lt
    have := hS.2
    have hlt : (EvD.kvReadyOf (i / 4)).off + 8 ≤ 213340 := EvD.Bar.off_lt _
    omega
  have hbv : (L.sharedBase + (EvD.kvReadyOf (i / 4)).off) % 2 ^ 32 < 2 ^ 32 :=
    Nat.mod_lt _ (by decide)
  obtain ⟨he, -⟩ := EvW.fires_kvCopy hpre hrm hr1 hr4 hr2 hr3 hxdl hbv hxxl hxyl hf
  have hcd : ProA.copyDst L g d.dt i = xd.toNat := by simp [ProA.copyDst, ProA.wordOf, hxd]
  have hcx : ProA.copyX L g d.dt i = xx.toNat := by simp [ProA.copyX, ProA.wordOf, hxx]
  have hcy : ProA.copyY L g d.dt i = xy.toNat := by simp [ProA.copyY, ProA.wordOf, hxy]
  rw [he, hcd, hcx, hcy, hmod, ProA.evPc, hpc]
  rfl

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
