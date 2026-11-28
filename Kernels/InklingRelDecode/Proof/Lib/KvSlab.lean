-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.KvBox
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
public import Lemmas.Flow.TensorLoadFacts
import Lemmas.Tensor.TensorMulticast
import Lemmas.Flow.NotObject
import Lemmas.Flow.TcTmpl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- **A tensor issue is the copy of a box of an existing slab** into the CTA `cta` at a
1024-aligned destination: the `kv_rows` map, the K or V half-head column of a KV head, and the
physical row of the slab the block table gives. -/
def KvSlab (Q : Params) (cta : Nat) (sp : TensorCopy.Spec) : Prop :=
  ∃ dst bar r s kvh isV hh, r < Q.b ∧ s < 2 * Q.blocks r ∧ kvh < kvHeads ∧ isV ≤ 1 ∧ hh ≤ 1 ∧
    dst % 1024 = 0 ∧ sp = kvCopySpec Q cta (kvh * Q.headCols + 128 * isV + 64 * hh)
      (Q.page r s * Q.pageRows + kvh * Q.headRows) dst bar

/-- **A unicast tile load of the `kv_rows` map from two registers is the `kvCopySpec` of their
words.** -/
theorem kvCopySpec_of_load {Q : Params} {L : Launch} {g : Nat} {t : TState}
    {dst mb r0 r1 x0 x1 a : Nat} {moff : Int} {map : Opnd} {s : TensorCopy.Spec}
    (h : tensorLoadCopy L g t false false dst 0 map [.reg r0, .reg r1] mb moff .tile = .ok (a, s))
    (desc : (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨1, mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩)
    (h0 : t.regs r0 = some (b32 x0)) (h1 : t.regs r1 = some (b32 x1)) (hx0 : x0 < 2 ^ 31)
    (hx1 : x1 < 2 ^ 31) : ∃ cta d, s = kvCopySpec Q cta x0 x1 d s.mbar := by
  have hv := tensorLoadCopy_origin_all h (vs := [BitVec.ofNat 64 x0, BitVec.ofNat 64 x1]) (by
    simp only [List.mapM_cons, List.mapM_nil, readBits_b32 h0 (by omega),
      readBits_b32 h1 (by omega), bind, Except.bind, pure, Except.pure])
  obtain ⟨hbox, hca, hgrp⟩ := tensorLoadCopy_box h
  obtain ⟨-, -, -, -, -, -, hrows⟩ := tensorLoadCopy_ok h
  obtain ⟨sp0, _⟩ := sharedEffAddr_local hbox
  obtain ⟨⟨n, d, o, base, rows⟩, bar, cl, gr⟩ := s
  obtain ⟨rfl, rfl⟩ := Sigma.mk.inj desc
  have key : ∀ x : Nat, x < 2 ^ 31 → (BitVec.ofNat 32 (BitVec.ofNat 64 x).toNat).toInt = i32 x :=
    fun x hx => by
      unfold i32; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]
  have rn : rows = none := hrows.2 rfl
  obtain ⟨sp, cta', ad⟩ := base
  refine ⟨cta', ad, ?_⟩
  change sp = .shared at sp0
  subst sp0
  change cl = false at hca
  change gr = (if false = true then .two else .one) at hgrp
  subst rn hca hgrp
  have orig : o = ![i32 x0, i32 x1] := by
    funext i
    refine (hv i).trans ?_
    fin_cases i
    exacts [key x0 hx0, key x1 hx1]
  simp [kvCopySpec, orig]

/-- The box origin of a slab of the CTA's request, for the CTA's KV head, is below `2 ^ 31`. -/
theorem kv_coord_lt {Q : Params} {L : Launch} {m : Mem0} {g : Nat} {sl isV hh : Nat}
    (hp : Pre Q L m) (hg : g < L.threads)
    (hsl : sl < 2 * Q.blocks ((L.ctaidOf (g / L.block)).get .z)) (hV : isV ≤ 1) (hH : hh ≤ 1) :
    (L.ctaidOf (g / L.block)).get .y < kvHeads ∧
    (L.ctaidOf (g / L.block)).get .y * Q.headCols + 128 * isV + 64 * hh < 2 ^ 31 ∧
    Q.page ((L.ctaidOf (g / L.block)).get .z) sl * Q.pageRows +
      (L.ctaidOf (g / L.block)).get .y * Q.headRows < 2 ^ 31 := by
  obtain ⟨-, hy, hz⟩ := coordinate_bounds hp hg
  have hin := hp.slabInside _ hz sl hsl _ hy
  have hr2 := hp.rowsRange
  have hc1 := hp.kvCols _ hy
  have hs2 := hp.slotStrideRange
  unfold headDim at hc1
  unfold kvHeads at hy ⊢
  exact ⟨hy, by omega, by omega⟩

/-- **The tile load of the slab `sl` of the CTA's request**: the registers hold the column of
half `hh` of the K (`isV = 0`) or V tile of the CTA's KV head and the physical row of the slab,
and the box lands at the address `D` of the CTA. -/
theorem kvCopy_of_load {Q : Params} {L : Launch} {m : Mem0} {g : Nat} {t : TState}
    {dst mb r0 r1 a x0 x1 : Nat} {moff : Int} {map : Opnd} {s : TensorCopy.Spec}
    {cta D sl isV hh : Nat} (hp : Pre Q L m) (hg : g < L.threads)
    (h : tensorLoadCopy L g t false false dst 0 map [.reg r0, .reg r1] mb moff .tile = .ok (a, s))
    (desc : (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨1, mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩)
    (hsl : sl < 2 * Q.blocks ((L.ctaidOf (g / L.block)).get .z)) (hV : isV ≤ 1) (hH : hh ≤ 1)
    (h0 : t.regs r0 = some (b32 x0)) (h1 : t.regs r1 = some (b32 x1))
    (e0 : x0 = (L.ctaidOf (g / L.block)).get .y * Q.headCols + 128 * isV + 64 * hh)
    (e1 : x1 = Q.page ((L.ctaidOf (g / L.block)).get .z) sl * Q.pageRows +
      (L.ctaidOf (g / L.block)).get .y * Q.headRows)
    (hb : s.sharedBase = ⟨.shared, cta, D⟩) :
    s = kvCopySpec Q cta ((L.ctaidOf (g / L.block)).get .y * Q.headCols + 128 * isV + 64 * hh)
      (Q.page ((L.ctaidOf (g / L.block)).get .z) sl * Q.pageRows +
        (L.ctaidOf (g / L.block)).get .y * Q.headRows) D s.mbar := by
  obtain ⟨-, c0, c1⟩ := kv_coord_lt hp hg hsl hV hH
  subst e0 e1
  obtain ⟨cta', d', hsp⟩ := kvCopySpec_of_load h desc h0 h1 c0 c1
  rw [hsp] at hb
  obtain ⟨rfl, rfl⟩ : cta' = cta ∧ d' = D := by simpa [kvCopySpec] using hb
  exact hsp

/-- **A tile load of a slab is a `KvSlab`** when its destination is 1024-aligned. -/
theorem kvSlab_of_load {Q : Params} {L : Launch} {m : Mem0} {g : Nat} {t : TState}
    {dst mb r0 r1 a x0 x1 : Nat} {moff : Int} {map : Opnd} {s : TensorCopy.Spec}
    {cta D sl isV hh : Nat} (hp : Pre Q L m) (hg : g < L.threads)
    (h : tensorLoadCopy L g t false false dst 0 map [.reg r0, .reg r1] mb moff .tile = .ok (a, s))
    (desc : (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
      ⟨1, mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩)
    (hsl : sl < 2 * Q.blocks ((L.ctaidOf (g / L.block)).get .z)) (hV : isV ≤ 1) (hH : hh ≤ 1)
    (h0 : t.regs r0 = some (b32 x0)) (h1 : t.regs r1 = some (b32 x1))
    (e0 : x0 = (L.ctaidOf (g / L.block)).get .y * Q.headCols + 128 * isV + 64 * hh)
    (e1 : x1 = Q.page ((L.ctaidOf (g / L.block)).get .z) sl * Q.pageRows +
      (L.ctaidOf (g / L.block)).get .y * Q.headRows)
    (hb : s.sharedBase = ⟨.shared, cta, D⟩) (hD : D % 1024 = 0) : KvSlab Q cta s := by
  obtain ⟨hy, -, -⟩ := kv_coord_lt hp hg hsl hV hH
  have hsp := kvCopy_of_load hp hg h desc hsl hV hH h0 h1 e0 e1 hb
  exact ⟨D, s.mbar, _, sl, _, isV, hh, (coordinate_bounds hp hg).2.2, hsl, hy, hV, hH, hD, hsp⟩

end

end PTX.Kernels.InklingRelDecode.Proof.Lib
