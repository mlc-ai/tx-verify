-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.NoUbOut
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Geometry.Maps
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr
import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
import Lemmas.Flow.TensorIssueCopy
import Lemmas.Flow.UbStop

@[expose] public section

/-! # Warpgroup 0's output store fires no undefined behaviour

The tile store of an output chunk: the map operand is the output map's descriptor slot of
`param_1` (`Pre.mapOBind`, valid), the source is a 128-byte aligned shared word of the lane's
CTA, the four coordinates are below `2 ^ 31` and the first is a multiple of 8 (a 16-byte origin
of two-byte elements). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

theorem readBits32_of {t : TState} {r wd : Nat} {x : BitVec 64}
    (h : t.regs r = some (.bits wd x)) : readBits L g t 32 (.reg r) = .ok (truncBits 32 x) := by
  simp [readBits, readReg, h, bind, Except.bind, pure, Except.pure]

/-- A word that is a multiple of 8 is a multiple of 16 bytes as a two-byte element origin. -/
theorem origin_align {w : Nat} (h : w % 8 = 0) (h1 : w < 2 ^ 31) :
    (BitVec.ofNat 32 w).toInt * 2 % 16 = 0 := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat]
  split_ifs <;> omega

/-- **The output store's operand checks pass.** -/
theorem otma_nonub (hp : Pre P L m) {A : List Assumption} {t : TState} {rx ry src : Nat}
    {sx X Y cx cy : BitVec 64} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t
      (.cpTensorStore (.reg 3832) [.reg rx, .reg ry, .reg 459, .reg 460] src 0 none .tile none))
      e o)
    (hs : t.regs src = some (.bits 32 sx)) (hal : (smLoc L g sx 0).addr % 128 = 0)
    (hm : t.regs 3832 = some (.bits 64 (BitVec.ofNat 64 (P.param1Base + 512))))
    (hx : t.regs rx = some (.bits 32 X)) (hx1 : X.toNat < 2 ^ 31) (hx8 : X.toNat % 8 = 0)
    (hy : t.regs ry = some (.bits 32 Y)) (hy1 : Y.toNat < 2 ^ 31)
    (hcx : t.regs 459 = some (.bits 32 cx)) (hcx1 : cx.toNat < 2 ^ 31)
    (hcy : t.regs 460 = some (.bits 32 cy)) (hcy1 : cy.toNat < 2 ^ 31) :
    ∀ f, e.kind ≠ .ub f := by
  intro f he
  have h := fires_ub hf he
  have h64 : (BitVec.ofNat 64 (P.param1Base + 512)).toNat = P.param1Base + 512 := by
    have := hp.param1Range
    simp only [BitVec.toNat_ofNat]
    omega
  have hal64 := hp.param1Align
  have hmap : tensorMap L g t (.reg 3832) [.reg rx, .reg ry, .reg 459, .reg 460] .tile =
      .ok (P.param1Base + 512,
        ⟨3, mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass⟩) := by
    unfold tensorMap
    have h1 : (P.param1Base + 512) % 64 = 0 := by omega
    have hcrd : TensorMode.tile.coordinates 3 = 4 := rfl
    simp only [bind, Except.bind, pure, Except.pure, tensorMapAddress_bits hm, h64, h1,
      ↓reduceIte, hp.mapOBind, List.length_cons, List.length_nil, hcrd,
      Geometry.mapO_valid_of_pre hp, true_or]
  have hsl : sharedEffAddr L g t false src 0 =
      .ok ⟨.shared, g / L.block, (truncBits 32 sx).toNat⟩ := by
    simp [sharedEffAddr, readReg, hs, readBits, bind, Except.bind, pure, Except.pure, truncBits]
  have hvs : [Opnd.reg rx, .reg ry, .reg 459, .reg 460].mapM (readBits L g t 32) =
      .ok [truncBits 32 X, truncBits 32 Y, truncBits 32 cx, truncBits 32 cy] := by
    simp only [List.mapM_cons, List.mapM_nil, readBits32_of hx, readBits32_of hy,
      readBits32_of hcx, readBits32_of hcy, bind, Except.bind, pure, Except.pure]
  have hal' : (truncBits 32 sx).toNat % 128 = 0 := by
    simpa [smLoc, truncBits] using hal
  have t32 : ∀ z : BitVec 64, z.toNat < 2 ^ 31 → (truncBits 32 z).toNat = z.toNat := by
    intro z hz
    simp only [truncBits, BitVec.toNat_ofNat]
    omega
  have hnn : ∀ axis : Fin 4, 0 ≤ (BitVec.ofNat 32 ([truncBits 32 X, truncBits 32 Y,
      truncBits 32 cx, truncBits 32 cy].getD axis.val 0).toNat).toInt := by
    intro axis
    apply toInt_nonneg
    fin_cases axis <;> simp [t32 _ hx1, t32 _ hy1, t32 _ hcx1, t32 _ hcy1] <;> omega
  have hbox : TensorDescriptor.BoxAligned
      (mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass)
      (fun axis : Fin 4 => (BitVec.ofNat 32 ([truncBits 32 X, truncBits 32 Y, truncBits 32 cx,
        truncBits 32 cy].getD axis.val 0).toNat).toInt) := by
    simp only [TensorDescriptor.BoxAligned]
    simp [mapO, encodeTiled, TensorDescriptor.Format.bytes, truncBits]
    have e : X.toNat % 4294967296 % 18446744073709551616 = X.toNat := by omega
    rw [e]
    exact origin_align hx8 hx1
  have hbox' := (requireBoxAligned_eq_ok _ _).2 hbox
  simp only [eventTmpl, tensorStoreTmpl, tensorStoreSpec, cachePolicyRead, hmap, hsl, hvs, bind,
    Except.bind, pure, Except.pure, Option.all, hal', ↓reduceIte, hnn, implies_true, true_or,
    hbox', TensorMode.transfer, TensorMode.rowCoordinates] at h
  simp [ofExec] at h

/-- The coordinates of the output chunks for a warp word below 4. -/
theorem otma_cols {w : BitVec 64} (hw : w.toNat < 4) :
    (shl w 7).toNat < 2 ^ 31 ∧ (shl w 7).toNat % 8 = 0 ∧
    (addi (shl (shl w 1) 6) 64).toNat < 2 ^ 31 ∧ (addi (shl (shl w 1) 6) 64).toNat % 8 = 0 ∧
    (addi (shl (shl w 1) 6) 256).toNat < 2 ^ 31 ∧ (addi (shl (shl w 1) 6) 256).toNat % 8 = 0 ∧
    (addi (shl (shl w 1) 6) 320).toNat < 2 ^ 31 ∧ (addi (shl (shl w 1) 6) 320).toNat % 8 = 0 := by
  obtain h | h | h | h : w.toNat = 0 ∨ w.toNat = 1 ∨ w.toNat = 2 ∨ w.toNat = 3 := by omega
  · obtain rfl : w = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
    decide
  · obtain rfl : w = 1 := BitVec.eq_of_toNat_eq (by simpa using h)
    decide
  · obtain rfl : w = 2 := BitVec.eq_of_toNat_eq (by simpa using h)
    decide
  · obtain rfl : w = 3 := BitVec.eq_of_toNat_eq (by simpa using h)
    decide

theorem noUbAt_otma (hp : Pre P L m) (d : D) (hs : ∃ c, d.site = .otma c)
    (hw : w = warpW L g) (ht : tidOf L g < 128) : W0NoUbAt P L g w d := by
  obtain ⟨c, hs⟩ := hs
  have hal : ∀ c : Fin 4, (smLoc L g (otmaW L (warpW L g) c) 0).addr % 128 = 0 := fun c =>
    wsLoc_al hp (otma_loc (g := g) hp ht c) (n := 128) (by decide)
      (by fin_cases c <;> simp [MemRow.wg0OutOff] <;> omega)
  have hwl : (warpW L g).toNat < 4 := by
    simp only [warpW, warpOf, BitVec.toNat_ofNat]
    omega
  have hcx : ∀ x : BitVec 64, x = BitVec.ofNat 64 (ctaidX L g) → x.toNat < 2 ^ 31 := by
    rintro x rfl
    have := ctaid_lt hp g
    have := hp.sqLt
    simp only [BitVec.toNat_ofNat]
    omega
  have hcy : ∀ x : BitVec 64, x = BitVec.ofNat 64 (ctaidY L g) → x.toNat < 2 ^ 31 := by
    rintro x rfl
    have := ctaid_lt hp g
    have := hp.bLt
    simp only [BitVec.toNat_ofNat]
    omega
  obtain ⟨a1, a2, b1, b2, c1, c2, d1, d2⟩ := otma_cols hwl
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  subst hw
  cases hs
  fin_cases c <;> w0_shape
  · exact fun f hk => otma_nonub hp hf (rg 1913) (hal 0) (rg 3832) (rg 1914) a1 a2
      (rg 1915) (by decide) (rg 459) (hcx _ rfl) (rg 460) (hcy _ rfl) f hk
  · exact fun f hk => otma_nonub hp hf (rg 2082) (hal 1) (rg 3832) (rg 2083) b1 b2
      (rg 2084) (by decide) (rg 459) (hcx _ rfl) (rg 460) (hcy _ rfl) f hk
  · exact fun f hk => otma_nonub hp hf (rg 2251) (hal 2) (rg 3832) (rg 2252) c1 c2
      (rg 2253) (by decide) (rg 459) (hcx _ rfl) (rg 460) (hcy _ rfl) f hk
  · exact fun f hk => otma_nonub hp hf (rg 2421) (hal 3) (rg 3832) (rg 2422) d1 d2
      (rg 2423) (by decide) (rg 459) (hcx _ rfl) (rg 460) (hcy _ rfl) f hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
