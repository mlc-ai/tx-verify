-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Reads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SinkOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SinkValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumRd
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads

@[expose] public section

/-! # The sink word of a lane reads as the reference's

At a late event of a lane of warpgroup 0 (pc 157 or later) the sink word of the events before it
reads as `w0SinkE`: `-inf` for a null pointer, else the head's `f32` word times the multiplier
`0x3FB8AA3B`, exactly (`wg0_sink_rd`; the trace order is `w0_sink_order`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Assumption MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The scaled sink word of the bits of a finite `f32` `q` reads as `q * sinkLog2Factor`. -/
theorem w0SkOf_rd_val {bits : Nat} {q : ℚ} (hb : bits < 2 ^ 32) (hq : f32Value bits = some q)
    {bs : List (Option Byte)} (hr : rebuild 3 bs = .ok (b32 bits)) :
    Rd (okVal (.bits 32 0) (fF (mulL true) [.reg 932, .f32imm 1069066811]
      [(rebuild 3 bs).toOption.getD (.pred false)])) (((q : ℝ) * sinkLog2Factor : ℝ) : EReal) := by
  have hf : fF (mulL true) [.reg 932, .f32imm 1069066811] [b32 bits] =
      mulE true (b32 bits) (.bits 32 (BitVec.ofNat 64 1069066811)) := by
    simp [fF, regsOf, regOf, fOpnd, lk, mulL]
  have hc : f32Value 1069066811 = some (12102203 / 8388608 : ℚ) := by decide +kernel
  have hx := rd_read (sink_raw_rd hb hq)
  have hy := readEReal_bits32 1069066811 _ rfl (by norm_num) hc
  have hm := mulE_reads (fz := true) hx hy (mulEReal_coe _ _)
  have hv : (((q : ℝ) * ((12102203 / 8388608 : ℚ) : ℝ) : ℝ)) = (q : ℝ) * sinkLog2Factor := by
    simp only [sinkLog2Factor]
    push_cast
    ring
  rw [hr]
  simp only [Except.toOption, Option.getD_some]
  rw [hf, hm, erealValue_coe, hv]
  exact ⟨clean_float _, readEReal_float _, Or.inl ⟨_, rfl⟩⟩

/-- **The sink word at a late event reads as the reference's** (valid trace): at an event of a
lane of warpgroup 0 at pc 157 or later, the sink word of the events before it reads as
`w0SinkE` of the lane's head. -/
theorem wg0_sink_rd (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L g < 4) (hv0 : W0Trace P X g)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hge : 157 ≤ e.pc) :
    Rd (w0SkWord ((X.tr g).take k)) (w0SinkE P (w0Head L g)) := by
  have hh : w0Head L g = tidOf L g % 64 := by
    simp only [w0Head, tidOf_x_eq hp, tidOf_eq hp]
  have hlt : w0Head L g < 64 := by rw [hh]; exact Nat.mod_lt _ (by norm_num)
  have hm := hp.paramSink
  rcases w0_sink_order hp hX hFw hnu hw hv0 he hge with ⟨hn, hsk⟩ | ⟨j, f, x, a, bs, hj, hf,
    h156, hk, hx, hsk⟩
  · rw [hn] at hm
    have hs : P.sink (w0Head L g) = none := hm.2 _ hlt
    simp only [w0SinkE, hs]
    rw [hsk]
    exact Wg0.Data.rd_negInf
  · obtain ⟨x', a', bs', hx', hk', hr⟩ := wg0_sink_reads hp hX hFw hnu hf
      ⟨hw, by omega, by omega⟩ h156
    rw [hx] at hm
    obtain ⟨-, -, hmem⟩ := hm
    obtain ⟨s, bits, hs, hb, hbytes, hq⟩ := hmem (w0Head L g) hlt
    obtain ⟨q, hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
    obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hk')
    have hrb : rebuild 3 bs = .ok (b32 bits) := rebuild_word hX hf hr fun i hi => by
      simpa [hh, Nat.add_assoc] using hbytes i hi
    have hv := w0SkOf_rd_val hb hq' hrb
    simp only [w0SkOf, h156, hk, ↓reduceIte] at hsk
    simp only [show ¬ ((156 : Nat) = 103) by norm_num, ↓reduceIte] at hsk
    simp only [w0SinkE, hs]
    rw [← Option.some.inj hsk]
    exact hv

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
