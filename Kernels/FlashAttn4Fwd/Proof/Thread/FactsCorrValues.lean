-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrTc
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrOut
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrSwizzle
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc

@[expose] public section

/-! # The correction warps' staging values (`CorrValues.final`)

A write covering staging slot `(x, y, k)` of half `hh` of stage `st` is a staging store of the
thread (`corr_wr`): element `el` of store `h` of final chunk `j` of stage `st'`, four bytes at the
thread's row's line of half `j / 4`, chunk `2 (j % 4) + h` exchanged by `lane % 8`. Against the
slot's address (`stageLoc_addr`) the stage, the half and the row agree (`y = rowOf`), the chunk is
`x / 8`, and the slot is byte `b = 2 (x % 8) + k - 4 el` of the word `fw d (4 h + el)`. The
run invariant names the chunk's load (`Counts.finLd`: in the item's final credit, value
`2 q + b / 2` is the one of column `64 hh + x`) and the read of the row sum (`Counts.finSt`,
after the item's last statistics sync of the stage), so, when the loaded values are numbers
(`F32s`, from `Safety.LoadFloats`) and the row sum reads as a number `l`, the byte is byte `k` of
the half-precision product of the value and `1 / l'` (`fw_byte`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem take_get {g n r : Nat} (hr : r < n) : ((X.tr g).take n)[r]? = X.get (g, r) := by
  simp [Execution.get, hr]

theorem take_take_le {g n r : Nat} (hr : r ≤ n) :
    ((X.tr g).take n).take r = (X.tr g).take r := by
  rw [List.take_take, Nat.min_eq_left hr]

theorem xor_cancel_r {a b m : Nat} (h : a ^^^ m = b ^^^ m) : a = b := by
  have := congrArg (· ^^^ m) h
  simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this

/-- A value of sixteen single-precision floats, by position. -/
theorem f32s_getD {o : List Value} (h : F32s o) {i : Nat} (hi : i < o.length) :
    ∃ x, o.getD i (b32 0) = .float .f32 x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact h _ (List.getElem_mem hi)

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **`CorrValues.final`**: a write of a staging slot by a correction thread is at the thread's
row, after the item's final load of the slot's column and the load of the row sum, and, when the
loaded values are numbers, writes byte `k` of the half-precision product of the loaded value and
`1 / l'`. -/
theorem CorrValues_final {g n st hh x y k : Nat} {dst : Acc} {bs : List Byte}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hW : X.Writes (g, n) dst bs)
    (hst : st < 2) (hhh : hh < 2) (hx : x < 64) (hy : y < 128) (hk : k < 2)
    (hcov : dst.Covers (stageLoc L (ctaOf L g) st hh x y k)) :
    y = rowOf L g ∧ ∃ i a p r, ∃ vals : List Value, ∃ bl : List (Option Byte), i < n ∧
      X.TLd (g, i) a vals .s32x32b ∧
      pArr L X g st i =
        kvBlocks P * (arrivals (stagedBar L (ctaOf L g) st) ((X.tr g).take n) + 1) ∧
      p < vals.length ∧ (tcDataCell32 L g a p).column = 256 + 128 * st + (64 * hh + x) ∧
      StatRead L X g st ((kvBlocks P + 1) * arrivals (stagedBar L (ctaOf L g) st)
        ((X.tr g).take n) + kvBlocks P) r bl ∧
      (F32s vals → ∀ o l : ℝ, vals[p]? = some (.float .f32 o) → F32Read bl l →
        wbyte dst bs (stageLoc L (ctaOf L g) st hh x y k) =
          some ((Value.float .f16 (o * (1 / if l = 0 then 1 else l))).byteAt k)) := by
  obtain ⟨pcw, he⟩ := hW
  obtain ⟨d, st', j, h, el, -, hc, -, hs, hloc, hsz, hbs⟩ := corr_wr hpre hX ht hw hw' he
  -- the addresses
  have hsb := hpre.sharedAlignment
  have hS := stageLoc_addr hsb (ctaOf L g) st hh x y k hx hk
  obtain ⟨-, -, hc1, hc2⟩ := hcov
  rw [hloc] at hc1 hc2
  rw [hsz] at hc2
  rw [hS] at hc1 hc2
  have hkk : Correction.kOf L g < 4 := Nat.mod_lt _ (by decide)
  have hln : Correction.lnOf L g < 32 := Nat.mod_lt _ (by decide)
  have hrow : rowOf L g = 32 * Correction.kOf L g + Correction.lnOf L g := by
    simp only [rowOf, Correction.kOf, Correction.lnOf, Correction.tidOf]; omega
  have hu : x / 8 ^^^ y % 8 < 8 := Nat.xor_lt_two_pow (n := 3) (by omega) (by omega)
  have hv : Correction.lnOf L g % 8 ^^^ (2 * (j.val % 4) + h.val) < 8 :=
    Nat.xor_lt_two_pow (n := 3) (by omega) (by omega)
  simp only at hc1 hc2
  unfold Correction.stage at hc1 hc2
  simp only [Correction.sb] at hc1 hc2
  have hj := j.isLt
  have hel := el.isLt
  have hh2 := h.isLt
  have hst' := st'.isLt
  have e1 : st = st'.val := by omega
  have e2 : hh = j.val / 4 := by omega
  have e3 : y = rowOf L g := by omega
  have e4 : x / 8 ^^^ y % 8 = Correction.lnOf L g % 8 ^^^ (2 * (j.val % 4) + h.val) := by omega
  have e5 : y % 8 = Correction.lnOf L g % 8 := by omega
  rw [e5, Nat.xor_comm (Correction.lnOf L g % 8)] at e4
  have e6 := xor_cancel_r e4
  -- the byte of the word
  set b := (2 * x + k) % 16 - 4 * el.val with hbdef
  have hb4 : b < 4 := by omega
  have hwb : (stageLoc L (ctaOf L g) st hh x y k).addr - dst.loc.addr = b := by
    rw [hS, hloc]; simp only; unfold Correction.stage
    simp only [Correction.sb]; omega
  subst e1 e2
  refine ⟨e3, ?_⟩
  -- the load of the chunk
  have hfc : Correction.finChunk d st' j := by unfold Correction.finChunk; exact .inr ⟨h, el, hs⟩
  obtain ⟨r, hr, pcl, hgl, hcl⟩ := hc.finLd st' j hfc
  rw [List.length_take] at hr
  have hrn : r < n := by omega
  rw [take_get hrn] at hgl
  rw [take_take_le hrn.le] at hcl
  obtain ⟨_, _, _, -, -, -, -, -, hlen⟩ := corr_tld hpre hX ht hw hw' hgl
  -- the read of the row sum
  have hfs : Correction.finStat d st' := by
    unfold Correction.finStat Correction.finRecip; exact .inr (.inr (.inr (.inr (.inr ⟨j, hfc⟩))))
  obtain ⟨r', hr', pcr, ac, bl, hgr, hlr, hvr, hcr⟩ := hc.finSt st' hfs
  rw [List.length_take] at hr'
  have hrn' : r' < n := by omega
  rw [take_get hrn'] at hgr
  rw [take_take_le hrn'.le] at hcr
  obtain ⟨-, str, -, -, -, -, hcl'⟩ := corr_rd hpre hX ht hw hw' hgr
  have hstr : str = st' := by
    obtain ⟨-, hl2, -⟩ := hcl'
    rw [hlr] at hl2
    simp only [Correction.ownLoc, statsWord, Correction.sb, Loc.mk.injEq, Correction.rowOf,
      Correction.tidOf, rowOf] at hl2
    exact Fin.ext (by omega)
  subst hstr
  have hstaged : arrivals (stagedBar L (ctaOf L g) str.val) ((X.tr g).take n) = d.i := by
    have := hc.staged str.val str.isLt
    rw [show stagedBar L (ctaOf L g) str.val = Correction.ownLoc L g (256 + 8 * str.val) by
      simp only [stagedBar, Correction.ownLoc, Correction.sb], this]
    obtain ⟨site, i', t', aw, aa, o⟩ := d
    simp only at hs ⊢
    subst hs
    fin_cases str <;> simp [Correction.stagedPos]
  have hkv := corr_trips_eq hpre
  rw [hstaged]
  set p := 2 * (4 * h.val + el.val) + b / 2 with hpdef
  refine ⟨r, _, p, r', d.o, bl, hrn, ⟨pcl, hgl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pArr, pReadyBar_lead, hcl, ← hkv]; ring
  · rw [hlen]; omega
  · rw [tmem_column L g g _ p (by omega)]; omega
  · refine ⟨pcr, ac, hgr, hcl', ?_⟩
    have hkw := corr_kOf hw hw'
    rw [corr_barOrd hpre hX ht hw hw' r' (by omega),
      show warpOf L g - 5 + 4 * str.val = Correction.kOf L g + 3 + 4 * str.val by omega, hcr, ← hkv]
  · intro hf o l ho hbl
    obtain ⟨v, hv1, hv2⟩ := hbl
    rw [hv1] at hvr
    injection hvr with hvr
    have hl : valFloat .f32 d.aw = .ok l := by rw [← hvr]; exact hv2.2
    have hq8 : 2 * (4 * h.val + el.val) + 1 < d.o.length := by rw [hlen]; omega
    obtain ⟨xv, hxv⟩ := f32s_getD hf (show 2 * (4 * h.val + el.val) < d.o.length by omega)
    obtain ⟨yv, hyv⟩ := f32s_getD hf hq8
    have ho' : d.o.getD (2 * (4 * h.val + el.val) + b / 2) (b32 0) = .float .f32 o := by
      rw [List.getD_eq_getElem?_getD, ← hpdef, ho]; rfl
    rw [wbyte, hwb, hbs, fw_byte d _ b hb4 hxv hyv hl ho']
    congr 2
    omega

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
