-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MaskWord
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Reads
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockLoad
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.OfPc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FinLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.BlockList
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SegEvent

@[expose] public section

/-! # The masks a lane of warpgroup 0 read (valid rows)

`mask_read`: the mask word of every finished block `t` of a lane at its epilogue is its last
validity read at pc 289 (`W0Ok.mask`: a 32-bit word, so the block has one), and that read is made
with `t` blocks closed (the block is the `t`-th closed, `w0Fin_block_of_close`), so its word's bit
`i` is the validity of the slot `32 half + i` of the block `t` (`valid_read_word`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem w0OrigBlocks_numOrig (P : Params) (e : Nat) :
    w0OrigBlocks P e = FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen e) := by
  unfold w0OrigBlocks FlashMlaSparseDecodeH64.numOrigBlocks FlashMlaSparseDecodeH64.origPadded
    FlashMlaSparseDecodeH64.ceilToMultiple FlashMlaSparseDecodeH64.topkBlock
  omega

/-- **The masks a lane read** (valid rows). -/
theorem mask_read (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hN : CoordInputs L X) (hnu : ¬ HasUb X) (hV : W0Rows P L X) : MaskRead P L X hV := by
  intro g k e hg he hpc t seg hseg i hi
  have hw : warp L g < 4 := wg0_warp_of_pc hp hX hFw hnu he (by omega)
  have hv : W0Trace P X g := hV g hg (by simp only [warp] at hw; omega)
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hno := w0_noEarly hp hX hFw hnu hw k
  have hW := (hv.1 k hk.le).1 seg (List.mem_of_getElem? hseg)
  obtain ⟨n, hn, hmw⟩ := hW.mask
  -- the last validity read of the block
  obtain ⟨v, hlast⟩ : ∃ v, w0Last w0RdVal [289] seg = some v := by
    cases hl : w0Last w0RdVal [289] seg with
    | some v => exact ⟨v, rfl⟩
    | none => simp [w0Words, hl] at hmw
  have hmwv : (w0Words seg).mw = v := by simp [w0Words, hlast]
  obtain ⟨f, hfseg, hf289, hfv⟩ : ∃ f ∈ seg, f.pc = 289 ∧ w0RdVal f = some v := by
    unfold w0Last at hlast
    have hmem := List.mem_of_getLast? hlast
    obtain ⟨f, hf, hfe⟩ := List.mem_filterMap.mp hmem
    refine ⟨f, hf, ?_, ?_⟩
    · by_contra hne
      simp [hne] at hfe
    · simpa [show f.pc = 289 by by_contra hne; simp [hne] at hfe] using hfe
  -- the block's closing event and the read's index
  obtain ⟨K0, c0, hc0, hpc0, hK0lt, hlen0, rfl, hev⟩ := w0_seg_events hp hX hFw hw hseg hnu
  obtain ⟨j, hjK, hgetj, hclj⟩ := hev f hfseg
  obtain ⟨pcf, kdf⟩ := f
  simp only at hf289
  subst hf289
  obtain ⟨a, bs, rfl⟩ : ∃ a bs, kdf = .rd a bs := by
    cases kdf <;> simp [w0RdVal] at hfv ⊢
  have hatf : MbarRow.Wg0At L g 289 := ⟨hw, by omega, by omega⟩
  obtain ⟨x, hx, -, hbits⟩ := valid_read_word hp hX hFw hR hI hB hN
    (noUbBefore_of_noUb hnu) hgetj hatf
  have hvx : v = .bits 32 x := by
    simp only [w0RdVal, Option.some.injEq] at hfv
    rw [← hfv]
    exact hx
  rw [hmwv, hvx]
  rw [hclj] at hbits
  have hb := hbits i hi
  simp only [w0Bit]
  rw [hb]
  have hbat : w0Batch L g = ctaidY L g := rfl
  have hq : w0Query L g = ctaidX L g := rfl
  have hh : 32 * w0Half L g = 8 * (4 * ((L.tidOf g).x / 32 / 2)) := by
    simp only [w0Half]
    omega
  simp only [maskBit, w0BlockExtra, w0BlockSlot, hbat, hq, w0OrigBlocks_numOrig, hh]
  by_cases hlt : t < FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g))
  · simp only [hlt, ↓reduceIte, not_le.mpr hlt, decide_false, Bool.false_eq_true]
    have : 64 * t + 8 * (4 * ((L.tidOf g).x / 32 / 2) + i / 8) + i % 8 =
        t * 64 + (8 * (4 * ((L.tidOf g).x / 32 / 2)) + i) := by omega
    rw [this]
  · simp only [hlt, ↓reduceIte, decide_eq_true (not_lt.mp hlt)]
    have : 64 * (t - FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g))) +
        8 * (4 * ((L.tidOf g).x / 32 / 2) + i / 8) + i % 8 =
        (t - FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen (ctaidY L g))) * 64 +
          (8 * (4 * ((L.tidOf g).x / 32 / 2)) + i) := by omega
    rw [this]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
