-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.DqSlotValue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.DqBElem
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.PvAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.PvBTile
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Result.Gemm
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Reads

@[expose] public section

/-! # The B elements of a PV MMA are the slots' dequantized values

B element `(col, kk)` of PV MMA `k'` of block `d` (`col < 256`, `kk < 16`) is the bf16 number
`e4m3Val x * ue8m0Val b` of the chunk store of the use (`dq_b_elem`); its byte is the chunk
`(8 kk + F % 64 / 8, k' / 2, F / 64)` of the dequantizer lane, byte `2 (F % 8)`, `F = 256 (k' % 2)
+ col` the feature (`pv_b_addr`, `dqChunk_inj`): the token is the slot `16 (k' / 2) + kk` of block
`d`, and `dq_store_slot` gives its value at feature `F` when the slot is valid (`pv_b_slot`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow PTX.AsyncCopy MmaFoot

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
  (hRaw : RawInputs L X) (hNc : CoordInputs L X)
  (hv : ∀ h k, NoUbBefore X h k → DqValid X h k)
include hp hX hFw hR hI hB hN hRaw hNc hv

/-- **A PV MMA's B element is the slot's dequantized value** (valid data): for the block `d` and
step `k'` of the MMA, B element `(col, kk)` is a number, which is `slotValue` of the slot
`16 (k' / 2) + kk` of block `d`, feature `256 (k' % 2) + col`, when that slot is valid. -/
theorem pv_b_slot {g i pc bb : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : MmaOperands} (he : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩)
    (hat : MbarRow.MmaAt L g pc) (hbb : bb < 256)
    (hops : X.async.mmaOperands (g, i) = some ops) {col kk : Nat} (hc : col < 256)
    (hkk : kk < 16) :
    ∃ d k', k' < 8 ∧ pc = TmemRow.pvPc k' ∧ mmaIssues ((X.tr g).take i) = 24 * d + 16 + k' ∧
      ∃ y : ℝ, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col kk = .ok y ∧
        (slotValid P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) d)
            (w0BlockSlot P (ctaidY L g) d (16 * (k' / 2) + kk)) →
          y = slotValue P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) d)
            (w0BlockSlot P (ctaidY L g) d (16 * (k' / 2) + kk)) (256 * (k' % 2) + col)) := by
  obtain ⟨d, k, hk8, hpc, -, hiss, -, hD, haT, -, -, hsb, hlow, hall⟩ :=
    mma_pvAt hp hX hFw he hat hbb
  have hS1024 : L.sharedBase % 1024 = 0 := hp.sharedBase ▸ hp.sharedAlignment
  have hb2 : d % 2 < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨hmu, -⟩ := hall ⟨d % 2, hb2⟩ rfl
  have hu' : ringUses 2 (d % 2) d = d / 2 := PTX.Flow.ringUses_here rfl hb2
  have hl : s.byteLoc .b (2 * (col * 16 + kk)) = some ⟨.shared, s.lowCta,
      TensorSwizzle.offset .b128 0 (QueryTile.linear (L.sharedBase + 65536 * (d % 2))
        (16 * (k / 2) + kk) (256 * (k % 2) + col) 0)⟩ := by
    have := QueryTile.pv_b_loc hD hsb hc hkk (z := 0) (by omega)
    rwa [show 32 * col + 2 * kk + 0 = 2 * (col * 16 + kk) by omega] at this
  have hadr := QueryTile.pv_b_addr (Bt := L.sharedBase + 65536 * (d % 2)) (k := k) (col := col)
    (kk := kk) (z := 0) (by omega) hkk (by omega)
  have hi0 : 8 * kk + (256 * (k % 2) + col) % 64 / 8 < 128 := by omega
  have hlt0 := MemRow.dqChunk_lt (i := 8 * kk + (256 * (k % 2) + col) % 64 / 8)
    (r := k / 2) (s := (256 * (k % 2) + col) / 64) hi0 (by omega) (by omega)
  have hal0 := MemRow.dqChunk_al (i := 8 * kk + (256 * (k % 2) + col) % 64 / 8)
    (r := k / 2) (s := (256 * (k % 2) + col) / 64) hi0
  have hlg : MemRow.LocIn L (g / L.block) (.dequant ⟨d % 2, hb2⟩) ⟨.shared, s.lowCta,
      TensorSwizzle.offset .b128 0 (QueryTile.linear (L.sharedBase + 65536 * (d % 2))
        (16 * (k / 2) + kk) (256 * (k % 2) + col) 0)⟩ := by
    refine ⟨rfl, hlow, ?_, ?_⟩ <;> simp only [Region.lo, Region.size] <;> rw [hadr] <;> omega
  obtain ⟨x, hx, h, k2, pcw, ac, bs, bw, r, s', j, hW, hpcw, hcta, hws, harr, hcov, hj8, hladdr,
      hxval⟩ := dq_b_elem hp hX hFw hR hI hB hN hv he hat hops (n := col * 16 + kk)
    (by rw [hD]; rfl) (by rw [hsb]; simp only [valueDesc]; exact ⟨by omega, trivial, trivial⟩) hl
    hlg hmu
  have hA : ac.loc.addr =
      L.sharedBase + ((Region.dequant bw).lo + MemRow.dqChunk (h % 128) r s') := by
    rw [hws.1]; rfl
  have hL2 : TensorSwizzle.offset .b128 0 (QueryTile.linear (L.sharedBase + 65536 * (d % 2))
      (16 * (k / 2) + kk) (256 * (k % 2) + col) 0) = ac.loc.addr + 2 * j := hladdr
  rw [hadr, hA] at hL2
  have hltr := MemRow.dqChunk_lt (i := h % 128) (r := r) (s := s') (Nat.mod_lt _ (by decide))
    r.isLt s'.isLt
  have hal1 := MemRow.dqChunk_al (i := h % 128) (r := r) (s := s') (Nat.mod_lt _ (by decide))
  simp only [Region.lo] at hL2
  have hbwl := bw.isLt
  obtain ⟨hbv, hch, hjj⟩ : bw.val = d % 2 ∧
      MemRow.dqChunk (h % 128) r s' = MemRow.dqChunk
        (8 * kk + (256 * (k % 2) + col) % 64 / 8) (k / 2) ((256 * (k % 2) + col) / 64) ∧
      j = (256 * (k % 2) + col) % 8 := by omega
  obtain ⟨hi', hr', hs'⟩ := MemRow.dqChunk_inj (Nat.mod_lt _ (by decide)) hi0 r.isLt
    (by omega) hch
  have hbw : bw = ⟨d % 2, hb2⟩ := Fin.ext hbv
  subst hbw
  have hW' : X.get (h, k2) = some ⟨dqStorePc r s', .wr ac bs⟩ := hpcw ▸ hW
  have harr' : arrivals (mbarLoc L (h / L.block) (.dequantReady ⟨d % 2, hb2⟩))
      ((X.tr h).take k2) = d / 2 := by
    rw [hcta, harr]; exact hu'
  have hslot := dq_store_slot hp hX hFw hR hI hB hRaw (noUbInner hX) hNc r.isLt
    s'.isLt hW' (hv h k2 (noUbBefore_of_get hX hW')) hws harr' (j := j) hj8
  refine ⟨d, k, hk8, hpc, hiss, x, Result.bf16MmaElement_of_bytes hx, fun hvalid => ?_⟩
  have e1 : 2 * (d / 2) + d % 2 = d := by omega
  have e2 : h % 128 / 8 + 16 * r.val = 16 * (k / 2) + kk := by omega
  have e3 : ctaidY L h = ctaidY L g := by simp only [ctaidY, ctaOf, hcta]
  have e4 : ctaidX L h = ctaidX L g := by simp only [ctaidX, ctaOf, hcta]
  have e5 : 64 * s'.val + 8 * (h % 8) + j = 256 * (k % 2) + col := by omega
  simp only [e1, e2, e3, e4, e5] at hslot
  exact hxval.trans (hslot hvalid)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
