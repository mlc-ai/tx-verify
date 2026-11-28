-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvAProof
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.PvAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ProbAddr
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FinLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MmaElem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Value

@[expose] public section

/-! # The value of a PV MMA's A element

A PV MMA `k'` (block `d`) reads at A row `row < 64`, contraction element `kk < 16` the bf16 number
of the P store `(j, q)` of warpgroup 0's lane `64 (u / 4) + row`, `u = 2 (k' / 2) + kk / 8`, in
its block `d` (`pv_a_val`): `j = u % 4`, `q = (kk % 8) / 2`, the word `8 j + kk % 8` of the
lane's probabilities in the block in progress at the store (`w0PWord`). The P tile's layout
(`probDesc`: 16 bytes a row, 1024 bytes a group of eight keys) is the lane's place of the store. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- One half of a bf16 pair's bytes is the number of its element. -/
theorem pair_half_val {x y : ℝ} {o : Nat} (ho : o = 0 ∨ o = 2) :
    ∃ z : ℝ, [(Assumptions.bf16Pair x y).toBytes[o]?, (Assumptions.bf16Pair x y).toBytes[o + 1]?] =
      (Value.float .bf16 z).toBytes.map some ∧ z = if o = 0 then x else y := by
  rcases ho with rfl | rfl
  · exact ⟨x, rfl, rfl⟩
  · exact ⟨y, rfl, rfl⟩

private theorem pvPc_inj {k k' : Nat} (h : TmemRow.pvPc k = TmemRow.pvPc k') : k = k' := by
  simp only [TmemRow.pvPc] at h
  split_ifs at h <;> omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hnu : ¬ HasUb X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
  (hBar : BarRows P L X)
  (hS : ∀ i d s acc mask, X.MmaIssue i d s acc mask → TcMma.IssueShape L i d s mask)
  (hT : TmemRows P L X) (hW : ∀ g, warp L g < 4 → W0Trace P X g)
include hp hX hFw hnu hR hI hB hBar hS hT hW

/-- **The A element of a PV MMA is a probability of the block** (valid rows). -/
theorem pv_a_val {g i pc bb row col kk : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {ops : AsyncCopy.MmaOperands} {x : ℝ}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩) (hbb : bb < 256)
    (hops : X.async.mmaOperands (g, i) = some ops) (hrow : row < 64) (hcol : col < 256)
    (hkk : kk < 16)
    (hel : Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a
      (TcMma.operandRow s.descriptor row col) kk = .ok x) :
    ∃ d k', k' < 8 ∧ pc = TmemRow.pvPc k' ∧ mmaIssues ((X.tr g).take i) = 24 * d + 16 + k' ∧
      ∃ h kst e, warp L h < 4 ∧ h / L.block = g / L.block ∧
        tidOf L h = 64 * ((2 * (k' / 2) + kk / 8) / 4) + row ∧ X.get (h, kst) = some e ∧
        704 ≤ e.pc ∧ e.pc < 708 ∧ (w0Fin ((X.tr h).take kst)).1.length = d ∧
        x = w0PWord P.scale ((X.tr h).take kst) (8 * ((2 * (k' / 2) + kk / 8) % 4) + kk % 8) := by
  have he : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩ := hx
  rcases mma_kind hT hX he with ⟨rfl, -⟩ | ⟨-, k', hk', rfl, hon, hmo⟩
  · omega
  obtain ⟨dB, k2, hk2, hpc, hbk, hiss, -, hD, haT, hA, hpolls, -⟩ :=
    mma_pvAt hp hX hFw he hon.1 hbb
  obtain rfl := pvPc_inj hpc
  have hkd := (desc_bf16 (Or.inr rfl) hmo.2.1).1
  obtain ⟨-, hvalid, -, -, ⟨-, -, -, hs1, hs2, hs3⟩, -, -, -, -, hex⟩ :=
    hS _ _ _ _ _ (show X.MmaIssue (g, i) bb s acc mask from ⟨_, he⟩)
  have hr : TcMma.operandRow s.descriptor row col < 128 := by
    rw [hD]
    exact pv_operandRow_lt row hrow col hcol
  have hidx : 2 * (TcMma.operandRow s.descriptor row col * 16 + kk) <
      TcMma.Operand.a.bytes s.descriptor := by
    have hb : TcMma.Operand.a.bytes s.descriptor = 4096 := by
      rw [hD]
      decide
    omega
  obtain ⟨l, hl⟩ : ∃ l, s.byteLoc .a (2 * (TcMma.operandRow s.descriptor row col * 16 + kk)) =
      some l := by
    rcases hex .a _ hidx with h | ⟨-, c, hc⟩
    · exact h
    · simp [TcMma.aCell, haT] at hc
  obtain ⟨dp, h, k3, j2, pcw, ac, bs, o, hdp, hcnt9, hw, hWe, hpcw, hj2, ho, hbytes, hhb, hao⟩ :=
    pv_a_pair hp hX hFw hR hI hB hBar he (by omega) hon.1 hops hkd
      ⟨by omega, by omega, by omega⟩ hl
  have hdd : dp = dB := by
    have e0 := (hdp 0).symm.trans (hpolls 0)
    have e1 := (hdp 1).symm.trans (hpolls 1)
    simp only [Fin.val_zero, Fin.val_one] at e0 e1
    unfold ringUses at e0 e1
    omega
  subst hdd
  have hladdr := MmaFoot.prob_addr hD hA haT (r := TcMma.operandRow s.descriptor row col)
    (kk := kk) (z := 0) hkk (by omega) hl
  have hv := (hW h hw).take (j := k3)
  obtain ⟨q, hq4, -, hloc, hbs⟩ := w0_pstore_value hp hX hFw hw hWe hj2 hpcw hv ac bs rfl
  have hopr : TcMma.operandRow s.descriptor row col % 64 = row := by
    rw [hD]
    exact (by decide +kernel : ∀ row < 64, ∀ col < 256,
      TcMma.operandRow MmaFoot.pvD row col % 64 = row) row hrow col hcol
  rw [hloc] at hao
  simp only [wsLoc] at hao
  have ht : tidOf L h < 128 := MemRow.wg0_tid hw
  rw [hopr] at hladdr
  have hcnt := w0_cnt_pst hp hX hFw hw hWe (noUb_kind hnu hWe)
    ⟨by simp only; omega, by simp only; omega⟩
  obtain ⟨z, hz, hzv⟩ := pair_half_val
    (x := w0PWord P.scale ((X.tr h).take k3) (2 * (4 * j2 + q)))
    (y := w0PWord P.scale ((X.tr h).take k3) (2 * (4 * j2 + q) + 1)) ho
  rw [← hbs] at hz
  have hzx : x = z := by
    have h1 : Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a
        (TcMma.operandRow s.descriptor row col) kk = .ok z :=
      Result.bf16MmaElement_of_bytes (hbytes.trans hz)
    rw [hel] at h1
    exact Except.ok.inj h1
  have hj : j2 = (2 * (k' / 2) + kk / 8) % 4 := by omega
  have hqq : q = (kk % 8) / 2 := by omega
  have hoo : o = 2 * (kk % 2) := by omega
  have htid : tidOf L h = 64 * ((2 * (k' / 2) + kk / 8) / 4) + row := by omega
  refine ⟨dp, k', hk2, hpc, hiss, h, k3, ⟨pcw, .wr ac bs⟩, hw, hhb, htid, hWe,
    by simp only; omega, by simp only; omega, by omega, ?_⟩
  rw [hzx, hzv]
  split_ifs with hc
  · congr 1
    omega
  · congr 1
    omega

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
