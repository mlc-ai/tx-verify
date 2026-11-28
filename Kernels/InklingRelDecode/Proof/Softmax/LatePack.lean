-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.GenRulesC
public import Lemmas.Flow.TypedPackF

@[expose] public section

/-! # `cvt.rn.bf16x2.f32` on operands that read as extended reals

`bf16Exact` packs the numbers of its two operands as the two bf16 halves, whatever their values,
and declines a NaN operand (`Iface.LateValues.pack` says that none is NaN at the packs of the data
lanes). The result is a datum of four bytes (`dat32_pairBf16`), so the strict piece at a pack only
needs the tags of the operands to be known to read as numbers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption

noncomputable section
variable {L : Launch} {g : Nat}

/-- **The step of the pack `cvt.rn.bf16x2.f32 d, a, b`** outside the software `exp2` blocks, on
operands that read as extended reals, writes a datum of four bytes. -/
theorem pack_step {t : TState} {c : CvtInstr} {a b : Opnd}
    (hd : c.dst = .packed (.float .bf16) 2) (hs : c.src = .float .f32) (hr : c.rnd = some .rn)
    (hp : c.plain = true) (hsr : c.srcs = [a, b])
    (hemu : Assumptions.emuSites.contains t.pc = false)
    (hx : ∃ x : EReal, readERealOpnd t .f32 a = some (.ok x))
    (hy : ∃ y : EReal, readERealOpnd t .f32 b = some (.ok y)) :
    ∃ v, execLocalA Assumptions.all L g t (.cvt c) = .ok (PTX.next (setReg t c.d v)) ∧
      Dat32 v := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  refine ⟨.pair (erealValue .bf16 y) (erealValue .bf16 x), ?_, dat32_pairBf16 x y⟩
  have hseg : SegFreePc Assumptions.all t.pc := Kernels.InklingRelDecode.Proof.segFree hemu
  have h1 : Assumptions.idealArith.localRule L g t (.cvt c) = none :=
    idealReal_localRule_none fun f h => by
      simp [FloatForm.ofOp, CvtInstr.widenF16?, CvtInstr.packF16?, hd, hs, hr, hsr] at h
  have h2 : Assumptions.approx.localRule L g t (.cvt c) = none :=
    approxExact_localRule_none fun f h => by simp [ApproxForm.ofOp] at h
  have h3 : (Assumptions.swExp2 kernel).localRule L g t (.cvt c) = none := rfl
  have h4 : Assumptions.lg2Exact.localRule L g t (.cvt c) = none := by
    simp [Assumptions.lg2Exact]
  have h5 : Assumptions.divFullExact.localRule L g t (.cvt c) = none := by
    simp [Assumptions.divFullExact]
  have h6 : Assumptions.negExact.localRule L g t (.cvt c) = none := by
    simp [Assumptions.negExact]
  have h7 : Assumptions.bf16Exact.localRule L g t (.cvt c) =
      some (.ok (PTX.next (setReg t c.d (.pair (erealValue .bf16 y) (erealValue .bf16 x))))) := by
    simp [Assumptions.bf16Exact, hd, hs, hr, hp, hsr, hx, hy, bindRead, pure, Except.pure]
  rw [hseg.exec rfl]
  simp only [execLocalRule, Assumptions.all, List.findSome?, h1, h2, h3, h4, h5, h6, h7]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax
