-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.RcpCore
import Kernels.InklingRelDecode.Proof.Lib.Segments

@[expose] public section

/-! # The assumptions at pc 2602 read the reciprocal as its exact function

`rcp.approx.f32` at pc 2602 is read by the approximation assumption; no other assumption of the
kernel applies at that pc. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

/-- At pc 2602 the kernel's assumptions read `rcp.approx.f32` as its exact function, or leave it
to the Core rule. -/
theorem approx_2602 {L : Launch} {g : Nat} {t : TState} (h : t.pc = 2602) :
    ApproxAt Assumptions.all (.rcp .f32) L g t ∧ ApproxDeclineAt Assumptions.all (.rcp .f32) L g t
    := by
  have key : ∀ op, ApproxForm.ofOp op = some (.rcp .f32) →
      execLocalA Assumptions.all L g t op = match execApproxExact t op with
        | some r => r
        | none => execLocal L g t op := by
    intro op hf
    have hseg : SegFreePc Assumptions.all t.pc :=
      Kernels.InklingRelDecode.Proof.segFree (by rw [h]; decide +kernel)
    have h1 : Assumptions.idealArith.localRule L g t op = none :=
      idealReal_localRule_none fun f' h' => by
        rw [Flow.floatForm_none_of_approx hf] at h'; cases h'
    have h3 : Assumptions.approx.localRule L g t op = execApproxExact t op :=
      approxExact_localRule_of hf (by simp)
    have h4 : (Assumptions.swExp2 kernel).localRule L g t op = none := rfl
    have h5 : Assumptions.lg2Exact.localRule L g t op = none := by
      simp [Assumptions.lg2Exact, Assumptions.lg2Sites, h]
    have h6 : Assumptions.divFullExact.localRule L g t op = none := by
      simp [Assumptions.divFullExact, Assumptions.divFullSites, h]
    have h7 : Assumptions.negExact.localRule L g t op = none := by
      simp [Assumptions.negExact, Assumptions.negSites, h]
    have h8 : Assumptions.bf16Exact.localRule L g t op = none := by
      simp only [Assumptions.bf16Exact]
      cases op <;> simp_all [ApproxForm.ofOp]
    rw [hseg.exec rfl]
    simp only [execLocalRule, Assumptions.all, List.findSome?, h1, h3, h4, h5, h6, h7, h8]
    rcases hE : execApproxExact t op with _ | r <;> rfl
  exact ⟨fun op hf e he => by rw [key op hf, he], fun op hf he => by rw [key op hf, he]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Lib
