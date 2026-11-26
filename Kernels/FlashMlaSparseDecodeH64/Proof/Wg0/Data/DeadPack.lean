-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataFacts
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.GenRules
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CtlSteps
public import Lemmas.Flow.EmuStep

@[expose] public section

/-! # The dead pack of the scale factor (pc 712)

The `mov.b64` at pc 712 packs the scale factor (`%r2493`, register 2951) with an unwritten word;
the kernel's assumption `sharedBits` makes it the factor with a zero high half
(`Assumptions.deadPackRule`). `seg_712` is the control segment: for any valuation `V`, the facts
`factsFrom keys V` with `V 2951` at the pack, the register 3565 holds `joinValue (V 2951)
(.bits 32 0)` after it, or the thread is dead (the factor is not a 4-byte word). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof

noncomputable section

variable {L : Launch} {g : Nat}

/-- The pack at pc 712. -/
def pack712 : Op :=
  .move ⟨.pack, .int .b 64, [some 3565], [.reg 2951, .reg 1715]⟩

/-- At pc 712 every assumption other than `sharedBits` declines the pack. -/
theorem execLocalA_712 {t : TState} (hpc : t.pc = 712) :
    execLocalA Assumptions.all L g t pack712 =
      (Assumptions.deadPackRule L g t pack712).getD (execLocal L g t pack712) := by
  have hpa : t.pc ∉ paramAdds := by simp [paramAdds, hpc]
  have hpf : t.pc ∉ prefetchTensorMapSites := by simp [prefetchTensorMapSites, hpc]
  have hsb : Assumptions.sharedBitsSites.contains t.pc = false := by
    simp [Assumptions.sharedBitsSites, hpc]
  rw [execLocalA_noSegment (fun a ha => noSegments a ha L g t), execLocalRule]
  simp only [Assumptions.all, List.findSome?_cons, List.findSome?_nil]
  have hpar : Assumptions.paramPointers.localRule L g t pack712 = none := by
    simp [Assumptions.paramPointers, hpa, hpf]
  have hsh : Assumptions.sharedBits.localRule L g t pack712 =
      Assumptions.deadPackRule L g t pack712 := by
    simp only [Assumptions.sharedBits, hsb, Bool.false_eq_true, ↓reduceIte]
    unfold Assumptions.deadPackRule pack712
    rw [hpc]
    simp [Assumptions.deadPackWords, Option.orElse, Assumptions.peerPackRule]
  rw [show Assumptions.idealArith.localRule L g t pack712 = none from rfl,
    show Assumptions.approx.localRule L g t pack712 = none from rfl,
    show Assumptions.mulBf16x2.localRule L g t pack712 = none from rfl,
    show Assumptions.cvtBf16x2.localRule L g t pack712 = none from rfl,
    show Assumptions.cvtUe8m0.localRule L g t pack712 = none from rfl,
    show Assumptions.lg2Exact.localRule L g t pack712 = none from rfl,
    show Assumptions.ncReadOnly.localRule L g t pack712 = none from rfl, hpar,
    show Assumptions.storeDrain.localRule L g t pack712 = none from rfl, hsh,
    show Assumptions.commitOrder.localRule L g t pack712 = none from rfl]
  cases Assumptions.deadPackRule L g t pack712 <;> rfl

/-- The pack either writes the factor with a zero high half or faults. -/
theorem exec_pack712 {t : TState} (hpc : t.pc = 712) {v : Value} (h : t.regs 2951 = some v) :
    execLocalA Assumptions.all L g t pack712 =
        .ok (PTX.next (setReg t 3565 (joinValue v (.bits 32 0)))) ∨
      ∃ f, execLocalA Assumptions.all L g t pack712 = .error f := by
  rw [execLocalA_712 hpc]
  have hd : Assumptions.deadPackWords t.pc = some (3565, 2951, 1715) := by rw [hpc]; rfl
  by_cases h4 : v.bytes = 4
  · left
    simp [Assumptions.deadPackRule, pack712, hd, readValue, readReg, h, h4, bind, Except.bind,
      pure, Except.pure]
  · right
    refine ⟨.typeMismatch, ?_⟩
    simp [Assumptions.deadPackRule, pack712, hd, readValue, readReg, h, h4, bind, Except.bind,
      pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- **The control segment of the dead pack** from any valuation of the facts' registers. -/
theorem seg_712 (L : Launch) (g : Nat) (V : Nat → Value) :
    SegU kernel Assumptions.all L g 712 (factsFrom [2951, 467, 3243, 2950, 2955, 2885, 2880] V) 713
      ((3565, joinValue (V 2951) (.bits 32 0)) ::
        factsFrom [2951, 467, 3243, 2950, 2955, 2885, 2880] V) := by
  intro t ht
  obtain ⟨hpc, hsub, hacc, hflt, hF⟩ := id ht
  have h := holds_mem hF (mem_factsFrom (show 2951 ∈ [2951, 467, 3243, 2950, 2955, 2885, 2880]
    by decide))
  rcases exec_pack712 hpc h with he | ⟨f, he⟩
  · exact .inl ⟨_, run_rtg (run_local (op := pack712) Flow.code_712 rfl ht he),
      At.set ht (not_mem_factsFrom (by decide))⟩
  · exact .inr (dead_of_error (op := pack712) (hpc ▸ Flow.code_712) rfl hflt he)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
