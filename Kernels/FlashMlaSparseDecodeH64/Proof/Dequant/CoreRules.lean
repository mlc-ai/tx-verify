-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.GenRules
public import Lemmas.Flow.OutCoreRules

@[expose] public section

/-! # No assumption reads the dequantizer's integer instructions and moves

The lemmas `Tools/out_gen.py` names for Core's forms (`XItem.core_<form>`) in the dequantizer's
runs: at a pc of the role (from 2696 on) no assumption of the kernel has a local rule for an
integer instruction, a move, or an integer conversion (`noRuleInt`, `noRuleMove`, `noRuleCvt`).
The parameter-pointer, shared-bits, dead-pack and peer-pack rules select pcs below 2696; the
numeric rules select floating instructions and the bf16 conversions. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section
variable {L : Launch} {g : Nat}

/-- At a pc of the role the site-selected rules decline every instruction. -/
theorem sited_none {s : TState} {op : Op} (hs : 2696 ≤ s.pc) :
    Assumptions.paramPointers.localRule L g s op = none ∧
      Assumptions.sharedBits.localRule L g s op = none := by
  have hpa : s.pc ∉ paramAdds := by simp [paramAdds]; omega
  have hpf : s.pc ∉ prefetchTensorMapSites := by simp [prefetchTensorMapSites]; omega
  have hsb : Assumptions.sharedBitsSites.contains s.pc = false := by
    simp [Assumptions.sharedBitsSites]; omega
  have hd : Assumptions.deadPackWords s.pc = none :=
    Assumptions.deadPackWords.eq_3 _ (by omega) (by omega)
  have hp : Assumptions.peerPack s.pc = none :=
    Assumptions.peerPack_none_of_outside (.inr (by omega))
  refine ⟨by simp [Assumptions.paramPointers, hpa, hpf], ?_⟩
  simp only [Assumptions.sharedBits, hsb, Bool.false_eq_true, ↓reduceIte,
    Assumptions.deadPackRule_of_none hd, Option.orElse, Assumptions.peerPackRule_of_none hp]

/-- The rules other than the site-selected ones, for an instruction they do not read. -/
theorem noRule_of {op : Op} (pc : Nat) (hp : 2696 ≤ pc)
    (h : ∀ s : TState, ∀ a ∈ [Assumptions.idealArith, Assumptions.approx, Assumptions.mulBf16x2,
      Assumptions.cvtBf16x2, Assumptions.cvtUe8m0, Assumptions.lg2Exact, Assumptions.ncReadOnly,
      Assumptions.storeDrain, Assumptions.commitOrder], a.localRule L g s op = none) :
    NoLocalRule Assumptions.all L g pc op := by
  intro s hs a ha
  obtain ⟨h1, h2⟩ := sited_none (L := L) (g := g) (op := op) (hs ▸ hp)
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact h1
    | exact h2
    | exact h s _ (by simp)

/-- No assumption reads an integer instruction at a pc of the role. -/
theorem noRuleInt {op : Op} (pc : Nat)
    (hk : (match op with | .int _ => true | _ => false) = true := by exact rfl)
    (hp : 2696 ≤ pc := by decide) : NoLocalRule Assumptions.all L g pc op := by
  cases op <;> simp at hk
  exact noRule_of pc hp fun s a ha => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- No assumption reads a move at a pc of the role. -/
theorem noRuleMove {op : Op} (pc : Nat)
    (hk : (match op with | .move _ => true | _ => false) = true := by exact rfl)
    (hp : 2696 ≤ pc := by decide) : NoLocalRule Assumptions.all L g pc op := by
  cases op <;> simp at hk
  exact noRule_of pc hp fun s a ha => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- No assumption reads a conversion that is no bf16 conversion of the kernel's rules and no
ideal or approximate form, at a pc of the role. -/
theorem noRuleCvt {op : Op} (pc : Nat)
    (hk : (match op with | .cvt _ => true | _ => false) = true := by exact rfl)
    (hc : ∀ s : TState, Assumptions.cvtBf16x2.localRule L g s op = none ∧
      Assumptions.cvtUe8m0.localRule L g s op = none := by exact fun _ => ⟨rfl, rfl⟩)
    (hi : Assumption.FloatForm.ofOp op = none := by exact rfl)
    (ha : Assumption.ApproxForm.ofOp op = none := by exact rfl)
    (hp : 2696 ≤ pc := by decide) : NoLocalRule Assumptions.all L g pc op := by
  cases op <;> simp at hk
  exact noRule_of pc hp fun s a h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Assumption.idealReal_localRule_none fun f hf => by rw [hi] at hf; cases hf
    · exact Assumption.approxExact_localRule_none fun f hf => by rw [ha] at hf; cases hf
    · rfl
    · exact (hc s).1
    · exact (hc s).2
    all_goals rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
