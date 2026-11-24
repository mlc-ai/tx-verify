-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.TraceObservations
import Kernels.FlashKdaFwd.Audit.TraceExecution

/-! Relate the debugger run's actual input words to the real recurrence and the bytes
written by the selected PTX store. The public launch omits both optional state tensors. -/
namespace FlashKda.Stateless.RawTrace
open PTX Sequence Chunk Reconstruction
noncomputable section
abbrev MatrixWords := List (Nat × Nat × Nat)
def scalar (cells : MatrixWords) (t i : Nat) : Option ℚ :=
  let v := cells.find? fun (r,c,_) => r == t && c == i
  FloatFmt.bf16.decode ((v.map fun x => x.2.2).getD 0)
def gateValue (t : Nat) := (Observed.rawGate[t]?).bind FloatFmt.bf16.decode

def asReal (words : MatrixWords) (t i : Nat) : ℝ :=
  if t < 33 then ((scalar words t i).getD 0 : ℚ) else 0
def asGate (t : Nat) : ℝ := if t < 33 then ((gateValue t).getD 0 : ℚ) else -40

def fromBuffer : Tokens 128 := activate
  (fun t i => asReal Observed.rawQ t i) (fun t i => asReal Observed.rawK t i)
  (fun t _ => asGate t) (fun t => asReal Observed.rawV t 0)
  (fun t => asReal Observed.rawLogits t 0)
  ((FloatFmt.f32.decode Observed.rawBound).getD 0 : ℚ) 0 (fun _ => 0)

def expectedKey (t i : Nat) : ℚ :=
  if t=15 then (if i=0 then 1 else 0)
  else if t=31 then (if i=0 then 1/2^28 else if i=1 then 1 else 0) else 0

set_option maxRecDepth 12000 in
theorem tensor_words :
    ∀ t : Fin 33, ∀ i : Fin 128,
      scalar Observed.rawQ t i = some (if t.val=32 ∧ i.val=0 then 1 else 0) ∧
      scalar Observed.rawK t i = some (expectedKey t i) ∧
      scalar Observed.rawV t i = some (if t.val=15 ∧ i.val=0 then 3 else 0) ∧
      scalar Observed.rawLogits t 0 = some (if t.val=15 then 1/65536 else 0) ∧
      gateValue t = some (if t.val=31 then 0 else -40) := by decide +kernel

theorem parameters : FloatFmt.f32.decode Observed.rawBound = some (-825889/1048576) ∧
    FloatFmt.f32.decode Observed.rawScale = some 1 := by decide +kernel

theorem model : fromBuffer = inputs := by
  unfold fromBuffer inputs
  congr 1
  · funext t i
    by_cases h : t < 33
    · have hx := (tensor_words ⟨t,h⟩ i).1
      simp only [asReal,h,ite_true,hx,Option.getD_some,rawQuery]
      split_ifs <;> simp_all [Cancellation.pair]
    · simp [asReal,h,rawQuery,Cancellation.pair,show t ≠ 32 by omega]
  · funext t i
    by_cases h : t < 33
    · have hx := (tensor_words ⟨t,h⟩ i).2.1
      simp only [asReal,h,ite_true,hx,Option.getD_some,rawKey,expectedKey,tiny]
      have one : i.val = 1 ↔ i = 1 := ⟨fun z => Fin.ext z, fun z => congrArg Fin.val z⟩
      split_ifs <;> simp_all [Cancellation.pair]
    · simp [asReal,h,rawKey,Cancellation.pair,show t ≠ 15 by omega,show t ≠ 31 by omega]
  · funext t i
    by_cases h : t < 33
    · have hx := (tensor_words ⟨t,h⟩ 0).2.2.2.2
      change gateValue t = some (if t=31 then 0 else -40) at hx
      simp only [asGate,h,ite_true,hx,Option.getD_some,rawGate]
      split_ifs <;> norm_num
    · simp [asGate,h,rawGate,show t ≠ 31 by omega]
  · funext t
    by_cases h : t < 33
    · have hx := (tensor_words ⟨t,h⟩ 0).2.2.1
      change scalar Observed.rawV t 0 = some (if t=15 ∧ (0:ℕ)=0 then 3 else 0) at hx
      simp only [and_true] at hx
      simp only [asReal,h,ite_true,hx,Option.getD_some]
      split_ifs <;> norm_num
    · simp [asReal,h,show t ≠ 15 by omega]
  · funext t
    by_cases h : t < 33
    · have hx := (tensor_words ⟨t,h⟩ 0).2.2.2.1
      change scalar Observed.rawLogits t 0 = some (if t=15 then 1/65536 else 0) at hx
      simp only [asReal,h,ite_true,hx,Option.getD_some]
      split_ifs <;> norm_num
    · simp [asReal,h,show t ≠ 15 by omega]
  · simp [parameters.1,bound]

/-- A run returning the recorded value for these tensors cannot be a correctly rounded
implementation of the real token recurrence on every valid input. -/
theorem public_disagrees :
    FloatFmt.bf16.layout.round .rn .inf
      (Sequence.output fromBuffer (fun _ => 0) 33
        ((FloatFmt.f32.decode Observed.rawScale).getD 0 : ℚ) 32) false =
        some (.fin (65/64)) ∧
    Reconstruction.forward = FloatFmt.bf16.decode Observed.publicWord ∧
    FloatFmt.bf16.layout.decode Observed.publicWord = some (.fin (129/128)) ∧
    (65/64 : ℚ) ≠ 129/128 := by
  rw [model,parameters.2]
  exact ⟨by simpa using exact_output_rounds_up,discrepancy.1,by decide +kernel,by decide +kernel⟩

/-- Any claimed absolute error bound for every input must exceed 1/256 on this one. -/
theorem absolute_error : (1/256 : ℝ) <
    |Sequence.output fromBuffer (fun _ => 0) 33 1 32 -
      ((FloatFmt.bf16.decode Observed.publicWord).getD 0 : ℚ)| := by
  rw [model,end_to_end,show FloatFmt.bf16.decode Observed.publicWord = some (129/128)
    by decide +kernel]
  have lo := interval.1
  change 1/256 < |answer - ((129/128 : ℚ) : ℝ)|
  push_cast
  exact lt_of_lt_of_le (by linarith : (1/256 : ℝ) < answer-129/128) (le_abs_self _)

end
end FlashKda.Stateless.RawTrace
