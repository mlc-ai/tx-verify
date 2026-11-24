-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Ptx
import Kernels.FlashKdaFwd.Audit.FiniteInputs

/-! Exact-real preprocessing with the two binary32 literals emitted by nvcc. -/
namespace FlashKda.Literals
open PTX Chunk Sequence
noncomputable section

def epsilon : ℚ := 8796093 / 2^43
def log2e : ℚ := 12102203 / 2^23

theorem encoded : FloatFmt.f32.layout.decode 0x358637bd = some (.fin epsilon) ∧
    FloatFmt.f32.layout.decode 0x3fb8aa3b = some (.fin log2e) := by decide +kernel

set_option maxRecDepth 16000 in
/-- The actual literals used in the scalar exponential's argument and in the query norm. -/
theorem source_literals :
    Generated.FlashKdaFwd.module.functions[9]!.body[148]? =
      some (.instruction none "mul.ftz.f32" [.register "%r87", .register "%r86",
        .literal "0f3FB8AA3B"]) ∧
    Generated.FlashKdaFwd.module.functions[9]!.body[289]? =
      some (.instruction none "add.ftz.f32" [.register "%r133", .register "%r6",
        .literal "0f358637BD"]) := ⟨rfl, rfl⟩

theorem epsilon_differs : 0 < epsilon ∧ epsilon < 1/1000000 := by decide +kernel

/-- Even exact arithmetic with the emitted epsilon gives a distinct normalization of a unit row. -/
theorem unit_normalization : 1 / Real.sqrt (1 + (1:ℝ)/1000000) <
    1 / Real.sqrt (1 + (epsilon:ℝ)) := by
  have hε : (epsilon:ℝ) < 1/1000000 := by norm_num [epsilon]
  have pos : 0 < 1+(epsilon:ℝ) := by norm_num [epsilon]
  apply one_div_lt_one_div_of_lt (Real.sqrt_pos.mpr pos)
  exact Real.sqrt_lt_sqrt pos.le (by linarith)

variable {d : ℕ}
def normalize (x : Row d) : Row d := fun i => x i / Real.sqrt (dot x x + epsilon)
def sigmoid (x : ℝ) : ℝ := 1 / (1 + (2:ℝ) ^ (-x * log2e))

/-- The gate-scale argument already contains the host's binary32 conversion. -/
def binaryGate (gateScale parameter : ℝ) (bias gate : Row d) (i : Fin d) : ℝ :=
  gateScale * sigmoid ((2:ℝ) ^ (parameter * log2e) * (gate i + bias i))

def tokens (q k gate : ℕ → Row d) (v logits : ℕ → ℝ) (gateScale parameter : ℝ)
    (bias : Row d) : Tokens d where
  query t := normalize (q t)
  key t := normalize (k t)
  value := v
  strength t := sigmoid (logits t)
  logDecay t i := Real.log 2 * binaryGate gateScale parameter bias (gate t) i

/-- With literal-preserving exact arithmetic, the independently defined token recurrence uses
the hardware expressions for the gates and normalization. -/
theorem forward (q k gate : ℕ → Row d) (v logits : ℕ → ℝ) (gateScale parameter : ℝ)
    (bias initial : Row d) (total : ℕ) (scale : ℝ) :
    let x := tokens q k gate v logits gateScale parameter bias
    let state := sequential initial
      (fun t i => (2:ℝ) ^ binaryGate gateScale parameter bias (gate t) i)
      (fun t => normalize (k t)) v (fun t => sigmoid (logits t))
    (∀ t < total, output x initial total scale t = scale * dot (state (t+1)) (normalize (q t))) ∧
      carry x initial total scale ((total+15)/16) = state total := by
  dsimp only
  have h := Sequence.forward (tokens q k gate v logits gateScale parameter bias) initial total scale
  simpa only [tokenState, tokens, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)] using h

end
end FlashKda.Literals
