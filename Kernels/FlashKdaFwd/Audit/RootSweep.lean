-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Proof.RootContract
import Kernels.FlashKdaFwd.Data.RootSweep

/-! Exact interpretation of the exhaustive device sweep. The CUDA launch, its device reduction
and the captured extrema are external observations. The partition, format arithmetic, extrema
words and their conversion to the published relative-error bound are checked here. -/
namespace FlashKda.RootSweep
open PTX RootContract
abbrev scale : Nat := 2^72
abbrev stride : Nat := 4096*256
abbrev minField : Nat := 0x00800000
abbrev stopField : Nat := 0x7f800000

/-- The probe's round and linear thread identifier enumerate each normal input exactly once. -/
def offset (p : Fin 2032 × Fin stride) : Fin (stopField-minField) :=
  ⟨p.1.val*stride + p.2.val,by
    have h₁ := p.1.isLt
    have h₂ : p.2.val < 1048576 := p.2.isLt
    change p.1.val*1048576 + p.2.val < 2130706432
    omega⟩

theorem covers : Function.Bijective offset := by
  constructor
  · intro a b eq
    have z := congrArg Fin.val eq
    have am := a.2.isLt
    have bm := b.2.isLt
    dsimp [offset,stride] at z am bm
    apply Prod.ext <;> apply Fin.ext <;> omega
  · intro i
    have hi : i.val < 2130706432 := i.isLt
    refine ⟨(⟨i.val/stride,by dsimp [stride]; omega⟩,
      ⟨i.val%stride,Nat.mod_lt _ (by decide)⟩), ?_⟩
    apply Fin.ext
    dsimp [offset,stride]
    omega

theorem count : visited = stopField-minField ∧ invalid = 0 ∧
    stopField + stride < 2^32 := by decide +kernel

def exponent (word : Nat) := word / 2^23
def significand (word : Nat) := 2^23 + word % 2^23

theorem field_value {w : Nat} (lo : minField ≤ w) (hi : w < stopField) :
    f32Value w = some (magnitude w) ∧ magnitude w =
      (significand w : ℚ) * (2:ℚ)^((exponent w : ℤ)-150) := by
  change 8388608 ≤ w at lo
  change w < 2139095040 at hi
  have dec := FloatFmt.decode_field .f32 false (F := w) (by
    change w ≤ 2139095039; omega)
  have hn : w ≠ 0 := by omega
  have hq : w/2^23 ≠ 0 := (Nat.div_pos lo (by decide)).ne'
  constructor
  · change (FloatFmt.f32.layout.decode w).bind FVal.num = _
    simpa [Layout.fieldVal,hn,FVal.num,FloatFmt.expBits,FloatFmt.mantBits,FloatFmt.layout]
      using congrArg (fun opt => opt.bind FVal.num) dec
  · simp only [Layout.magnitude,hq,ite_false,significand,exponent]
    congr 2
    norm_num [Layout.bias]
    ring

/-- The high/low 64-bit pair and the carry from shifting the low word reconstruct the
full mathematical integer, including when its high word straddles the power-of-two reference. -/
theorem shifted_limbs (product shift : Nat) :
    ((product/2^64)*2^shift + ((product%2^64)*2^shift)/2^64)*2^64 +
      ((product%2^64)*2^shift)%2^64 = product*2^shift := by
  let m : Nat := 2^64
  let a := product%m*2^shift
  have low := Nat.div_add_mod a m
  have all := congrArg (fun k => k*2^shift) (Nat.div_add_mod product m)
  change (product/m*2^shift + a/m)*m + a%m = _
  rw [Nat.add_mul, Nat.add_assoc, Nat.mul_comm (a/m), low]
  dsimp [a]
  calc
    _ = (m*(product/m)+product%m)*2^shift := by ring
    _ = _ := all

/-- The integer scanned by the probe equals 2^72 times the squared relative ratio y²x. -/
theorem squared_integer {x y : Nat} (xl : minField ≤ x) (xh : x < stopField)
    (yl : minField ≤ y) (yh : y < stopField)
    (lo : 378 ≤ exponent x + 2*exponent y) :
    (significand x * (significand y)^2 * 2^(exponent x+2*exponent y-378) : Nat) =
      (magnitude x * (magnitude y)^2 * (scale : ℚ)) := by
  rw [(field_value xl xh).2, (field_value yl yh).2]
  have e : ((exponent x+2*exponent y-378 : Nat) : ℤ) =
      (exponent x-150 : ℤ) + ((exponent y-150 : ℤ)+(exponent y-150 : ℤ)) + 72 := by
    omega
  have powEq : (2:ℚ)^(exponent x+2*exponent y-378) =
      (2:ℚ)^((exponent x:ℤ)-150) * ((2:ℚ)^((exponent y:ℤ)-150))^2 * 2^72 := by
    rw [← zpow_natCast, e, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num),
      zpow_add₀ (by norm_num)]
    norm_num [pow_two]
  push_cast
  rw [powEq]
  norm_num [scale]
  ring

def extremum (record : Nat × Nat × Nat) (under : Bool) : Prop :=
  let a := record.1
  let b := record.2.1
  let n := (record.2.2 : ℚ)
  let x := magnitude a
  let y := magnitude b
  f32Value a = some x ∧ f32Value b = some y ∧
    x*y^2 = 1 + (if under then -n else n)/scale

instance (r : Nat × Nat × Nat) (under : Bool) : Decidable (extremum r under) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem attained : extremum below true ∧ extremum above false := by decide +kernel

def cap : ℚ := parts / 1000000000000
theorem envelope :
    (1-cap)^2 ≤ 1-(below.2.2 : ℚ)/scale ∧ 1+(above.2.2 : ℚ)/scale ≤ (1+cap)^2 ∧
    (1-(cap-1/1000000000000))^2 > 1-(below.2.2 : ℚ)/scale ∧ cap^10 ≤ 1/2^229 := by
  decide +kernel

noncomputable section
theorem below_spec : (cap : ℝ) ≤ tolerance := by
  by_contra! h
  have pos : 0 ≤ tolerance := le_trans (by norm_num) tolerance_bounds.1
  have strict := pow_lt_pow_left₀ h pos (by decide : 10 ≠ 0)
  rw [tolerance_power] at strict
  have check : (cap:ℝ)^10 ≤ (1:ℝ)/2^229 := by
    simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).2 envelope.2.2.2
  linarith

/-- Any positive-normal pair in the reported squared interval meets the device-specific
bound and the published PTX limit. -/
theorem within {x y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (low : 1-(below.2.2 : ℚ)/scale ≤ y^2*x) (high : y^2*x ≤ 1+(above.2.2 : ℚ)/scale) :
    |(y:ℝ)*√(x:ℝ)-1| ≤ (cap:ℝ) ∧ (cap:ℝ) ≤ tolerance := by
  refine ⟨?_,below_spec⟩
  apply (error_iff (by exact_mod_cast hx) (by exact_mod_cast hy)
    (by norm_num [cap,parts]) (by norm_num [cap,parts])).2
  constructor
  · exact_mod_cast envelope.1.trans low
  · exact_mod_cast high.trans envelope.2.1

/-- The observed low endpoint rules out reducing the reported cap by one part per trillion. -/
theorem tight :
    (cap:ℝ)-1/1000000000000 <
      |(magnitude below.2.1 : ℝ)*√(magnitude below.1 : ℝ)-1| := by
  have bad : (1-(cap-1/1000000000000))^2 > (magnitude below.2.1)^2 * magnitude below.1 :=
    by decide +kernel
  by_contra! contrary
  have h := (error_iff (by exact_mod_cast Layout.magnitude_nonneg 8 23 below.1)
    (by exact_mod_cast Layout.magnitude_nonneg 8 23 below.2.1)
    (by norm_num [cap,parts]) (by norm_num [cap,parts])).1 contrary
  have clash := (Rat.cast_lt (K := ℝ)).2 bad
  push_cast at clash
  exact (not_lt_of_ge h.1) clash

end
end FlashKda.RootSweep
