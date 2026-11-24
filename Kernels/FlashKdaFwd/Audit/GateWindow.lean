-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.Orthogonal
import Kernels.FlashKdaFwd.Proof.GatedOperands

/-! Certify both rounded matrix inputs for every allowed exponential, starting from the
measured binary32 gate prefix and inverse norm. Only the first coordinate changes. -/
namespace FlashKda.Orthogonal
open PTX OneToken GatedOperands RootContract
noncomputable section

def negPrefix (changed : Bool) : ℚ := if changed then 11422685/4194304 else 7563877/2097152
def root : ℚ := 16777207/16777216
def scale32 : ℚ := 11863283/134217728
def below (changed : Bool) : ℚ := if changed then 66031/10000 else 121800/10000
def above (changed : Bool) : ℚ := if changed then 66054/10000 else 121842/10000

theorem source_words (changed : Bool) :
    decoded binary32 (if changed then 0xc02e4bdd else 0xc066d4ca) = some (-negPrefix changed) ∧
    decoded binary32 0x3f7ffff7 = some root ∧ decoded binary32 0x3db504f3 = some scale32 := by
  cases changed <;> decide +kernel

private theorem lift_powers {p q z : ℚ} {m n : Nat} (hq : 0 ≤ q)
    (e : (m:ℚ) ≤ z*2048 ∧ z*2048 ≤ (n:ℚ))
    (cert : p^2048 ≤ (2:ℚ)^m ∧ (2:ℚ)^n ≤ q^2048) :
    (p:ℝ) ≤ (2:ℝ)^(z:ℝ) ∧ (2:ℝ)^(z:ℝ) ≤ (q:ℝ) := by
  have lo : (m:ℝ) ≤ (z:ℝ)*2048 := by exact_mod_cast e.1
  have hi : (z:ℝ)*2048 ≤ (n:ℝ) := by exact_mod_cast e.2
  have low := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) lo
  have high := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hi
  have arr : ((2:ℝ)^(z:ℝ))^2048 = (2:ℝ)^((z:ℝ)*2048) := by
    rw [← Real.rpow_mul_natCast (by norm_num)]; norm_num
  simp only [Real.rpow_natCast] at low high
  constructor
  · apply le_of_not_gt
    intro bad
    have big := pow_lt_pow_left₀ bad (by positivity) (by decide : 2048 ≠ 0)
    rw [arr] at big
    exact (not_lt_of_ge ((by exact_mod_cast cert.1 : (p:ℝ)^2048 ≤ 2^m).trans low)) big
  · apply le_of_not_gt
    intro bad
    have big := pow_lt_pow_left₀ bad (by exact_mod_cast hq) (by decide : 2048 ≠ 0)
    rw [arr] at big
    exact (not_lt_of_ge (high.trans (by exact_mod_cast cert.2 : (2:ℝ)^n ≤ (q:ℝ)^2048))) big

set_option maxRecDepth 15000 in
theorem exponential_range (changed : Bool) :
    (below changed : ℝ) ≤ (2:ℝ)^(negPrefix changed : ℝ) ∧
      (2:ℝ)^(negPrefix changed : ℝ) ≤ above changed := by
  cases changed
  · exact lift_powers (m := 7386) (n := 7387) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact lift_powers (m := 5577) (n := 5578) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- Both approximations are bounded separately using the NVIDIA two-ulp envelope. -/
theorem factor_ranges (changed : Bool) {a b : ℝ}
    (ha : GatePair.allowed (-(negPrefix changed:ℝ)) a)
    (hb : GatePair.allowed (negPrefix changed:ℝ) b) :
    (1-GatePair.unitError)/(above changed:ℝ) ≤ a ∧
      a ≤ (1+GatePair.unitError)/(below changed:ℝ) ∧
    (1-GatePair.unitError)*(below changed:ℝ) ≤ b ∧
      b ≤ (1+GatePair.unitError)*(above changed:ℝ) := by
  have z : |(negPrefix changed:ℝ)| ≤ 120 := by cases changed <;> norm_num [negPrefix]
  have da := abs_le.mp (GatePair.relative (by simpa using z) ha)
  have db := abs_le.mp (GatePair.relative z hb)
  have range := exponential_range changed
  let x := (2:ℝ)^(negPrefix changed:ℝ)
  have xp : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have low : 0 < (below changed:ℝ) := by cases changed <;> norm_num [below]
  have ea : (2:ℝ)^(-(negPrefix changed:ℝ)) = 1/x := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),one_div]
  rw [ea] at da
  have dl : (1-GatePair.unitError)/x ≤ a := calc
    _ = 1/x-GatePair.unitError*(1/x) := by ring
    _ ≤ a := by linarith only [da.1]
  have dh : a ≤ (1+GatePair.unitError)/x := calc
    _ ≤ 1/x+GatePair.unitError*(1/x) := by linarith only [da.2]
    _ = _ := by ring
  refine ⟨le_trans (div_le_div_of_nonneg_left (by norm_num [GatePair.unitError]) xp range.2) dl,
    dh.trans (div_le_div_of_nonneg_left (by norm_num [GatePair.unitError]) low range.1),?_,?_⟩
  · calc
      _ ≤ (1-GatePair.unitError)*x :=
        mul_le_mul_of_nonneg_left range.1 (by norm_num [GatePair.unitError])
      _ ≤ b := by dsimp [x]; linarith [db.1]
  · calc
      _ ≤ (1+GatePair.unitError)*x := by dsimp [x]; linarith [db.2]
      _ ≤ _ := by gcongr; exact range.2

def queryLo (changed : Bool) : ℚ := if changed then 6690/1000000 else 3627/1000000
def queryHi (changed : Bool) : ℚ := if changed then 6694/1000000 else 3629/1000000
def keyLo (changed : Bool) : ℚ := if changed then 3301/1000 else 6089/1000
def keyHi (changed : Bool) : ℚ := if changed then 3303/1000 else 6093/1000
def signedKey (negative : Bool) : ℚ := if negative then -root/2 else root/2

/-- Include both binary32 query multiplications and the key multiplication before narrowing. -/
theorem operands (changed negative : Bool) {a b : ℝ} {u v k : ℚ}
    (ha : GatePair.allowed (-(negPrefix changed:ℝ)) a)
    (hb : GatePair.allowed (negPrefix changed:ℝ) b)
    (p : Single ((root:ℝ)/2*a) u) (s : Single ((u:ℝ)*scale32) v)
    (key : Single ((signedKey negative:ℝ)*b) k) :
    (queryLo changed : ℝ) ≤ v ∧ (v:ℝ) ≤ queryHi changed ∧
    (keyLo changed : ℝ) ≤ (if negative then -(k:ℝ) else (k:ℝ)) ∧
    (if negative then -(k:ℝ) else (k:ℝ)) ≤ keyHi changed := by
  obtain ⟨a0,a1,b0,b1⟩ := factor_ranges changed ha hb
  have pe := abs_le.mp (single_err p)
  have se := abs_le.mp (single_err s)
  have ke := abs_le.mp (single_err key)
  have ap : 0 ≤ a := by apply le_trans _ a0; cases changed <;> norm_num [GatePair.unitError,above]
  have bp : 0 ≤ b := by apply le_trans _ b0; cases changed <;> norm_num [GatePair.unitError,below]
  have up : 0 ≤ (u:ℝ) := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num [root]) ap)] at pe
    norm_num [root] at pe
    linarith [pe.1]
  rw [abs_of_nonneg (mul_nonneg (by norm_num [root]) ap)] at pe
  rw [abs_of_nonneg (mul_nonneg up (by norm_num [scale32]))] at se
  cases negative <;> cases changed <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    norm_num [signedKey,root,scale32,below,above,queryLo,queryHi,keyLo,keyHi,GatePair.unitError,
      abs_mul,abs_of_nonneg bp] at a0 a1 b0 b1 pe se ke ⊢ <;>
    constructor <;> first | linarith [pe.1,pe.2,se.1,se.2,ke.1,ke.2] |
      constructor <;> first | linarith [pe.1,pe.2,se.1,se.2,ke.1,ke.2] |
        constructor <;> linarith [pe.1,pe.2,se.1,se.2,ke.1,ke.2]

def queryValue (changed : Bool) : ℚ := if changed then 219/32768 else 119/32768
def keyValue (changed negative : Bool) : ℚ :=
  let mag := if changed then 211/64 else 195/32
  if negative then -mag else mag

local macro "remove_abs" : tactic => `(tactic|
  first | rw [abs_of_pos (by linarith)] | rw [abs_of_neg (by linarith)])

local macro "narrow_cell" f:num : tactic => `(tactic| (
  rw [Layout.round_between (m := .rn) (F := $f) (by trivial) (by decide)
    (by remove_abs; norm_num [Layout.magnitude,Layout.bias]; linarith)
    (by remove_abs; norm_num [Layout.magnitude,Layout.bias]; linarith) (by simp)]
  remove_abs
  norm_num [RoundMode.away,Layout.fieldVal,Layout.magnitude,Layout.bias]
  split_ifs <;> norm_num [Layout.magnitude,Layout.bias] <;>
    (first | apply And.intro | skip) <;> linarith))

theorem query_narrow (changed : Bool) (v : ℝ) (lo : (queryLo changed : ℝ) ≤ v)
    (hi : v ≤ (queryHi changed : ℝ)) :
    brainFloat.round .rn .inf v false = some (.fin (queryValue changed)) := by
  cases changed <;> norm_num [queryLo,queryHi,queryValue] at *
  · narrow_cell 0x3b6d
  · narrow_cell 0x3bdb

theorem key_narrow (changed negative : Bool) (k : ℝ)
    (lo : (keyLo changed : ℝ) ≤ (if negative then -k else k))
    (hi : (if negative then -k else k) ≤ (keyHi changed : ℝ)) :
    brainFloat.round .rn .inf k false = some (.fin (keyValue changed negative)) := by
  cases changed <;> cases negative <;> norm_num [keyLo,keyHi,keyValue] at *
  · narrow_cell 0x40c2
  · narrow_cell 0x40c2
  · narrow_cell 0x4053
  · narrow_cell 0x4053

/-- Both bfloat16 operands are forced for every eligible approximate output at both
exponential sites, given the recorded gate prefix and normalization result. -/
theorem unique_operands (changed negative : Bool) {a b : ℝ} {u v k : ℚ}
    (ha : GatePair.allowed (-(negPrefix changed:ℝ)) a)
    (hb : GatePair.allowed (negPrefix changed:ℝ) b)
    (p : Single ((root:ℝ)/2*a) u) (s : Single ((u:ℝ)*scale32) v)
    (key : Single ((signedKey negative:ℝ)*b) k) :
    brainFloat.round .rn .inf (v:ℝ) false = some (.fin (queryValue changed)) ∧
    brainFloat.round .rn .inf (k:ℝ) false = some (.fin (keyValue changed negative)) := by
  obtain ⟨l,h,lk,hk⟩ := operands changed negative ha hb p s key
  exact ⟨query_narrow changed _ l h,key_narrow changed negative _ lk hk⟩


/-- Evaluate the measured register-to-operand path for arbitrary acceptable paired
exponential values. Both rounding operations for the query are explicit. -/
def stored (negative : Bool) (a b : ℝ) : Option (FVal × FVal) := do
  let u ← single ((root:ℝ)/2*a)
  let v ← single ((u:ℝ)*scale32)
  let k ← single ((signedKey negative:ℝ)*b)
  return (← brainFloat.round .rn .inf (v:ℝ) false, ← brainFloat.round .rn .inf (k:ℝ) false)

theorem stored_words (changed negative : Bool) {a b : ℝ}
    (ha : GatePair.allowed (-(negPrefix changed:ℝ)) a)
    (hb : GatePair.allowed (negPrefix changed:ℝ) b) :
    stored negative a b = some (.fin (queryValue changed),.fin (keyValue changed negative)) := by
  obtain ⟨a0,a1,b0,b1⟩ := factor_ranges changed ha hb
  have aq : 1/32 ≤ a ∧ a ≤ 1 := by
    cases changed <;> norm_num [GatePair.unitError,above,below] at * <;> constructor <;> linarith
  have bk : 1 ≤ b ∧ b ≤ 16 := by
    cases changed <;> norm_num [GatePair.unitError,above,below] at * <;> constructor <;> linarith
  have ap : 0 ≤ (root:ℝ)/2*a := by norm_num [root]; linarith [aq.1]
  have firstBand : band ((root:ℝ)/2*a) := by
    right; rw [abs_of_nonneg ap]
    norm_num [root]; constructor <;> linarith [aq.1,aq.2]
  obtain ⟨u,ur,ue⟩ := single_value firstBand
  rw [abs_of_nonneg ap,abs_le] at ue
  have un : 0 ≤ (u:ℝ) := by
    norm_num [root] at ue
    linarith [ue.1,aq.1]
  have up : 0 ≤ (u:ℝ)*scale32 := mul_nonneg un (by norm_num [scale32])
  have secondBand : band ((u:ℝ)*scale32) := by
    right; rw [abs_of_nonneg up]
    norm_num [root,scale32] at ue ⊢
    constructor <;> linarith [ue.1,ue.2,aq.1,aq.2]
  have bp : 0 ≤ b := by linarith [bk.1]
  have keyBand : band ((signedKey negative:ℝ)*b) := by
    right
    rw [abs_mul,abs_of_nonneg bp]
    cases negative <;> norm_num [signedKey,root] <;> constructor <;> linarith [bk.1,bk.2]
  obtain ⟨v,vr,_⟩ := single_value secondBand
  obtain ⟨k,kr,_⟩ := single_value keyBand
  obtain ⟨qw,kw⟩ := unique_operands changed negative ha hb
    ⟨firstBand,ur⟩ ⟨secondBand,vr⟩ ⟨keyBand,kr⟩
  simp [stored,ur,vr,kr,qw,kw]

/-- The selected pair of bfloat16 words is exactly the one read from the two shared
matrices. Only coordinate zero uses the changed gate, and coordinates two and three
carry the negative sign in the key. -/
theorem stored_matches (changed : Bool) (i : Fin 4) {a b : ℝ}
    (ha : GatePair.allowed (-(negPrefix (changed && i == 0):ℝ)) a)
    (hb : GatePair.allowed (negPrefix (changed && i == 0):ℝ) b) :
    (stored (decide (2 ≤ i.val)) a b).map (fun (q,k) => (q.num,k.num)) =
    some (decoded brainFloat (queryWords changed i), decoded brainFloat (keyWords changed i)) := by
  rw [stored_words _ _ ha hb]
  cases changed <;> fin_cases i <;> decide +kernel

/-- Exact dot of the four prepared nonzero pairs followed by the two device-format
conversions and the strength factor. The exact dot equals the measured accumulator. -/
def readout (a b : Fin 4 → ℝ) : Option ℚ := do
  let dot ← exactDot fun i =>
    (stored (decide (2 ≤ i.val)) (a i) (b i)).map (fun (q,k) => (q.num,k.num))
  let acc ← (brainFloat.round .rn .inf (dot:ℝ) false).bind FVal.num
  (brainFloat.round .rn .inf ((acc:ℝ)/2) false).bind FVal.num

/-- All allowed exponential results yield the recorded output, conditional only on the
measured incoming prefix and normalization words and the exact four-term contraction. -/
theorem readout_forced (changed : Bool) (a b : Fin 4 → ℝ)
    (ha : ∀ i, GatePair.allowed (-(negPrefix (changed && i == 0):ℝ)) (a i))
    (hb : ∀ i, GatePair.allowed (negPrefix (changed && i == 0):ℝ) (b i)) :
    readout a b = some (score changed/2) := by
  have dot : (exactDot fun i =>
      (stored (decide (2 ≤ i.val)) (a i) (b i)).map (fun (q,k) => (q.num,k.num))) =
      some (score changed) := by
    calc
      _ = cell changed :=
        congrArg exactDot (funext fun i => stored_matches changed i (ha i) (hb i))
      _ = _ := (contraction changed).1
  simp [readout,dot,(conversions changed).1,(conversions changed).2]

end
end FlashKda.Orthogonal
