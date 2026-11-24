-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Audit.OneToken
public import Kernels.FlashKdaFwd.Proof.Residual
public import Kernels.FlashKdaFwd.Data.ResidualSample
public import Core.Float.Format
import Mathlib.Tactic

/-! Absolute output and state bounds for the recorded 33-token public launch. -/
@[expose] public section
namespace FlashKda.Sample
open Sequence Chunk Stability Algorithm
def Triple.scale (x : Triple) (r : ℚ) : Triple := ⟨x.a*r, x.b*r, x.c*r⟩
def Triple.inner (x y : Triple) := x.a*y.a + x.b*y.b + x.c*y.c
def Triple.sub (x y : Triple) : Triple := ⟨x.a-y.a, x.b-y.b, x.c-y.c⟩
def Triple.add (x y : Triple) : Triple := ⟨x.a+y.a, x.b+y.b, x.c+y.c⟩
def Triple.squared (x : Triple) := x.inner x
def raw (x : Triple) := x.scale (1/128)
def normalized (x : Triple) := x.scale (125/15641)
def measurement (n : Nat) : Measurement := measurements.getD n default
def value (n : Nat) := (measurement n).value/8
def approx : Nat → Triple
  | 0 => ⟨1/4, -1/8, 1/16⟩
  | n+1 => (measurement n).stateNumerator.scale (1/2^30)
def next (s key : Triple) (v : ℚ) := s.add (key.scale ((v - s.inner key)/2))
def delta : ℚ := 1/2^28
def outputValue (t : Nat) := (PTX.FloatFmt.bf16.decode (measurement t).outputWord).getD 0
def finalValue : Triple :=
  ⟨(PTX.f32Value finalWords.1).getD 0, (PTX.f32Value finalWords.2.1).getD 0,
   (PTX.f32Value finalWords.2.2).getD 0⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem checked : ∀ t : Fin 33,
    let r := measurement t.val
    let q := normalized r.query
    let k := normalized r.key
    let s := approx (t.val+1)
    (raw r.query).squared + 1/1000000 = (15641/16000 : ℚ)^2 ∧
    (raw r.key).squared + 1/1000000 = (15641/16000 : ℚ)^2 ∧
    (s.sub (next (approx t.val) k (value t.val))).squared ≤ delta^2 ∧
    PTX.FloatFmt.bf16.decode r.outputWord = some (outputValue t.val) ∧
    |outputValue t.val - s.inner q| + (t.val+1 : ℚ)*delta ≤ 2414/1000000 := by
  decide +kernel

theorem initial_words :
    PTX.f32Value initialWords.1 = some (approx 0).a ∧
    PTX.f32Value initialWords.2.1 = some (approx 0).b ∧
    PTX.f32Value initialWords.2.2 = some (approx 0).c := by decide +kernel

theorem packed_words : packedFinal = finalWords ∧
    ∀ t : Fin 33, packedWords.getD t.val 0 = (measurement t.val).outputWord := by decide +kernel

theorem checked_final :
    PTX.f32Value finalWords.1 = some finalValue.a ∧
    PTX.f32Value finalWords.2.1 = some finalValue.b ∧
    PTX.f32Value finalWords.2.2 = some finalValue.c ∧
    (finalValue.sub (approx 33)).squared ≤ (444/1000000 - 33*delta)^2 := by
  decide +kernel

noncomputable section
def embed (x : Triple) : Row 128 := OneToken.four x.a x.b x.c 0
theorem embed_inner (x y : Triple) : dot (embed x) (embed y) = (x.inner y : ℝ) := by
  simp only [embed, OneToken.dot_four]
  norm_num [OneToken.four, Triple.inner]

theorem embed_apply (x : Triple) (i : Fin 128) :
    embed x i = if i=0 then (x.a : ℝ) else if i=1 then (x.b : ℝ)
      else if i=2 then (x.c : ℝ) else 0 := by
  unfold embed OneToken.four
  split_ifs <;> simp_all

theorem embed_scale (x : Triple) (r : ℚ) (i : Fin 128) :
    embed (x.scale r) i = embed x i * (r : ℝ) := by
  simp only [embed_apply, Triple.scale, Rat.cast_mul]
  split_ifs <;> simp

theorem embed_sub (x y : Triple) :
    embed (x.sub y) = fun i => embed x i - embed y i := by
  funext i
  simp only [embed_apply, Triple.sub, Rat.cast_sub]
  split_ifs <;> simp

theorem embed_add (x y : Triple) (i : Fin 128) :
    embed (x.add y) i = embed x i + embed y i := by
  simp only [embed_apply, Triple.add, Rat.cast_add]
  split_ifs <;> simp

theorem magnitude {x y : Triple} {b : ℚ} (hb : 0 ≤ b) (h : (x.sub y).squared ≤ b^2) :
    distance (embed x) (embed y) ≤ (b : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by exact_mod_cast hb, ?_⟩
  rw [← embed_sub]
  have ee (z : Triple) : energy (embed z) = (z.squared : ℝ) := by
    change energy (embed z) = (z.inner z : ℝ)
    rw [← embed_inner]
    simp [energy, dot, pow_two]
  rw [ee]
  exact_mod_cast h

theorem normalization (x : Triple) (h : (raw x).squared + 1/1000000 = (15641/16000 : ℚ)^2) :
    normalize (embed (raw x)) = embed (normalized x) := by
  have hs : dot (embed (raw x)) (embed (raw x)) + 1/1000000 = (15641/16000 : ℝ)^2 := by
    rw [embed_inner]
    have hc := congrArg (fun z : ℚ => (z : ℝ)) h
    simpa [Triple.squared] using hc
  funext i
  simp only [Algorithm.normalize, hs, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 15641/16000)]
  simp only [raw, normalized, embed_scale]
  push_cast
  ring

theorem embed_next (s k : Triple) (v : ℚ) :
    step (embed s) (fun _ => 1) (embed k) (v : ℝ) (1/2) = embed (next s k v) := by
  funext i
  simp only [step, mul_one, embed_inner, next, embed_add, embed_scale]
  push_cast
  ring

def input : Tokens 128 := activate
  (fun t => embed (raw (measurement t).query)) (fun t => embed (raw (measurement t).key))
  (fun _ _ => 0) (fun t => (value t : ℝ)) (fun _ => 0) 0 0 (fun _ => 0)

theorem state_error (n : Nat) (hn : n ≤ 33) :
    distance (embed (approx n)) (tokenState input (embed (approx 0)) n) ≤
      (n : ℝ) * (delta : ℝ) := by
  induction n with
  | zero => simp [tokenState, sequential, distance, length, energy]
  | succ t ih =>
    have ht : t < 33 := by omega
    obtain ⟨_, hk, hlocal, _, _⟩ := checked ⟨t,ht⟩
    let k := normalized (measurement t).key
    let prior := tokenState input (embed (approx 0)) t
    have hkey : input.key t = embed k := normalization _ hk
    have unit := normalized_energy (embed (raw (measurement t).key))
    rw [normalization _ hk] at unit
    have localBound := magnitude (by norm_num [delta] : 0 ≤ delta) hlocal
    have contraction := step_nonexpansive (embed (approx t)) prior (fun _ => 1) (embed k)
      (value t : ℝ) (1/2) (fun _ => by norm_num) unit (by norm_num)
    have spec : tokenState input (embed (approx 0)) (t+1) =
        step prior (fun _ => 1) (embed k) (value t : ℝ) (1/2) := by
      change step prior _ (input.key t) _ _ = _
      rw [hkey]
      norm_num [input, activate, logGate, sigmoid]
    rw [← embed_next] at localBound
    rw [spec]
    apply (triangle _ _ _).trans
    apply (add_le_add localBound (contraction.trans (ih (by omega)))).trans
    push_cast
    linarith

theorem outputs (t : Fin 33) :
    PTX.FloatFmt.bf16.decode (measurement t.val).outputWord = some (outputValue t.val) ∧
    |(outputValue t.val : ℝ) - output input (embed (approx 0)) 33 1 t.val| ≤ 2414/1000000 := by
  obtain ⟨hq, _, _, bits, readout⟩ := checked t
  refine ⟨bits, ?_⟩
  rw [(forward input _ 33 1).1 t.val t.isLt, one_mul]
  have qeq : input.query t.val = embed (normalized (measurement t.val).query) := normalization _ hq
  have unit := normalized_energy (embed (raw (measurement t.val).query))
  change energy (input.query t.val) ≤ 1 at unit
  have proj := output_bound (embed (approx (t.val+1)))
    (tokenState input (embed (approx 0)) (t.val+1)) (input.query t.val) 1 unit
  simp only [one_mul, abs_one] at proj
  have h := (abs_sub_le (outputValue t.val : ℝ) _ _).trans
    (add_le_add le_rfl (proj.trans (state_error _ (by omega))))
  rw [qeq, embed_inner] at h
  rw [qeq]
  apply h.trans
  have lifted := (Rat.cast_le (K := ℝ)).2 readout
  push_cast at lifted
  simpa using lifted

theorem packed_outputs (t : Fin 33) :
    PTX.FloatFmt.bf16.decode (packedWords.getD t.val 0) = some (outputValue t.val) ∧
    |(outputValue t.val : ℝ) - output input (embed (approx 0)) 33 1 t.val| ≤ 2414/1000000 := by
  rw [packed_words.2 t]
  exact outputs t

theorem final_state :
    distance (embed finalValue) (tokenState input (embed (approx 0)) 33) ≤ 444/1000000 := by
  have h := magnitude (by norm_num [delta] : (0:ℚ) ≤ 444/1000000 - 33*delta)
    checked_final.2.2.2
  have bound := (triangle _ _ _).trans (add_le_add h (state_error 33 (by decide)))
  push_cast at bound
  linarith

/-- Every other value coordinate has zero input value and zero initial state in this sample. -/
theorem zero_channels (x : Tokens 128) (hz : ∀ t, x.value t = 0) :
    (∀ n, tokenState x (fun _ => 0) n = fun _ => 0) ∧
    ∀ total t, t < total → output x (fun _ => 0) total 1 t = 0 := by
  have states (n : Nat) : tokenState x (fun _ => 0) n = fun _ => 0 := by
    induction n with
    | zero => rfl
    | succ t ih =>
      change step (tokenState x (fun _ => 0) t) _ _ _ _ = _
      rw [ih, hz]
      funext i
      simp [step, dot]
  refine ⟨states, fun total t ht => ?_⟩
  rw [(forward x _ total _).1 t ht, states]
  simp [dot]

end
end FlashKda.Sample
