-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Data.StatelessTrace
import Kernels.FlashKdaFwd.Audit.StatelessCarry
import Kernels.FlashKdaFwd.Audit.StatelessForward
import Kernels.FlashKdaFwd.Audit.NormProducts

/-! Reconstruct the last scalar from the same launch's sparse preparation arrays, two
sigmoid results and raw values. The triangular inverses are identities, the query-key
blocks vanish, and only one token per earlier block has a nonzero key. -/
namespace FlashKda.Stateless.Reconstruction
open PTX Carry Carry.Output
noncomputable section

def atCell (cells : List (Nat × Nat × Nat × Nat)) (b t i : Nat) : Option ℚ :=
  let entry := cells.find? fun (block,row,col,_) => block == b && row == t && col == i
  FloatFmt.bf16.decode ((entry.map fun x => x.2.2.2).getD 0)

def spread (b : Nat) : Option ℚ := (Observed.decay[b]?).bind FloatFmt.f32.decode
def strength (b : Nat) : Option ℚ := do
  let row ← Observed.residualScale[b]?
  FloatFmt.f32.decode (← row[1]?)

def single (x : ℚ) := (FloatFmt.f32.layout.roundVal .rn true (FVal.ofRat x)).bind FVal.num
def brain (x : ℚ) := (bf.round .rn .inf (x : ℝ) false).bind FVal.num
def fused (a b c : ℚ) : Option ℚ := do
  let .val v ← carryUpdate.lane [FVal.ofRat a,FVal.ofRat b,FVal.ofRat c] | none
  v.num

/-- During each of the two updates the entering state row has just its first coordinate
nonzero or is identically zero. The inverse leaves the single correction unchanged. -/
def updateCell (b : Nat) (value state : ℚ) : Option ℚ := do
  let view ← brain state
  let prediction ← single ((← atCell Observed.decayedKey b 15 0) * view)
  let residual ← single (value-prediction)
  let scaled ← single (residual * (← strength b))
  let correction ← brain scaled
  let additive ← single ((← atCell Observed.restoredKey b 15 0) * correction)
  fused state (← spread b) additive

/-- The last token has only one nonzero query coordinate and a zero query-key block. -/
def forward : Option ℚ := do
  let first ← updateCell 0 3 0
  let second ← updateCell 1 0 first
  let acc ← single ((← atCell Observed.decayedQuery 2 0 0) * (← brain second))
  brain acc

def firstBeta : ℚ := 131073/262144
def k : ℚ := 173/2^36
def restoredK : ℚ := 1/2^28
def residual : ℚ := -(3/2)*k
def corrected : ℚ := -65/2^35

theorem workspace :
    atCell Observed.decayedKey 0 15 0 = some 1 ∧ atCell Observed.decayedKey 1 15 0 = some k ∧
    atCell Observed.restoredKey 0 15 0 = some 1 ∧
    atCell Observed.restoredKey 1 15 0 = some restoredK ∧
    atCell Observed.decayedQuery 2 0 0 = some 1 ∧
    spread 0 = some 1 ∧ spread 1 = some multiplier ∧
    strength 0 = some firstBeta ∧ strength 1 = some (1/2) := by decide +kernel

theorem support :
    (∀ b t i : Nat, (b,t,i) ≠ (0,15,0) → (b,t,i) ≠ (1,15,0) → (b,t,i) ≠ (1,15,1) →
      atCell Observed.decayedKey b t i = some 0 ∧ atCell Observed.restoredKey b t i = some 0) ∧
    (∀ b t i : Nat, (b,t,i) ≠ (2,0,0) → atCell Observed.decayedQuery b t i = some 0) ∧
    ∀ b t i : Nat, atCell Observed.queryKey b t i = some 0 := by
  constructor
  · intro b t i h0 h1 h2
    have f (p q r : Nat) (h : (b,t,i) ≠ (p,q,r)) :
        (p == b && q == t && r == i) = false := by
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      by_contra! contra
      apply h
      rcases contra with ⟨⟨rfl,rfl⟩,rfl⟩
      rfl
    simp [atCell, Observed.decayedKey, Observed.restoredKey, f _ _ _ h0, f _ _ _ h1, f _ _ _ h2]
    decide +kernel
  constructor
  · intro b t i h
    have f : (2 == b && 0 == t && 0 == i) = false := by
      by_contra! c
      simp at c
      obtain ⟨rfl,rfl,rfl⟩ := c
      exact h rfl
    simp [atCell, Observed.decayedQuery, f]
    decide +kernel
  · intros
    change FloatFmt.bf16.decode 0 = some 0
    decide +kernel

theorem single_exact {x : ℚ} {bits : Nat} (h : Binary.exactProductField x bits) :
    single x = some x := by
  have p := Binary.product_exact h
  have hx : x ≠ 0 := by
    intro hx
    have m := h.2.2.2
    rw [hx,abs_zero] at m
    exact (by decide +kernel : ¬ OneToken.binary32.minNormal ≤ 0) m
  unfold single
  rw [FVal.ofRat,ite_eq_right hx]
  change (OneToken.binary32.roundVal .rn true (.fin x)).bind FVal.num = _
  unfold Binary.singleProduct at p
  cases hr : OneToken.binary32.roundVal .rn true (.fin x) with
  | none => simp [hr] at p
  | some v => cases v <;> simp [hr,FVal.num] at p ⊢
              exact p

theorem brain_zero : brain 0 = some 0 := by
  simp [brain, Layout.round_zero (m := .rn) (by trivial), FVal.num]
theorem single_zero : single 0 = some 0 := rfl

local macro "values" : tactic => `(tactic|
  norm_num [firstBeta,residual,k,corrected,Layout.magnitude,Layout.bias,RoundMode.away,
    Layout.fieldVal,FVal.num])

theorem first_scaled : brain (3*firstBeta) = some (3/2) := by
  unfold brain
  rw [Layout.round_between (m := .rn) (F := 0x3fc0) (by trivial) (by decide)
    (by values) (by values) (by simp)]
  values

theorem second_scaled : brain (residual/2) = some corrected := by
  unfold brain
  rw [Layout.round_between (m := .rn) (F := 0x3101) (by trivial) (by decide)
    (by values) (by values) (by simp)]
  values

theorem brain_field {x : ℚ} {w : Nat} (hw : 0 < w) (ht : w ≤ bf.topField)
    (eq : x = Layout.magnitude 8 7 w) : brain x = some x := by
  have px : (0:ℝ) < x := by exact_mod_cast eq ▸ Layout.magnitude_pos (eb := 8) (mb := 7) hw
  unfold brain
  rw [Layout.round_exact (m := .rn) (F := w) (by trivial) hw ht
    (by rw [abs_of_pos px]; exact_mod_cast eq) (by simp)]
  simp [Layout.fieldVal,Nat.ne_of_gt hw,FVal.num,eq,
    not_lt.mpr (Layout.magnitude_nonneg 8 7 w)]

theorem first_fma : fused 0 1 (3/2) = some (3/2) := by
  have h : carryUpdate.lane [.zero false,.fin 1,.fin (3/2)] = some (.val (.fin (3/2))) := by
    apply Carry.evaluate (intermediate := .fin (3/2))
    · decide +kernel
    · decide +kernel
    · exact (Normalize.exactField_sound (v := .fin (3/2)) (bits := 0x3fc00000)
        (by decide +kernel)).trans (by decide +kernel)
  unfold fused
  rw [show FVal.ofRat 0 = .zero false by decide +kernel,
    show FVal.ofRat 1 = .fin 1 by decide +kernel,
    show FVal.ofRat (3/2) = .fin (3/2) by decide +kernel,h]
  rfl

theorem second_fma : fused (3/2) multiplier (restoredK*corrected) = some lower := by
  unfold fused
  rw [show FVal.ofRat (3/2) = .fin incoming by decide +kernel,
    show FVal.ofRat multiplier = .fin multiplier by decide +kernel,
    show FVal.ofRat (restoredK*corrected) = .fin delta by decide +kernel,machine_update]
  rfl

theorem reconstructed : forward = some (129/128) := by
  obtain ⟨k0,k1,r0,r1,q2,m0,m1,b0,b1⟩ := workspace
  have carry1 := brain_field (x := (3/2)) (w := 0x3fc0) (by decide) (by decide) (by decide +kernel)
  have published := brain_field (x := (129/128)) (w := 0x3f81) (by decide) (by decide)
    (by decide +kernel)
  have state2 : brain lower = some (129/128) := by simp [brain,next_tile_views.1,FVal.num]
  have cert (x : ℚ) (w : Nat) (h : Binary.exactProductField x w) := single_exact h
  have first : updateCell 0 3 0 = some (3/2) := by
    simp [updateCell,brain_zero,k0,b0,r0,m0,single_zero,cert 3 0x40400000 (by decide +kernel),
      cert (3*firstBeta) 0x3fc00060 (by decide +kernel), first_scaled,
      cert (3/2) 0x3fc00000 (by decide +kernel),first_fma]
  have second : updateCell 1 0 (3/2) = some lower := by
    have negative : -(k*(3/2)) = residual := by unfold residual; ring
    have half : residual*2⁻¹ = residual/2 := by ring
    simp [updateCell,carry1,k1,b1,r1,m1,cert (k*(3/2)) 0x3181c000 (by decide +kernel),
      negative,cert residual 0x3181c000 (by decide +kernel),half,
      cert (residual/2) 0x3101c000 (by decide +kernel),second_scaled,
      cert (restoredK*corrected) 0x23020000 (by decide +kernel),second_fma]
  simp [forward,first,second,q2,state2,cert (129/128) 0x3f810000 (by decide +kernel),published]

theorem discrepancy : forward = FloatFmt.bf16.decode Observed.publicWord ∧
    FloatFmt.bf16.layout.round .rn .inf (Sequence.output inputs (fun _ => 0) 33 1 32) false ≠
      (FVal.fin <$> forward) := by
  rw [reconstructed,exact_output_rounds_up]
  decide +kernel

end
end FlashKda.Stateless.Reconstruction
