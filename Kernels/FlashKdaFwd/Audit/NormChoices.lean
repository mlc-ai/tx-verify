-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.RootExecution
import Kernels.FlashKdaFwd.Audit.NormProducts

/-! All machine-word outcomes for the two normalization roots under the PTX 9.2
error limit, at the actual PTX sites in both launch modes. -/
namespace FlashKda.NormChoices
open PTX OneToken RootExecution Binary
noncomputable section

def squared (x y e : ℚ) : Prop := (1-e)^2 ≤ y^2*x ∧ y^2*x ≤ (1+e)^2
instance (x y e : ℚ) : Decidable (squared x y e) := inferInstanceAs (Decidable (_ ∧ _))

private theorem squared_iff (key : Bool) (w : Nat) {e : ℚ} (he : 0 ≤ e) (h1 : e ≤ 1) :
    |(mag w : ℝ)*√(inputValue key : ℝ)-1| ≤ (e : ℝ) ↔ squared (inputValue key) (mag w) e := by
  rw [RootContract.error_iff (by cases key <;> norm_num [inputValue])
    (by exact_mod_cast Layout.magnitude_nonneg 8 23 w)
    (by exact_mod_cast he) (by exact_mod_cast h1)]
  unfold squared
  norm_cast

theorem normal_input (key : Bool) : RootContract.normal (inputValue key) := by
  unfold RootContract.normal
  cases key <;> decide +kernel

theorem weaker {key : Bool} {w : Nat} (h : RootContract.allowed (inputValue key) w) :
    admissibleRoot (inputValue key) (mag w) :=
  h.2.2.trans (by linarith [RootContract.tolerance_bounds.2])

theorem words (key : Bool) (w : Nat) : RootContract.allowed (inputValue key) w ↔
    ∃ i : Fin 2, w = measuredWord key + i.val := by
  have range : ∀ k : Bool, ∀ i : Fin 4,
      squared (inputValue k) (mag (firstRootWord k + i.val)) (130/1000000000) →
        i.val=1 ∨ i.val=2 := by decide +kernel
  have pass : ∀ k : Bool, ∀ i : Fin 2, 8388608 ≤ measuredWord k+i.val ∧
      measuredWord k+i.val ≤ RootContract.format.topField ∧
      squared (inputValue k) (mag (measuredWord k+i.val)) (120/1000000000) := by decide +kernel
  constructor
  · intro h
    obtain ⟨i,eq⟩ := (all_root_words key _).1 (weaker h)
    have envelope := h.2.2.trans RootContract.tolerance_bounds.2
    have rat := (squared_iff key w (e := 130/1000000000) (by norm_num) (by norm_num)).1
      (by simpa using envelope)
    rw [eq] at rat
    rcases range key i rat with one | two
    · exact ⟨0,by simp [eq,one,measuredWord]⟩
    · exact ⟨1,by simp [eq,two,measuredWord,Nat.add_assoc]⟩
  · rintro ⟨i,rfl⟩
    obtain ⟨a,b,c⟩ := pass key i
    refine ⟨a,b,?_⟩
    have h := (squared_iff key _ (by norm_num) (by norm_num)).2 c
    apply h.trans
    simpa using RootContract.tolerance_bounds.1

/-- In each compiled entry the key root comes first, then the query root. -/
def src (packed key : Bool) : Nat :=
  if packed then (if key then 341 else 343) else (if key then 333 else 335)
def dst (packed key : Bool) := src packed key + 1
def entry (packed : Bool) := if packed then 1 else 9
def sites (packed : Bool) := Normalize.sites (entry packed)
  (if packed then [125,174,176] else [92,141,143])
def roots (packed : Bool) := (sites packed).map List.tail

theorem decoded (packed : Bool) : roots packed = some ([true,false].map fun key =>
    Normalize.rootAt (src packed key) (dst packed key)) := by
  cases packed
  · change (Normalize.sites 9 [92,141,143]).map List.tail = _
    rw [Normalize.fixed_sites]; rfl
  · change (Normalize.sites 1 [125,174,176]).map List.tail = _
    rw [Normalize.packed_sites]; rfl

theorem successors (packed key : Bool) (L : Launch) (g : Nat) (t after : TState)
    (read : t.regs (src packed key) = some (bits32 (inputWord key))) :
    (∃ pick, execLocalA [assumption pick] L g t
      (.float (Normalize.rootAt (src packed key) (dst packed key))) = .ok after) ↔
    ∃ i : Fin 2, after = next (setReg t (dst packed key) (bits32 (measuredWord key+i.val))) := by
  have operand := source_word read (by cases key <;> decide) (binary_arguments.2 key)
  rw [outcomes L g t after _ _ operand (normal_input key)]
  constructor
  · rintro ⟨w,h,rfl⟩
    obtain ⟨i,rfl⟩ := (words key w).1 h
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨_,(words key _).2 ⟨i,rfl⟩,rfl⟩

theorem arithmetic_result (q k : Fin 2) :
    outputUsingRoots (mag (measuredWord false+q.val)) (mag (measuredWord true+k.val)) =
      some (.fin (69/262144)) ∧ answer (1/32) 1 < 0 :=
  all_rounded_outputs _ _ (weaker ((words false _).2 ⟨q,rfl⟩))
    (weaker ((words true _).2 ⟨k,rfl⟩))

/-- Feed the actual destination-register words into the subsequent scalar arithmetic. -/
def fromRegisters (packed : Bool) (q k : TState) : Option FVal := do
  let .fin a ← source q (dst packed false) | none
  let .fin b ← source k (dst packed true) | none
  outputUsingRoots a b

private theorem result_word (t : TState) (r : Nat) (key : Bool) (i : Fin 2) :
    source (next (setReg t r (bits32 (measuredWord key+i.val)))) r =
      some (.fin (mag (measuredWord key+i.val))) :=
  source_word (by simp [next,setReg]) (by cases key <;> fin_cases i <;> decide)
    (RootContract.decode ((words key _).2 ⟨i,rfl⟩))

theorem from_execution (packed : Bool) (L : Launch) (g : Nat)
    (q k qAfter kAfter : TState) (qp kp : Proposal)
    (qr : q.regs (src packed false) = some (bits32 (inputWord false)))
    (kr : k.regs (src packed true) = some (bits32 (inputWord true)))
    (qe : execLocalA [assumption qp] L g q
      (.float (Normalize.rootAt (src packed false) (dst packed false))) = .ok qAfter)
    (ke : execLocalA [assumption kp] L g k
      (.float (Normalize.rootAt (src packed true) (dst packed true))) = .ok kAfter) :
    fromRegisters packed qAfter kAfter = some (.fin (69/262144)) ∧ answer (1/32) 1 < 0 := by
  obtain ⟨i,rfl⟩ := (successors packed false L g q qAfter qr).1 ⟨qp,qe⟩
  obtain ⟨j,rfl⟩ := (successors packed true L g k kAfter kr).1 ⟨kp,ke⟩
  simpa [fromRegisters,result_word] using arithmetic_result i j

end
end FlashKda.NormChoices
