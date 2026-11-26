-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidSnoc
public import Lemmas.Order.OrderBaseCausality

@[expose] public section

/-! # The elements of a vector access and the pcs that are not quiet

Facts of runs (`SameAccess`) used by the step of warpgroup 0's trace: the consecutive elements of a
run are consecutive accesses (`sameAccess_adj`), every event of a run has an access, and an
event that is not quiet is at one of the pcs a clause lemma handles (`w0Quiet_or`). -/

/-! # Validity through the end of a vector access

`W0Run P L X w`: for an event `w = (g, k)` of warpgroup 0 the lane's prefix is valid through
every element `m` of the vector access that starts at `k`. Its proof at `w` starts from the run
start `s` of `w` (`runStart`: the least `s` with `SameAccess (g, s) (g, k)`, or `k`), where the
program order gives the validity of the prefix before the run, and steps through the run
(`W0Run.of_step`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {X : Execution}

theorem Acc.shift_shift (a b : Nat) (x : Acc) :
    Acc.shift a (Acc.shift b x) = Acc.shift (b + a) x := by
  simp only [Acc.shift, Loc.at, Nat.add_mul, Nat.add_assoc]

/-- **A prefix of a run is a run.** -/
theorem sameAccess_mid {g s j m : Nat} (h : SameAccess X (g, s) (g, m)) (h1 : s ≤ j)
    (h2 : j ≤ m) : SameAccess X (g, s) (g, j) := by
  obtain ⟨hf, hd⟩ := h
  have hs : ((X.get (g, s)).bind Event.acc).isSome := by
    have := hd (m - s) le_rfl
    rw [show s + (m - s) = m by omega] at this
    cases ha : (X.get (g, s)).bind Event.acc with
    | none => rw [ha] at this; simp [this] at hf
    | some a => simp
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
  refine ⟨?_, fun d hd' => hd d (by simp only at hd' ⊢; omega)⟩
  have := hd (j - s) (by omega)
  rw [show s + (j - s) = j by omega, ha] at this
  simp [this]

/-- **Runs compose.** -/
theorem sameAccess_trans {g s k m : Nat} (h1 : SameAccess X (g, s) (g, k))
    (h2 : SameAccess X (g, k) (g, m)) (hsk : s ≤ k) (hkm : k ≤ m) :
    SameAccess X (g, s) (g, m) := by
  refine ⟨h2.1, fun d hd => ?_⟩
  simp only at hd ⊢
  by_cases hdk : d ≤ k - s
  · exact h1.2 d (by simpa using hdk)
  · have e1 := h1.2 (k - s) le_rfl
    have e2 := h2.2 (d - (k - s)) (by simp only; omega)
    simp only [show s + (k - s) = k by omega] at e1
    simp only [show k + (d - (k - s)) = s + d by omega] at e2
    rw [e2, e1]
    cases (X.get (g, s)).bind Event.acc <;> simp [Acc.shift_shift, show
      k - s + (d - (k - s)) = d by omega]

/-- **The run start of an event.** -/
theorem runStart (X : Execution) (g k : Nat) :
    ∃ s, s ≤ k ∧ (s = k ∨ SameAccess X (g, s) (g, k)) ∧
      ∀ j, j < s → ¬ SameAccess X (g, j) (g, k) := by
  classical
  have hex : ∃ s, s ≤ k ∧ (s = k ∨ SameAccess X (g, s) (g, k)) := ⟨k, le_rfl, Or.inl rfl⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun j hj hs => ?_⟩
  have hjk : j ≤ k := by have := (Nat.find_spec hex).1; omega
  exact Nat.find_min hex hj ⟨hjk, Or.inr hs⟩

/-- A run element is a memory access, unless the run is the single event. -/
def RunIn (X : Execution) (g s m j : Nat) : Prop :=
  s ≤ j ∧ j ≤ m ∧ (j = s ∨ SameAccess X (g, s) (g, j))

/-- **The claim `Q`**: the lane's prefix is valid through every element of the run at `w` that is
no undefined behaviour. -/
def W0Run (P : Params) (L : Launch) (X : Execution) (w : EvId) : Prop :=
  warp L w.1 < 4 → ∀ m, w.2 ≤ m → (m = w.2 ∨ SameAccess X w (w.1, m)) → NonUbAt X (w.1, m) →
    W0Valid P.scale ((X.tr w.1).take (m + 1))

theorem W0Run.valid {w : EvId} (h : W0Run P L X w) (hw : warp L w.1 < 4) (hn : NonUbAt X w) :
    W0Valid P.scale ((X.tr w.1).take (w.2 + 1)) := h hw w.2 le_rfl (Or.inl rfl) hn

/-- **The run step**: the prefix before the run and a step for each run element at `w` give
the claim at `w`. `hpre` is the validity of the prefix of the lane before the run start,
`hstep` the step of an element `j` of the run from `s` through `m`. -/
theorem W0Run.of_step {L : Launch} {m : Mem0}
    (hX : Consistent L kernel Assumptions.all m X) {g k : Nat} (hk : k < (X.tr g).length)
    (hpre : ∀ s, s ≤ k → (s = k ∨ SameAccess X (g, s) (g, k)) →
      (∀ j, j < s → ¬ SameAccess X (g, j) (g, k)) → W0Valid P.scale ((X.tr g).take s))
    (hstep : ∀ s m j, s ≤ k → (s = k ∨ SameAccess X (g, s) (g, k)) → k ≤ m →
      (m = k ∨ SameAccess X (g, k) (g, m)) → RunIn X g s m j → NonUbAt X (g, j) →
      W0Valid P.scale ((X.tr g).take j) → W0Valid P.scale ((X.tr g).take (j + 1))) :
    W0Run P L X (g, k) := by
  intro _ m hkm hm hnm
  have hml : m < (X.tr g).length := by
    rcases hm with rfl | hm
    · exact hk
    · obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind hm.1)
      exact (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s, hsk, hs, hmin⟩ := runStart X g k
  have hsm : SameAccess X (g, s) (g, m) ∨ s = m := by
    rcases hm with rfl | hm
    · rcases hs with rfl | hs
      · exact Or.inr rfl
      · exact Or.inl hs
    · rcases hs with rfl | hs
      · exact Or.inl hm
      · exact Or.inl (sameAccess_trans hs hm hsk hkm)
  have hall : ∀ t, s ≤ t → t ≤ m → W0Valid P.scale ((X.tr g).take (t + 1)) := by
    intro t hst htm
    induction t, hst using Nat.le_induction with
    | base =>
      refine hstep s m s hsk hs hkm hm ⟨le_rfl, by omega, Or.inl rfl⟩ ?_ (hpre s hsk hs hmin)
      intro e he f
      rcases Nat.lt_or_ge s m with h | h
      · exact noUb_kind_of_lt hX he h hml f
      · obtain rfl : s = m := by omega
        exact hnm e he f
    | succ t hst ih =>
      have ht : W0Valid P.scale ((X.tr g).take (t + 1)) := ih (by omega)
      refine hstep s m (t + 1) hsk hs hkm hm ⟨by omega, htm, Or.inr ?_⟩ ?_ ht
      · rcases hsm with h | rfl
        · exact sameAccess_mid h (by omega) htm
        · omega
      · intro e he f
        rcases Nat.lt_or_ge (t + 1) m with h | h
        · exact noUb_kind_of_lt hX he h hml f
        · obtain rfl : t + 1 = m := by omega
          exact hnm e he f
  exact hall m (by omega) le_rfl

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow MbarRow

noncomputable section

variable {X : Execution}

/-- The first element of a run has an access. -/
theorem shift_zero_aux (x : Acc) : Acc.shift 0 x = x := by
  obtain ⟨⟨a, b⟩, sz, ac, rl, sc, el, rx⟩ := x
  simp [Acc.shift, Loc.at]

theorem sameAccess_first {g s m : Nat} (h : SameAccess X (g, s) (g, m)) (hsm : s ≤ m) :
    ((X.get (g, s)).bind Event.acc).isSome := by
  have := h.2 (m - s) (by simp only; omega)
  rw [show s + (m - s) = m by omega] at this
  cases ha : (X.get (g, s)).bind Event.acc with
  | none =>
    rw [ha] at this
    have h1 := h.1
    simp only [this, Option.map_none] at h1
    simp at h1
  | some a => simp

/-- Every event of a run has an access. -/
theorem sameAccess_acc {g s m j : Nat} (h : SameAccess X (g, s) (g, m)) (h1 : s ≤ j)
    (h2 : j ≤ m) : ((X.get (g, j)).bind Event.acc).isSome := by
  have hs := sameAccess_first h (by omega)
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
  have := h.2 (j - s) (by simp only; omega)
  rw [show s + (j - s) = j by omega, ha] at this
  simp only [Option.map_some] at this
  rw [this]; rfl

/-- **The elements of a run are consecutive accesses.** -/
theorem sameAccess_adj {g s m j : Nat} (h : SameAccess X (g, s) (g, m)) (h1 : s ≤ j)
    (h2 : j < m) : SameAccess X (g, j) (g, j + 1) := by
  have hs := sameAccess_first h (by omega)
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
  have e1 := h.2 (j - s) (by simp only; omega)
  have e2 := h.2 (j + 1 - s) (by simp only; omega)
  rw [show s + (j - s) = j by omega, ha] at e1
  rw [show s + (j + 1 - s) = j + 1 by omega, ha] at e2
  refine ⟨by simp [e2], fun d hd => ?_⟩
  simp only at hd ⊢
  rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
  · have hz : Acc.shift 0 = id := funext shift_zero_aux
    cases (X.get (g, j)) <;> simp [hz]
  · rw [e1, e2]
    simp only [Option.map_some, Option.some.injEq]
    rw [show j + 1 - s = (j - s) + 1 by omega]
    simp [Acc.shift_shift]

/-- The pcs at which a clause lemma of warpgroup 0's trace is needed. -/
theorem w0Quiet_or (f : Event) : W0Quiet f ∨ f.pc = 103 ∨ f.pc = 156 ∨ f.pc = 200 ∨
    f.pc = 1122 ∨ f.pc = 278 ∨ f.pc = 280 ∨ f.pc = 283 ∨ f.pc = 285 ∨ f.pc = 289 ∨
    f.pc = 572 ∨ f.pc = 578 ∨ f.pc = 1157 ∨ (∃ k0, k0 < 8 ∧ f.pc = 477 + 5 * k0) ∨
    f.pc ∈ w0OPcs := by
  by_cases h1 : f.pc = 103; · exact Or.inr (Or.inl h1)
  by_cases h2 : f.pc = 156; · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : f.pc = 200; · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  by_cases h4 : f.pc = 1122; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  by_cases h5 : f.pc = 278; · simp [h5]
  by_cases h6 : f.pc = 280; · simp [h6]
  by_cases h7 : f.pc = 283; · simp [h7]
  by_cases h8 : f.pc = 285; · simp [h8]
  by_cases h9 : f.pc = 289; · simp [h9]
  by_cases h10 : f.pc = 572; · simp [h10]
  by_cases h11 : f.pc = 578; · simp [h11]
  by_cases h12 : f.pc = 1157; · simp [h12]
  by_cases h13 : ∃ k0, k0 < 8 ∧ f.pc = 477 + 5 * k0
  · simp [h13]
  by_cases h14 : f.pc ∈ w0OPcs
  · simp [h14]
  refine Or.inl ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨h12, h14⟩, ?_⟩
  · exact ⟨h4, h3⟩
  · exact ⟨h6, h7⟩
  · exact ⟨h5, h8⟩
  · exact h9
  · exact h10
  · exact h11
  · exact fun k hk hq => h13 ⟨k, hk, hq⟩
  · exact ⟨h1, h2⟩

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
