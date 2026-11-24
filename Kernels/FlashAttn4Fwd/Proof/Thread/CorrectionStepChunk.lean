-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionRldW0a
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionRldW0b
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionRldW1a
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionRldW1b
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionFldW0a
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionFldW0b
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionFldW1a
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionFldW1b

@[expose] public section

/-! # After the implicit wait of a load

From the state one instruction past a load's implicit `tcgen05.wait::ld`, at its first sub-step
with the facts of the wait's state, the chunk's products reach the chunk's store
(`tcgen05.st` of the rescale, the first `st.shared.v4` of the final part) when the chunk is
accepted (`next` continues), and the thread is dead otherwise (`next` stops). The rescale's
`α` word has four bytes because the vote's comparison read it (the invariant's `alpha`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

theorem rldW_cont {L : Launch} {g : Nat} {st : Fin 2} {j : Fin 8} {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {e : Event} {u : TState} {n : Nat}
    (hi : Inv L g ⟨.rldW st j, i, tt, aw, a, o⟩)
    (h : (chunkOk o (joinValue aw aw) = true → ∃ t', run kernel asms L g n u = some t' ∧
       At t' (Site.rst st j).pc (facts L g ⟨.rst st j, i, tt, aw, a, o⟩)) ∧
      (chunkOk o (joinValue aw aw) = false →
        Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)) :
    Step asms L g ⟨.rldW st j, i, tt, aw, a, o⟩ e u := by
  have hb : aw.bytes = 4 := by
    obtain ⟨b, hb⟩ := hi.alpha rfl
    exact setpE_bytes (Or.inl rfl) hb
  cases hok : chunkOk o (joinValue aw aw) with
  | true =>
    exact step_of_run (d' := ⟨.rst st j, i, tt, aw, a, o⟩)
      (by simp only [next, rcPair, hb, hok, and_self, ↓reduceIte])
      ⟨fun _ => hi.item rfl, fun h' => by simp [Site.inItem] at h', fun h' => by simp at h',
        fun _ => hi.trip rfl, fun _ => hi.alpha rfl⟩ rfl ⟨n, h.1 hok⟩
  | false =>
    exact .inr ⟨by simp only [next, rcPair, hok, Bool.false_eq_true, and_false, ↓reduceIte],
      h.2 hok⟩

theorem fldW_cont {L : Launch} {g : Nat} {st : Fin 2} {j : Fin 8} {i tt : Nat} {aw : Value}
    {a : ℝ} {o : List Value} {e : Event} {u : TState} {n : Nat}
    (hi : Inv L g ⟨.fldW st j, i, tt, aw, a, o⟩)
    (h : (finOk o (fcPair ⟨.fldW st j, i, tt, aw, a, o⟩) = true →
        ∃ t', run kernel asms L g n u = some t' ∧
       At t' (Site.fst st j 0 0).pc (facts L g ⟨.fst st j 0 0, i, tt, aw, a, o⟩)) ∧
      (finOk o (fcPair ⟨.fldW st j, i, tt, aw, a, o⟩) = false →
        Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)) :
    Step asms L g ⟨.fldW st j, i, tt, aw, a, o⟩ e u := by
  cases hok : finOk o (fcPair ⟨.fldW st j, i, tt, aw, a, o⟩) with
  | true =>
    exact step_of_run (d' := ⟨.fst st j 0 0, i, tt, aw, a, o⟩)
      (by simp only [next, hok, ↓reduceIte])
      ⟨fun _ => hi.item rfl, fun h' => by simp [Site.inItem] at h', fun h' => by simp at h',
        fun h' => by simp [Site.inTrip] at h', fun h' => by simp [Site.rescale] at h'⟩ rfl
      ⟨n, h.1 hok⟩
  | false =>
    exact .inr ⟨by simp only [next, hok, Bool.false_eq_true, ↓reduceIte], h.2 hok⟩

/-- **The rescale chunk after its wait**: from the state past the implicit wait. -/
theorem rldW_step {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    {d : D} {e : Event} {u : TState} (st : Fin 2) (j : Fin 8) (hs : d.site = .rldW st j)
    (hi : Inv L g d) (hu : At u ((Site.rldW st j).pc + 1) (facts L g d)) :
    Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs hu hi ⊢
  subst hs
  have hb : aw.bytes = 4 := by
    obtain ⟨b, hb⟩ := hi.alpha rfl
    exact setpE_bytes (Or.inl rfl) hb
  fin_cases st <;> fin_cases j
  · exact rldW_cont hi (rldW_run_0_0 hpre hb hu)
  · exact rldW_cont hi (rldW_run_0_1 hpre hu)
  · exact rldW_cont hi (rldW_run_0_2 hpre hu)
  · exact rldW_cont hi (rldW_run_0_3 hpre hu)
  · exact rldW_cont hi (rldW_run_0_4 hpre hu)
  · exact rldW_cont hi (rldW_run_0_5 hpre hu)
  · exact rldW_cont hi (rldW_run_0_6 hpre hu)
  · exact rldW_cont hi (rldW_run_0_7 hpre hu)
  · exact rldW_cont hi (rldW_run_1_0 hpre hb hu)
  · exact rldW_cont hi (rldW_run_1_1 hpre hu)
  · exact rldW_cont hi (rldW_run_1_2 hpre hu)
  · exact rldW_cont hi (rldW_run_1_3 hpre hu)
  · exact rldW_cont hi (rldW_run_1_4 hpre hu)
  · exact rldW_cont hi (rldW_run_1_5 hpre hu)
  · exact rldW_cont hi (rldW_run_1_6 hpre hu)
  · exact rldW_cont hi (rldW_run_1_7 hpre hu)

/-- **The final chunk after its wait**: from the state past the implicit wait. -/
theorem fldW_step {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    {d : D} {e : Event} {u : TState} (st : Fin 2) (j : Fin 8) (hs : d.site = .fldW st j)
    (hi : Inv L g d) (hu : At u ((Site.fldW st j).pc + 1) (facts L g d)) :
    Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs hu hi ⊢
  subst hs
  fin_cases st <;> fin_cases j
  · exact fldW_cont hi (fldW_run_0_0 hpre hu)
  · exact fldW_cont hi (fldW_run_0_1 hpre hu)
  · exact fldW_cont hi (fldW_run_0_2 hpre hu)
  · exact fldW_cont hi (fldW_run_0_3 hpre hu)
  · exact fldW_cont hi (fldW_run_0_4 hpre hu)
  · exact fldW_cont hi (fldW_run_0_5 hpre hu)
  · exact fldW_cont hi (fldW_run_0_6 hpre hu)
  · exact fldW_cont hi (fldW_run_0_7 hpre hu)
  · exact fldW_cont hi (fldW_run_1_0 hpre hu)
  · exact fldW_cont hi (fldW_run_1_1 hpre hu)
  · exact fldW_cont hi (fldW_run_1_2 hpre hu)
  · exact fldW_cont hi (fldW_run_1_3 hpre hu)
  · exact fldW_cont hi (fldW_run_1_4 hpre hu)
  · exact fldW_cont hi (fldW_run_1_5 hpre hu)
  · exact fldW_cont hi (fldW_run_1_6 hpre hu)
  · exact fldW_cont hi (fldW_run_1_7 hpre hu)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
