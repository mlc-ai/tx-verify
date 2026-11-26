-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.Trace

@[expose] public section

/-! # Valid data keeps the data machine following

`dataNext_ok`: on valid data (`GoodEv`) the data machine follows wherever the control machine
follows, from a state that holds the invariant `InvD` (`Data/Trace.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Numeric.Dequant

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-! ### Valid data keeps the data machine following -/

/-- A load event of valid data (`DqValid`'s clause). -/
def GoodEv (f : Event) : Prop :=
  (∀ r s, r < 4 → s < 8 → f.pc = dqRawPc r s →
      ∃ x, readWord 64 f = some x ∧ ∀ i < 8, byteAt x i ≠ 127 ∧ byteAt x i ≠ 255) ∧
    (∀ r, r < 4 → f.pc = dqScalePc r → ∃ w, readWord 32 f = some w ∧ ∀ i < 4, byteAt w i < 255)

theorem scOk_of {w0 w1 w2 w3 : Nat} (h0 : w0 < 2 ^ 32) (h1 : w1 < 2 ^ 32)
    (h2 : w2 < 2 ^ 32) (b0 : ∀ i < 4, byteAt w0 i < 255) (b1 : ∀ i < 4, byteAt w1 i < 255)
    (b2 : ∀ i < 4, byteAt w2 i < 255) (b3 : ∀ i < 4, byteAt w3 i < 255) :
    ScOk (scWord w0 w1 w2 w3) := by
  intro i hi
  have hk := Nat.mod_lt i (show 4 > 0 by decide)
  obtain ⟨e0, e1, e2, e3⟩ := byteAt_scWord (w3 := w3) h0 h1 h2 (i % 4) hk
  rcases (by omega : i = i % 4 ∨ i = 4 + i % 4 ∨ i = 4 + (4 + i % 4) ∨
    i = 4 + (4 + (4 + i % 4))) with h | h | h | h <;> rw [h]
  · rw [e0]; exact b0 _ hk
  · rw [e1]; exact b1 _ hk
  · rw [e2]; exact b2 _ hk
  · rw [e3]; exact b3 _ hk

theorem mem_lastN_atPc {l : List Event} {f : Event} {n p : Nat}
    (h : f ∈ lastN n (atPc l p)) : f ∈ l ∧ f.pc = p := by
  have h' := List.mem_of_mem_drop h
  simpa [atPc] using h'

/-- **Valid data keeps the data machine following** where the control machine follows. -/
theorem dataNext_ok {l : List Event} {d : D} {c' : Control.D} {e : Event}
    (hI : InvD l d) (hel : d.c.el < Control.elems d.c.site) (hpc : e.pc = d.c.site.pc)
    (hc : Control.succ P L g d.c e = some (some c')) (hv : ∀ f ∈ l ++ [e], GoodEv f) :
    ∃ d', dataNext d c' e = some d' := by
  rcases hs : d.c.site with _ | _ | _ | _ | _ | _ | r | ⟨r, s⟩ | ⟨r, s⟩ | _ | _ | _ | _ | _
  case scale =>
    rw [hs] at hpc hel
    obtain ⟨a, bs, hk⟩ : ∃ a bs, e.kind = .rd a bs := by
      simp only [Control.succ, hs] at hc
      split at hc
      · exact ⟨_, _, ‹_›⟩
      · cases hc
    simp only [dataNext, hs, hk]
    split
    · exact ⟨_, rfl⟩
    obtain ⟨hle, hacc⟩ := hI.acc r hs
    have h3 : d.c.el = 3 := by simp [Control.elems] at hel; omega
    have hM : ∀ f ∈ lastN 3 (atPc l (dqScalePc r)) ++ [e], ∃ w, wordOf 32 (readVal f) = some w ∧
        w < 2 ^ 32 ∧ ∀ i < 4, byteAt w i < 255 := by
      intro f hf
      have hf' : f ∈ l ++ [e] ∧ f.pc = dqScalePc r := by
        rcases List.mem_append.mp hf with hf | hf
        · obtain ⟨h1, h2⟩ := mem_lastN_atPc hf
          exact ⟨List.mem_append_left _ h1, h2⟩
        · obtain rfl := List.mem_singleton.mp hf
          exact ⟨by simp, hpc.trans (scale_pc r)⟩
      obtain ⟨w, hw, hb⟩ := (hv f hf'.1).2 r r.isLt hf'.2
      rw [readWord_eq] at hw
      exact ⟨w, hw, bitsWord_lt hw, hb⟩
    have hl : (lastN 3 (atPc l (dqScalePc r)) ++ [e]).length = 4 := by
      rw [List.length_append, lastN_length (h3 ▸ hle)]; rfl
    have hacc' : d.c.acc ++ [loadVal bs] =
        (lastN 3 (atPc l (dqScalePc r)) ++ [e]).map readVal := by
      rw [hacc, h3, List.map_append]; simp [readVal, hk]
    rw [hacc']
    generalize lastN 3 (atPc l (dqScalePc r)) ++ [e] = M at hM hl
    rcases M with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | ⟨f4, M⟩⟩⟩⟩⟩ <;> simp at hl
    obtain ⟨w0, hw0, l0, b0⟩ := hM f0 (by simp)
    obtain ⟨w1, hw1, l1, b1⟩ := hM f1 (by simp)
    obtain ⟨w2, hw2, l2, b2⟩ := hM f2 (by simp)
    obtain ⟨w3, hw3, -, b3⟩ := hM f3 (by simp)
    simp only [List.map, scaleOf, hw0, hw1, hw2, hw3, scOk_of l0 l1 l2 b0 b1 b2 b3, ↓reduceDIte,
      Option.map_some]
    exact ⟨_, rfl⟩
  case raw =>
    rw [hs] at hpc
    obtain ⟨a, bs, hk⟩ : ∃ a bs, e.kind = .rd a bs := by
      simp only [Control.succ, hs, Control.dataRd] at hc
      split at hc
      · exact ⟨_, _, ‹_›⟩
      · cases hc
    simp only [dataNext, hs, hk]
    obtain ⟨x, hx, hb⟩ := (hv e (by simp)).1 r s r.isLt s.isLt (hpc.trans (raw_pc r s))
    have hx' : wordOf 64 (loadVal bs) = some x := by
      rw [readWord_eq] at hx; simpa [readVal, hk] using hx
    simp only [rawOf, hx', show WordOk x from ⟨hb, bitsWord_lt hx'⟩,
      ↓reduceDIte, Option.map_some]
    exact ⟨_, rfl⟩
  all_goals simp only [dataNext, hs]
  all_goals exact ⟨_, rfl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
