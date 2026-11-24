-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Interface

@[expose] public section

/-! # The invariant and the event kind along a step

The transition function keeps the state invariant (`runFacts_step`): it moves to the next element of
a vector access or to the next site with the element counter reset, enters a row only while the
batch has one, and keeps the loaded raw values of the four elements. The event of a site is a
read, a write, a shuffle, a barrier or the exit by the site (`site_event`). -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {g : Nat}

theorem loadNext_some {d d' : D} {e : Event} {k : List Value → Option D}
    (h : loadNext d e k = some (some d')) :
    (d.sub + 1 < 4 ∧ ∃ v, d' = { d with sub := d.sub + 1, acc := d.acc ++ [v] }) ∨
      (¬ d.sub + 1 < 4 ∧ ∃ v, k (d.acc ++ [v]) = some d') := by
  unfold loadNext at h
  split at h
  · split at h
    · rename_i v _
      split_ifs at h with hs
      · exact .inl ⟨hs, v, (Option.some.inj (Option.some.inj h)).symm⟩
      · obtain ⟨d'', hk, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        exact .inr ⟨hs, v, hk⟩
    · cases h
  · cases h

theorem storeNext_some {d d' d'' : D} (h : storeNext d d'' = some (some d')) :
    (d.sub + 1 < 4 ∧ d' = { d with sub := d.sub + 1 }) ∨ (¬ d.sub + 1 < 4 ∧ d' = d'') := by
  unfold storeNext at h
  split_ifs at h with hs
  · exact .inl ⟨hs, (Option.some.inj (Option.some.inj h)).symm⟩
  · exact .inr ⟨hs, (Option.some.inj (Option.some.inj h)).symm⟩

end
end PTX.Kernels.RmsNorm.Proof

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {g : Nat}

theorem get_snoc {pre : List Event} {e : Event} {q : Nat} (h : q < pre.length) :
    (pre ++ [e])[q]? = pre[q]? := List.getElem?_append_left h

theorem get_last {pre : List Event} {e : Event} {q : Nat} (h : q = pre.length) :
    (pre ++ [e])[q]? = some e := by
  subst h; simp

theorem rv4_snoc {pre : List Event} {e : Event} {p : Nat} (h : p + 4 ≤ pre.length) :
    rv4 (pre ++ [e]) p = rv4 pre p := by
  simp only [rv4, get_snoc (show p < pre.length by omega),
    get_snoc (show p + 1 < pre.length by omega),
    get_snoc (show p + 2 < pre.length by omega), get_snoc (show p + 3 < pre.length by omega)]

/-- The values of a vector load after its element `j`. -/
theorem rv4_take_snoc {pre : List Event} {e : Event} {p j : Nat} (hj : j < 4)
    (h : pre.length = p + j) :
    (rv4 (pre ++ [e]) p).take (j + 1) = (rv4 pre p).take j ++ [rdv (some e)] := by
  interval_cases j <;>
    simp [rv4, h]


/-! ### The data of a row along steps that keep a datum -/

section keep
variable {d d' : D} {pre : List Event} {e : Event}
  (hD : RowData P g d pre)
  (hlen : d.site.inRow = true → pre.length = rowBase g d.i + d.pos g) (hi : d'.i = d.i)
include hD hlen hi

theorem keep_xa (hF : d'.xa = d.xa)
    (hc : d'.site.inRow = true → 4 ≤ d'.pos g → d.site.inRow = true ∧ 4 ≤ d.pos g) :
    d'.site.inRow = true → 4 ≤ d'.pos g → d'.xa = rv4 (pre ++ [e]) (rowBase g d'.i) := by
  intro h1 h2
  obtain ⟨h1', h2'⟩ := hc h1 h2
  rw [hF, hi, rv4_snoc (by have := hlen h1'; omega)]
  exact hD.xa h1' h2'

theorem keep_xb (hF : d'.xb = d.xb)
    (hc : d'.site.inRow = true → 16 ≤ d'.pos g → d.site.inRow = true ∧ 16 ≤ d.pos g) :
    d'.site.inRow = true → 16 ≤ d'.pos g →
      d'.xb = rv4 (pre ++ [e]) (rowBase g d'.i + 12) := by
  intro h1 h2
  obtain ⟨h1', h2'⟩ := hc h1 h2
  rw [hF, hi, rv4_snoc (by have := hlen h1'; omega)]
  exact hD.xb h1' h2'

theorem keep_ra (hF : ∀ k, 24 + k < d'.pos g → d'.ra k = d.ra k)
    (hc : ∀ k < 5, d'.site.inRow = true → 24 + k < d'.pos g →
      d.site.inRow = true ∧ 24 + k < d.pos g) :
    d'.site.inRow = true → ∀ k < 5, 24 + k < d'.pos g →
      d'.ra k = recvOf (pre ++ [e])[rowBase g d'.i + 24 + k]? := by
  intro h1 k hk h2
  obtain ⟨h1', h2'⟩ := hc k hk h1 h2
  rw [hF k h2, hi, get_snoc (by have := hlen h1'; omega)]
  exact hD.ra h1' k hk h2'

theorem keep_u (hF : d'.u = d.u)
    (hc : d'.site.inRow = true → g % 256 < 32 → 30 + l0 g + l8 g ≤ d'.pos g →
      d.site.inRow = true ∧ 30 + l0 g + l8 g ≤ d.pos g) :
    d'.site.inRow = true → g % 256 < 32 → 30 + l0 g + l8 g ≤ d'.pos g →
      d'.u = if g % 256 < 8 then rdv (pre ++ [e])[rowBase g d'.i + 30 + l0 g]? else b32 0 := by
  intro h1 hw h2
  obtain ⟨h1', h2'⟩ := hc h1 hw h2
  have hl := hlen h1'
  have hu := hD.u h1' hw h2'
  rw [hF, hi]
  by_cases h8 : g % 256 < 8
  · have : l8 g = 1 := by simp [l8, h8]
    simp only [h8, ↓reduceIte] at hu ⊢
    rw [get_snoc (by omega)]
    exact hu
  · simp only [h8, ↓reduceIte] at hu ⊢
    exact hu

theorem keep_rb (hF : ∀ k, 30 + l0 g + l8 g + k < d'.pos g → d'.rb k = d.rb k)
    (hc : ∀ k < 5, d'.site.inRow = true → g % 256 < 32 → 30 + l0 g + l8 g + k < d'.pos g →
      d.site.inRow = true ∧ 30 + l0 g + l8 g + k < d.pos g) :
    d'.site.inRow = true → g % 256 < 32 → ∀ k < 5, 30 + l0 g + l8 g + k < d'.pos g →
      d'.rb k = recvOf (pre ++ [e])[rowBase g d'.i + 30 + l0 g + l8 g + k]? := by
  intro h1 hw k hk h2
  obtain ⟨h1', h2'⟩ := hc k hk h1 hw h2
  rw [hF k h2, hi, get_snoc (by have := hlen h1'; omega)]
  exact hD.rb h1' hw k hk h2'

theorem keep_tt (hF : d'.tt = d.tt)
    (hc : d'.site.inRow = true → p1 g + 1 < d'.pos g → d.site.inRow = true ∧ p1 g + 1 < d.pos g) :
    d'.site.inRow = true → p1 g + 1 < d'.pos g →
      d'.tt = rdv (pre ++ [e])[rowBase g d'.i + p1 g + 1]? := by
  intro h1 h2
  obtain ⟨h1', h2'⟩ := hc h1 h2
  rw [hF, hi, get_snoc (by have := hlen h1'; omega)]
  exact hD.tt h1' h2'

theorem keep_rawa (hF : d'.raw = d.raw)
    (hc : d'.site.inRow = true → p1 g + 6 ≤ d'.pos g → d'.pos g < p1 g + 18 →
      d.site.inRow = true ∧ p1 g + 6 ≤ d.pos g ∧ d.pos g < p1 g + 18) :
    d'.site.inRow = true → p1 g + 6 ≤ d'.pos g → d'.pos g < p1 g + 18 →
      d'.raw = rv4 (pre ++ [e]) (rowBase g d'.i + p1 g + 2) := by
  intro h1 h2 h3
  obtain ⟨h1', h2', h3'⟩ := hc h1 h2 h3
  rw [hF, hi, rv4_snoc (by have := hlen h1'; omega)]
  exact hD.rawa h1' h2' h3'

theorem keep_rawb (hF : d'.raw = d.raw)
    (hc : d'.site.inRow = true → p1 g + 22 ≤ d'.pos g → d.site.inRow = true ∧ p1 g + 22 ≤ d.pos g) :
    d'.site.inRow = true → p1 g + 22 ≤ d'.pos g →
      d'.raw = rv4 (pre ++ [e]) (rowBase g d'.i + p1 g + 18) := by
  intro h1 h2
  obtain ⟨h1', h2'⟩ := hc h1 h2
  rw [hF, hi, rv4_snoc (by have := hlen h1'; omega)]
  exact hD.rawb h1' h2'

theorem keep_rs0a (hF : d'.rs0 = d.rs0)
    (hc : d'.site.inRow = true → p1 g + 10 ≤ d'.pos g → d'.pos g < p1 g + 26 →
      d.site.inRow = true ∧ p1 g + 10 ≤ d.pos g ∧ d.pos g < p1 g + 26) :
    d'.site.inRow = true → p1 g + 10 ≤ d'.pos g → d'.pos g < p1 g + 26 →
      d'.rs0 = rv4 (pre ++ [e]) (rowBase g d'.i + p1 g + 6) := by
  intro h1 h2 h3
  obtain ⟨h1', h2', h3'⟩ := hc h1 h2 h3
  rw [hF, hi, rv4_snoc (by have := hlen h1'; omega)]
  exact hD.rs0a h1' h2' h3'

theorem keep_rs0b (hF : d'.rs0 = d.rs0)
    (hc : d'.site.inRow = true → p1 g + 26 ≤ d'.pos g → d.site.inRow = true ∧ p1 g + 26 ≤ d.pos g) :
    d'.site.inRow = true → p1 g + 26 ≤ d'.pos g →
      d'.rs0 = rv4 (pre ++ [e]) (rowBase g d'.i + p1 g + 22) := by
  intro h1 h2
  obtain ⟨h1', h2'⟩ := hc h1 h2
  rw [hF, hi, rv4_snoc (by have := hlen h1'; omega)]
  exact hD.rs0b h1' h2'

theorem keep_rs1a (hF : d'.rs1 = d.rs1)
    (hc : d'.site.inRow = true → p1 g + 14 ≤ d'.pos g → d'.pos g < p1 g + 18 →
      d.site.inRow = true ∧ p1 g + 14 ≤ d.pos g ∧ d.pos g < p1 g + 18) :
    d'.site.inRow = true → p1 g + 14 ≤ d'.pos g → d'.pos g < p1 g + 18 →
      d'.rs1 = rv4 (pre ++ [e]) (rowBase g d'.i + p1 g + 10) := by
  intro h1 h2 h3
  obtain ⟨h1', h2', h3'⟩ := hc h1 h2 h3
  rw [hF, hi, rv4_snoc (by have := hlen h1'; omega)]
  exact hD.rs1a h1' h2' h3'

theorem keep_rs1b (hF : d'.rs1 = d.rs1)
    (hc : d'.site.inRow = true → p1 g + 30 ≤ d'.pos g → d.site.inRow = true ∧ p1 g + 30 ≤ d.pos g) :
    d'.site.inRow = true → p1 g + 30 ≤ d'.pos g →
      d'.rs1 = rv4 (pre ++ [e]) (rowBase g d'.i + p1 g + 26) := by
  intro h1 h2
  obtain ⟨h1', h2'⟩ := hc h1 h2
  rw [hF, hi, rv4_snoc (by have := hlen h1'; omega)]
  exact hD.rs1b h1' h2'

end keep


theorem rdv_rd {pc : Nat} {a : Acc} {bs : List (Option Byte)} {v : Value}
    (h : rebuild 3 bs = .ok v) : rdv (some ⟨pc, .rd a bs⟩) = v := by
  simp [rdv, h]

theorem loadNext_rd {d d' : D} {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    {k : List Value → Option D} (h : loadNext d ⟨pc, .rd a bs⟩ k = some (some d')) :
    ∃ v, rebuild 3 bs = .ok v ∧
      ((d.sub + 1 < 4 ∧ d' = { d with sub := d.sub + 1, acc := d.acc ++ [v] }) ∨
        (¬ d.sub + 1 < 4 ∧ k (d.acc ++ [v]) = some d')) := by
  simp only [loadNext] at h
  cases hb : rebuild 3 bs with
  | error f => rw [hb] at h; cases h
  | ok v =>
    rw [hb] at h
    refine ⟨v, rfl, ?_⟩
    split_ifs at h with hs
    · exact .inl ⟨hs, (Option.some.inj (Option.some.inj h)).symm⟩
    · obtain ⟨d'', hk, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact .inr ⟨hs, hk⟩

/-- The values a vector load holds after an element before the last. -/
theorem acc_mid {d : D} {pre : List Event} {e : Event} {p0 : Nat} {v : Value}
    (hD0 : d.acc = (rv4 pre p0).take d.sub) (hlen : pre.length = p0 + d.sub) (hsub : d.sub < 4)
    (hv : rdv (some e) = v) : d.acc ++ [v] = (rv4 (pre ++ [e]) p0).take (d.sub + 1) := by
  rw [rv4_take_snoc hsub hlen, hD0, hv]

/-- The values a vector load holds after its last element. -/
theorem acc_last {d : D} {pre : List Event} {e : Event} {p0 : Nat} {v : Value}
    (hD0 : d.acc = (rv4 pre p0).take d.sub) (hlen : pre.length = p0 + d.sub) (h3 : d.sub = 3)
    (hv : rdv (some e) = v) : d.acc ++ [v] = rv4 (pre ++ [e]) p0 := by
  rw [acc_mid hD0 hlen (by omega) hv, h3]
  rfl

end
end PTX.Kernels.RmsNorm.Proof
