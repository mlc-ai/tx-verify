-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Handoff

@[expose] public section

/-! # A barrier hand-off whose consumers sync only up to the hand-off's ordinal

`Frame.Handoff.of_bar_upTo` asks every consumer to arrive at the barrier only by `bar.sync`, and
every participant that exits to have made `n` arrivals. The consumer's barrier event that the
hand-off uses has an ordinal below the bound `n`, so it is enough that the consumer's barrier
events of ordinals below `n` are syncs (the softmax and correction warps sync at their first
barrier-2 event and arrive without waiting at their last one); and the exit condition is used for
the producer only, so it is asked of the producers `prod` (`of_bar_upTo_ord`). The proof is
`of_bar_upTo`'s. -/

namespace PTX.Frame

open PTX PTX.Flow

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

namespace Handoff

theorem of_bar_upTo_ord (hX : Consistent L K A mem0 X) {count : Option Nat} {p : Finset Nat}
    {id : Nat}
    (hS : NamedBar.Sources L X count p id) (hG : NamedBar.Shape L count p id)
    {syncs prod : Nat → Prop}
    (n : Nat)
    (hsync : ∀ h j pc cnt mode, syncs h → X.get (h, j) = some ⟨pc, .bar id cnt mode⟩ →
      ((X.tr h).take j).countP (Execution.isBarId id) < n → mode = .sync)
    (hexit : ∀ g, g < L.threads → (g % L.block) / 32 ∈ p → prod g →
      (∃ j pc, X.get (g, j) = some ⟨pc, .exit⟩) → n ≤ (X.tr g).countP (Execution.isBarId id)) :
    Handoff L X (fun g h => SameCta L g h ∧ (g % L.block) / 32 ∈ p ∧ syncs h ∧ prod g)
      (fun i => ((X.tr i.1).take (i.2 + 1)).countP (Execution.isBarId id))
      (fun i => min (((X.tr i.1).take i.2).countP (Execution.isBarId id)) n) := by
  rintro g h e f ⟨hsame, hpg, hsh, hpr⟩ hf hlt0
  simp only at hlt0
  have hlt : ((X.tr g).take (e + 1)).countP (Execution.isBarId id) <
      ((X.tr h).take f).countP (Execution.isBarId id) := lt_of_lt_of_le hlt0 (Nat.min_le_left _ _)
  have hltn : ((X.tr g).take (e + 1)).countP (Execution.isBarId id) < n :=
    lt_of_lt_of_le hlt0 (Nat.min_le_right _ _)
  set q := ((X.tr g).take (e + 1)).countP (Execution.isBarId id) with hq
  have hgt : g < L.threads := hsame.1
  have hht : h < L.threads := hsame.2.1
  -- the consumer's barrier of ordinal `q`
  obtain ⟨j, ev, hj, hbj, hcj⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId id)
    (show q + 1 ≤ ((X.tr h).take f).countP (Execution.isBarId id) by omega)
  have hjf : j < f := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hjf.le] at hcj
  have hgetj : X.get (h, j) = some ev := by
    change (X.tr h)[j]? = some ev
    rw [← hj, List.getElem?_take, ite_eq_left hjf]
  obtain ⟨pcj, kj⟩ := ev
  cases kj with
  | bar idj cntj modej =>
    simp only [Execution.isBarId, beq_iff_eq] at hbj
    subst hbj
    have hmj := hsync h j pcj cntj modej hsh hgetj (by omega)
    subst hmj
    have hfb : X.IsBarrier (h, j) idj cntj pcj := hgetj
    have hph : (h % L.block) / 32 ∈ p := (hS.sync hfb hht).1
    -- the producer's arrival of the same ordinal
    obtain ⟨i, pci, mi, hbi, hci⟩ := hS.member_arrival_any hX hG hfb (by simp only; omega)
      (show g / L.block = h / L.block from hsame.2.2) hpg (by
        rintro hex
        have hall := hexit g hgt hpg hpr hex
        have hge : q + 1 ≤ (X.tr g).countP (Execution.isBarId idj) := by omega
        obtain ⟨i, ev', hi, hbi, hci⟩ :=
          MbarRing.Slot.exists_nth_countP (Execution.isBarId idj) hge
        obtain ⟨pci, ki⟩ := ev'
        cases ki with
        | bar idi cnti modei =>
          simp only [Execution.isBarId, beq_iff_eq] at hbi
          subst hbi
          have hcnti := (hS (g, i) pci cnti ⟨modei, hi⟩ hgt).2
          subst hcnti
          exact ⟨i, pci, modei, hi, by simp only; omega⟩
        | _ => simp [Execution.isBarId] at hbi)
    simp only at hci
    have hiq : ((X.tr g).take i).countP (Execution.isBarId idj) = q := hci.trans hcj
    have hei : e < i := by
      by_contra hle
      have h1 := countP_take_succ_ge (P := Execution.isBarId idj) (es := X.tr g) (e := e) hbi
        (by simp [Execution.isBarId]) (by omega)
      rw [hiq, ← hq] at h1
      omega
    exact NamedBar.Sources.arrive_sync_baseCausality hX hS hG hsame hbi hfb (by omega)
      (by omega) hei hjf hf
  | _ => simp [Execution.isBarId] at hbj

end Handoff

end PTX.Frame
