-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Values
public import Lemmas.Tcgen05.MemFloat

@[expose] public section

/-! # The output of a complete execution

In a complete execution thread 0 of CTA `c` has exited after its output store, its event 259,
which writes the sum of the 256 cells it read; each read returns its cell's input, so the store
writes `S x c 256` (`out_write`). It is the only write of `B[c]`, and no write touches global
memory outside `B` (`result`). -/

namespace PTX.Kernels.BlockSum.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B : Nat} {x : Nat → ℝ} {mem0 : Mem0} {X : Execution}

/-- **Thread 0 of each CTA stores the CTA's input sum.** -/
theorem out_write (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) (hcomplete : Complete L X) {c : Nat}
    (hc : c < L.grid) :
    X.get (256 * c, 259) = some ⟨Flow.store_1,
      .wr { loc := gl (B + 4 * c), size := 4 } (fl (S x c 256)).toBytes⟩ := by
  have hg : 256 * c < L.threads := by simp only [Launch.threads, hpre.block]; omega
  have hz : 256 * c % 256 = 0 := by omega
  have hdiv : 256 * c / 256 = c := by omega
  obtain ⟨pcx, hlast⟩ := ((noTma_of_consistent noTma hX).complete_iff L hX.clc).mp hcomplete _ hg
  have hlen0 : 0 < (X.tr (256 * c)).length := by
    rcases h : X.tr (256 * c) with _ | ⟨e, es⟩
    · rw [h] at hlast; cases hlast
    · simp
  have hx : X.get (256 * c, (X.tr (256 * c)).length - 1) = some ⟨pcx, .exit⟩ := by
    unfold Execution.get
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  obtain ⟨-, dx, hσx, hevx, hkx, -⟩ := event_facts hpre hX ht hx (by intro _ _ h; cases h)
  have hsx : dx.site = .exit := by
    obtain ⟨s, v, i, acc, sm⟩ := dx
    cases s <;> simp only [SiteEvent] at hevx
    all_goals first | rfl | (obtain ⟨_, h⟩ := hevx; cases h) | cases hevx
  simp only [D.idx, hsx, hz, ↓reduceIte] at hkx
  -- event 259
  obtain ⟨d, hσ⟩ := followed_before hpre hX ht hx (by intro _ _ h; cases h) (show 259 ≤ _ by omega)
  obtain ⟨e, he⟩ : ∃ e, X.get (256 * c, 259) = some e :=
    ⟨_, List.getElem?_eq_getElem (show 259 < (X.tr (256 * c)).length by omega)⟩
  have hev := ht.event hg he hσ
  have hk := ht.index hg (len_of_get he).le hσ
  have hi := ht.inv hg hσ
  obtain ⟨s, v, i, acc, sm⟩ := d
  cases s with
  | input => simp only [D.idx] at hk; omega
  | share => simp only [D.idx] at hk; omega
  | bar => simp only [D.idx] at hk; omega
  | sum => have := (hi.sum rfl).1; simp only [D.idx] at hk this; omega
  | exit => simp only [D.idx, hz, ↓reduceIte] at hk; omega
  | out =>
    simp only [SiteEvent] at hev
    have hsum := ht.sum hg hσ (.inr rfl)
    have h256 := (hi.out rfl).2
    simp only at hsum h256
    rw [h256] at hsum
    have hS : ∑ j ∈ Finset.range 256, rdVal (X.get (256 * c, 3 + j)) =
        ((S x c 256 : ℝ) : EReal) := by
      rw [show ((S x c 256 : ℝ) : EReal) =
        ∑ j ∈ Finset.range 256, ((x (256 * c + j) : ℝ) : EReal) by
        unfold S
        rw [sum_coe]]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < 256 := Finset.mem_range.mp hj
      obtain ⟨dj, hσj⟩ := followed_before hpre hX ht hx (by intro _ _ h; cases h)
        (show 3 + j ≤ _ by omega)
      obtain ⟨ej, hej⟩ : ∃ e, X.get (256 * c, 3 + j) = some e :=
        ⟨_, List.getElem?_eq_getElem (show 3 + j < (X.tr (256 * c)).length by omega)⟩
      have hevj := ht.event hg hej hσj
      have hkj := ht.index hg (len_of_get hej).le hσj
      obtain ⟨sj, vj, ij, accj, smj⟩ := dj
      cases sj with
      | input => simp only [D.idx] at hkj; omega
      | share => simp only [D.idx] at hkj; omega
      | bar => simp only [D.idx] at hkj; omega
      | out => simp only [D.idx] at hkj; omega
      | exit => simp only [D.idx, hz, ↓reduceIte] at hkj; omega
      | sum =>
        simp only [SiteEvent] at hevj
        obtain ⟨bs, rfl⟩ := hevj
        simp only [D.idx] at hkj
        obtain rfl : ij = j := by omega
        have hb := shared_read hpre hX ht hj' rfl hej
        rw [hej, hb]
        simp [rdVal, readVal_bytesOf, hdiv]
    have hs : sm = ((S x c 256 : ℝ) : EReal) := by rw [hsum, hS]
    rw [he, hev, hs, erealValue_coe_value, hdiv]
    rfl

/-- **The output of a complete execution.** -/
theorem result (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) (hcomplete : Complete L X)
    {m : FinalMem} (hfin : IsFinal L mem0 X m) : Post L B x mem0 m := by
  have hn := noTma_of_consistent noTma hX
  have hbyte : ∀ c < L.grid, ∀ k < 4,
      m ((gl (B + 4 * c)).at k) = some (some (fl (S x c 256), k)) := by
    intro c hc k hk
    have hwr : X.Writes (256 * c, 259) { loc := gl (B + 4 * c), size := 4 }
        (fl (S x c 256)).toBytes := ⟨_, out_write hpre hX ht hcomplete hc⟩
    have hw : X.MemWrites (.thread (256 * c, 259)) { loc := gl (B + 4 * c), size := 4 }
        (fl (S x c 256)).toBytes := .inl hwr
    have hcov : Acc.Covers { loc := gl (B + 4 * c), size := 4 } ((gl (B + 4 * c)).at k) :=
      Acc.covers_at (a := { loc := gl (B + 4 * c), size := 4 }) hk
    rw [hfin.unique hw hcov fun w' a' bs' hw' hc' => by
      rcases Execution.NoTma.memWrites_thread (hn.emptyAsync hX) hw' with ⟨w', rfl, hwT⟩
      cases hwT with
      | inl hwT =>
        have ha := overlapping_access_eq hpre hX ht (.inr (.inl ⟨_, hwT, rfl⟩))
          (.inr (.inl ⟨_, hwr, rfl⟩)) ⟨_, hc', hcov⟩
        subst ha
        exact congrArg AsyncCopy.Ref.thread (writes_unique hpre hX ht hwT hwr)
      | inr hrmw => obtain ⟨old, hrmw⟩ := hrmw; exact absurd hrmw (no_rmw hpre hX)]
    have hfl : (fl (S x c 256)).toBytes[k]? = some (fl (S x c 256), k) := PTX.Proof.fl_byte _ hk
    simp only [wbyte, gl, Loc.at, Nat.add_sub_cancel_left, hfl]
  refine ⟨fun c hc => memFloat_float fun k hk => hbyte c hc k hk, fun l hglobal hl => ?_⟩
  apply hfin.unwritten
  intro w a bs hw hcov
  obtain ⟨⟨g, k⟩, rfl, hwT | ⟨old, hrmw⟩⟩ := Execution.NoTma.memWrites_thread (hn.emptyAsync hX) hw
  · obtain ⟨pcw, hwT⟩ := hwT
    have hg := Frame.lt_of_get hX hwT
    rcases write_cases hpre hX ht hwT with ⟨-, rfl, -⟩ | ⟨-, -, rfl, -⟩
    · have hh := hcov.1; rw [hglobal] at hh; cases hh
    · have hcg : g / 256 < L.grid := by simp only [Launch.threads, hpre.block] at hg; omega
      obtain ⟨-, hcta, hlo, hhi⟩ := hcov
      exact hl ⟨hcta, by dsimp [gl] at hlo; omega, by dsimp [gl] at hhi; omega⟩
  · exact absurd hrmw (no_rmw hpre hX)

end
end PTX.Kernels.BlockSum.Proof
