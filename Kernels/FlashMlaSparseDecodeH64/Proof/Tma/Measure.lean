-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Time

@[expose] public section

/-! # The TMA warp's termination measure

The measure of a state is its place capped at `top` (`measure`, at most `top`). A step the machine
follows from a state with the reference invariant stays (a failed poll) or moves to a later place
(`place_step`): inside a block a step adds one event to the block's place (`Site.idx`), the
block's end moves to the next block's first place or the barrier. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

attribute [local simp] tmaBlk0 endPlace endSlot tmaOrg loopBase tmaOff stride blockCap

/-- **The TMA warp's measure.** -/
def measure (d : D) : Nat := min (place d) top

theorem measure_le (d : D) : measure d ≤ top := Nat.min_le_right _ _

/-- A state off the election is after it. -/
theorem place_pos {d : D} (h : d.site ≠ .elect) : 0 < place d := by
  unfold place
  split
  · simp
  · simp
  · split_ifs
    · simp
    · cases hx : d.site <;> simp only [Site.ord] <;> first | omega | exact absurd hx h

/-- A step inside a block to the next event of the block. -/
theorem place_in {d d' : D} (hd : d.site.inLoop = true) (hd' : d'.site.inLoop = true)
    (hc : d'.cnt = d.cnt) (hi : d'.site.idx = d.site.idx + 1) : place d < place d' := by
  rw [place_loop hd, place_loop hd', hc, hi]
  omega

/-- A poll: the same state at a failed poll (which does not count), or its next site at a later
place. -/
theorem poll_place {d d' d₁ : D} {e : Event} (hlt : place d < place d₁)
    (hn : poll d e d₁ = some (some d')) : (d' = d ∧ e.counts = false) ∨ place d < place d' := by
  obtain ⟨pc, kd⟩ := e
  unfold poll at hn
  split at hn
  next l q ok a sc hk =>
    simp only at hk
    subst hk
    cases ok <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at hn <;> subst hn
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr hlt
  · cases hn

/-- **Every step the machine follows** stays at a failed poll or moves to a later place. -/
theorem place_step {d d' : D} {n : Cnt → Nat} {e : Event} (hJ : RefCore L g d n)
    (hn : succ P L g d e = some (some d')) : (d' = d ∧ e.counts = false) ∨ place d < place d' := by
  have hp0 : ∀ s, d.site = s → ProSite s → place d = s.ord := fun s hs h =>
    by rw [place_pro (hs ▸ h), hs]
  cases hs : d.site with
  | exit | leave _ => simp [succ, hs] at hn
  | elect =>
    simp only [succ, hs, electNext] at hn
    split at hn
    · simp only [Option.some.injEq] at hn
      subst hn
      refine .inr ?_
      rw [hp0 _ hs ⟨rfl, by simp, by simp⟩]
      apply place_pos
      split_ifs
      · simp only [leadNext, afterTopk, lensD]
        split_ifs <;> simp
      · simp
    · cases hn
  | loadTopk | loadExtra =>
    simp only [succ, hs] at hn
    obtain ⟨x, rfl⟩ := word_next hn
    refine .inr ?_
    rw [hp0 _ hs ⟨rfl, by simp, by simp⟩]
    first
    | (simp only [afterTopk, lensD]; split_ifs <;> simp [place, Site.ord, Site.inLoop])
    | simp [lensD, place, Site.ord, Site.inLoop]
  | qWait =>
    simp only [succ, hs] at hn
    refine poll_place ?_ hn
    rw [hp0 _ hs ⟨rfl, by simp, by simp⟩]
    simp [place, Site.ord, Site.inLoop]
  | storeWait =>
    simp only [succ, hs] at hn
    refine poll_place ?_ hn
    rw [hp0 _ hs ⟨rfl, by simp, by simp⟩]
    unfold loopEntry
    split_ifs with h
    · simp [place, Site.ord]
    · have h0 : (i32 0).toNat = 0 := by decide
      simp [place, Site.inLoop, Site.idx, Site.stage, Site.rdN, Site.gN, Site.ord, h0]
  | coordWait =>
    simp only [succ, hs] at hn
    exact poll_place (d₁ := { d with site := .rawWait })
      (place_in (by rw [hs]; rfl) rfl rfl (by rw [hs]; rfl)) hn
  | rawWait =>
    simp only [succ, hs] at hn
    exact poll_place (d₁ := { d with site := .coord0 0 })
      (place_in (by rw [hs]; rfl) rfl rfl (by rw [hs]; rfl)) hn
  | coord0 k | coord1 k | coord2 k | coord3 k =>
    simp only [succ, hs] at hn
    obtain ⟨x, rfl⟩ := rd_next hn
    refine .inr (place_in (by rw [hs]; rfl) ?_ rfl ?_)
    · first | rfl | (show (afterCoord k).inLoop = true; unfold afterCoord; split_ifs <;> rfl)
    · obtain ⟨p1, p2, p3⟩ := coord_places k
      first
      | (simp only [Site.idx, hs, Site.stage, Site.rdN, Site.gN]; omega)
      | (simp only [hs, afterQuad_site]; rw [Site.idx, Site.idx, p1, p2, p3]
         simp only [Site.stage, Site.rdN, Site.gN]; omega)
  | gather k =>
    simp only [succ, hs, Option.some.injEq] at hn
    subst hn
    obtain ⟨p1, p2, p3⟩ := gather_places k
    refine .inr (place_in (by rw [hs]; rfl) ?_ rfl ?_)
    · show (afterGather k).inLoop = true
      unfold afterGather; split_ifs <;> rfl
    · simp only [hs]
      rw [Site.idx, Site.idx, p1, p2, p3]
      simp only [Site.stage, Site.gN]
      omega
  | rawArrive =>
    simp only [succ, hs, Option.some.injEq] at hn
    subst hn
    exact .inr (place_in (by rw [hs]; rfl) rfl rfl (by rw [hs]; rfl))
  | outBar =>
    simp only [succ, hs, Option.some.injEq] at hn
    subst hn
    refine .inr ?_
    unfold place
    simp [hs]
  | coordFree =>
    simp only [succ, hs, Option.some.injEq] at hn
    subst hn
    refine .inr ?_
    have hd : d.site.inLoop = true := by rw [hs]; rfl
    obtain ⟨⟨-, -, hR, hr, hcnt, hbuf, hslot, hpf, hpr, hneg⟩, -⟩ := (core_loop hd).1 hJ
    obtain ⟨e1, -, -, -, -, -, e7⟩ := block_end hr hR hcnt hbuf hslot hpf hpr hneg
    rw [place_loop hd, hs]
    have hw : (W (d.cnt.toNat + 1)).toNat = d.cnt.toNat + 1 := toNat_W (by omega)
    unfold loopEnd
    simp only [e7]
    split_ifs with hc
    · rw [place_loop rfl]
      simp only [e1, hw, Site.idx, Site.stage, Site.rdN, Site.gN, stride]
      omega
    · simp at hc
      simp only [place, Site.idx, Site.stage, Site.rdN, Site.gN, tmaBlk0, endPlace, endSlot,
        tmaOrg, loopBase, tmaOff, stride, blockCap]
      omega

/-- **The measure along a step** between states with the reference invariant: it never falls and
a counted event raises it. -/
theorem measure_step {d d' : D} {n n' : Cnt → Nat} {e : Event} (hJ : RefCore L g d n)
    (hJ' : RefCore L g d' n') (hn : succ P L g d e = some (some d')) :
    measure d ≤ measure d' ∧ (e.counts = true → measure d < measure d') := by
  have hle := place_le hJ'
  rcases place_step hJ hn with ⟨rfl, hc⟩ | hlt
  · exact ⟨Nat.le_refl _, fun h => by rw [hc] at h; cases h⟩
  · unfold measure
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
