-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Time

@[expose] public section

/-! # The MMA warp's termination measure

The measure of a state is its place capped at `top` (`measure`, at most `top`). A step the machine
follows from a state with the reference invariant stays (a failed poll) or moves to a later place
(`place_next`); one declaration per site family. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

attribute [local simp] mmaSo mmaPvc mmaBlk0 endPlace endSlot mmaOrg loopBase mmaOff stride blockCap

/-- **The MMA warp's measure.** -/
def measure (d : D) : Nat := min (place d) top

theorem measure_le (d : D) : measure d ≤ top := Nat.min_le_right _ _

/-- The place obligation of a step from site `s`. -/
def PlaceStep (P : Params) (L : Launch) (g : Nat) (s : Site) : Prop :=
  ∀ (l0 l1 neg cnt pha par : BitVec 64) (n : Cnt → Nat) (e : Event) (d' : D),
    RefCore L g ⟨s, l0, l1, neg, cnt, pha, par⟩ n →
    succ P L g ⟨s, l0, l1, neg, cnt, pha, par⟩ e = some (some d') →
    (d' = ⟨s, l0, l1, neg, cnt, pha, par⟩ ∧ e.counts = false) ∨
      place ⟨s, l0, l1, neg, cnt, pha, par⟩ < place d'

/-- A state off the election is after it. -/
theorem place_pos {d : D} (h : d.site ≠ .elect) : 0 < place d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  unfold place
  split
  · simp
  · omega
  · split_ifs
    · simp only [mmaBlk0, loopBase, mmaOff, mmaOrg]
      omega
    · cases s <;> simp only [Site.ord] <;> first | omega | exact absurd rfl h

theorem step_elect : PlaceStep P L g .elect := by
  intro l0 l1 neg cnt pha par n e d' _ hn
  simp only [succ] at hn
  split at hn
  · simp only [Option.some.injEq] at hn
    subst hn
    refine .inr ?_
    rw [show place ⟨.elect, l0, l1, neg, cnt, pha, par⟩ = 0 from rfl]
    apply place_pos
    split_ifs
    · simp only [leadNext, afterTopk, lensD]
      split_ifs <;> simp
    · simp
  · cases hn

theorem step_nc {s : Site} (hs : s = .loadTopk ∨ s = .loadExtra) : PlaceStep P L g s := by
  intro l0 l1 neg cnt pha par n e d' _ hn
  refine .inr ?_
  rcases hs with rfl | rfl <;> simp only [succ] at hn <;> obtain ⟨x, rfl⟩ := ncWord_some hn
  · simp only [afterTopk, lensD]
    split_ifs <;> simp [place, Site.ord, Site.inLoop]
  · simp only [lensD]
    split_ifs <;> simp [place, Site.ord, Site.inLoop]

/-- A poll: the same state at a failed poll (which does not count), or its next site at a later
place. -/
theorem step_poll {d d' : D} {e : Event} {s : Site} (hlt : place d < place { d with site := s })
    (hn : poll d e s = some (some d')) : (d' = d ∧ e.counts = false) ∨ place d < place d' := by
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

theorem step_wait {s s' : Site}
    (hs : s = .qWait ∧ s' = .qFence ∨ s = .qCopyWait ∧ s' = .qCopyFence ∨
      s = .kvWait ∧ s' = .kvFence ∨ s = .soWait ∧ s' = .soFence) : PlaceStep P L g s := by
  intro l0 l1 neg cnt pha par n e d' _ hn
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [succ] at hn <;>
    exact step_poll (by simp [place, Site.ord, Site.inLoop, Site.idx, Site.off]) hn

theorem step_plain {s : Site} (hs : s = .qArrive ∨ s = .qFence ∨ s = .qCopyCommit ∨
    s = .kvFence ∨ s = .qkCommit ∨ s = .soFence ∨ s = .outBar) : PlaceStep P L g s := by
  intro l0 l1 neg cnt pha par n e d' _ hn
  refine .inr ?_
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [succ, Option.some.injEq] at hn <;> subst hn <;>
    simp [place, Site.ord, Site.inLoop, Site.idx, Site.off]

set_option hygiene false in
/-- `place_fin`: a site of a `Fin` family to its successor or the family's end. -/
macro "place_fin " last:num : tactic => `(tactic| (
  intro l0 l1 neg cnt pha par n e d' _ hn
  refine .inr ?_
  simp only [succ, Option.some.injEq] at hn
  subst hn
  by_cases h : k.val = $last
  · simp only [h, ↓reduceIte]
    simp [place, Site.ord, Site.inLoop, Site.idx, Site.off, h]
  · simp only [h, ↓reduceIte]
    simp [place, Site.ord, Site.inLoop, Site.idx, Site.off, fin_succ k h]))

theorem step_qLoad (k : Fin 8) : PlaceStep P L g (.qLoad k) := by place_fin 7
theorem step_qCopy (k : Fin 16) : PlaceStep P L g (.qCopy k) := by place_fin 15
theorem step_qk (k : Fin 16) : PlaceStep P L g (.qk k) := by place_fin 15
theorem step_pv (k : Fin 8) : PlaceStep P L g (.pv k) := by place_fin 7

theorem step_qCopyFence : PlaceStep P L g .qCopyFence := by
  intro l0 l1 neg cnt pha par n e d' _ hn
  refine .inr ?_
  simp only [succ, Option.some.injEq] at hn
  subst hn
  unfold loopEntry
  split_ifs <;> simp [place, Site.ord, Site.inLoop, Site.idx, Site.off]
  omega

/-- **The block's end** moves to the next block's first place or the barrier after the last. -/
theorem step_pvCommit : PlaceStep P L g .pvCommit := by
  intro l0 l1 neg cnt pha par n e d' hJ hn
  refine .inr ?_
  obtain ⟨⟨hlt, h1R, hR, hr, hcnt, -, -, -⟩, -⟩ := (core_loop rfl).1 hJ
  simp only at hlt h1R hR hr hcnt
  simp only [succ, Option.some.injEq] at hn
  subst hn
  rw [place_loop rfl]
  simp only [Site.off]
  have hw : (addi cnt 1).toNat = cnt.toNat + 1 := by
    obtain ⟨e1, -⟩ := end_words hr hR
    conv_lhs => rw [hcnt]
    rw [e1, toNat_W (by omega)]
  unfold loopEnd
  split_ifs
  · rw [place_loop rfl]
    simp only [Site.off, Site.idx, hw, mmaPvc, stride]
    omega
  · simp only [place, endPlace, endSlot, mmaOrg, loopBase, stride, blockCap, mmaBlk0, mmaOff,
      mmaPvc]
    omega

/-- **Every step the machine follows** stays at a failed poll or moves to a later place. -/
theorem place_next {d d' : D} {n : Cnt → Nat} {e : Event} (hJ : RefCore L g d n)
    (hn : succ P L g d e = some (some d')) : (d' = d ∧ e.counts = false) ∨ place d < place d' := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  have h : PlaceStep P L g s := by
    cases s with
    | elect => exact step_elect
    | loadTopk => exact step_nc (.inl rfl)
    | loadExtra => exact step_nc (.inr rfl)
    | qLoad k => exact step_qLoad k
    | qCopy k => exact step_qCopy k
    | qk k => exact step_qk k
    | pv k => exact step_pv k
    | qWait => exact step_wait (.inl ⟨rfl, rfl⟩)
    | qCopyWait => exact step_wait (.inr (.inl ⟨rfl, rfl⟩))
    | kvWait => exact step_wait (.inr (.inr (.inl ⟨rfl, rfl⟩)))
    | soWait => exact step_wait (.inr (.inr (.inr ⟨rfl, rfl⟩)))
    | qArrive => exact step_plain (.inl rfl)
    | qFence => exact step_plain (.inr (.inl rfl))
    | qCopyCommit => exact step_plain (.inr (.inr (.inl rfl)))
    | kvFence => exact step_plain (.inr (.inr (.inr (.inl rfl))))
    | qkCommit => exact step_plain (.inr (.inr (.inr (.inr (.inl rfl)))))
    | soFence => exact step_plain (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
    | outBar => exact step_plain (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
    | qCopyFence => exact step_qCopyFence
    | pvCommit => exact step_pvCommit
    | trap | exit | leave _ => intro _ _ _ _ _ _ _ _ _ _ hn; simp [succ] at hn
  exact h l0 l1 neg cnt pha par n e d' hJ hn

/-- **The measure along a step** between states with the reference invariant: it never falls and
a counted event raises it. -/
theorem measure_step {d d' : D} {n n' : Cnt → Nat} {e : Event} (hJ : RefCore L g d n)
    (hJ' : RefCore L g d' n') (hn : succ P L g d e = some (some d')) :
    measure d ≤ measure d' ∧ (e.counts = true → measure d < measure d') := by
  have hle := place_le hJ'
  rcases place_next hJ hn with ⟨rfl, hc⟩ | hlt
  · exact ⟨Nat.le_refl _, fun h => by rw [hc] at h; cases h⟩
  · unfold measure
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
