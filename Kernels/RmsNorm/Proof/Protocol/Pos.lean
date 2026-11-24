-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Protocol.Events

@[expose] public section

/-! # Positions of a thread's events

A state of a row has an offset below the row's length (`pos_lt`), so its position determines its
row and offset (`idx_row`). An offset determines the site (`bar0_of_pos`, `ldxa_of_pos`, …).
A thread followed up to an event is followed at every earlier position (`followed_before`), at
the state of that position. -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {d : D}

/-- The order of a state's site within its row, the same for all threads: each vector access by
its element, each butterfly by its round. -/
def D.ord (d : D) : Nat :=
  match d.site with
  | .ldxa => min d.sub 3 | .stxa0 => 4 + min d.sub 3 | .stxa1 => 8 + min d.sub 3
  | .ldxb => 12 + min d.sub 3 | .stxb0 => 16 + min d.sub 3 | .stxb1 => 20 + min d.sub 3
  | .bfa k => 24 + min k 4 | .stws => 29 | .bar0 => 30 | .ldws => 31 | .bfb k => 32 + min k 4
  | .stts => 37 | .bar1 => 38 | .ldts => 39 | .ldwa => 40 + min d.sub 3
  | .ldsa0 => 44 + min d.sub 3 | .ldsa1 => 48 + min d.sub 3 | .stoa => 52 + min d.sub 3
  | .ldwb => 56 + min d.sub 3 | .ldsb0 => 60 + min d.sub 3 | .ldsb1 => 64 + min d.sub 3
  | .stob => 68 + min d.sub 3 | .bar2 => 72 | .shfl0 | .exit => 0

theorem l0_le (g : Nat) : l0 g ≤ 1 := by unfold l0; split <;> omega
theorem l8_le (g : Nat) : l8 g ≤ 1 := by unfold l8; split <;> omega
theorem w0_le (g : Nat) : w0 g ≤ 1 := by unfold w0; split <;> omega
theorem t0_le (g : Nat) : t0 g ≤ 1 := by unfold t0; split <;> omega

/-- **The offset of a row state is below the row's length.** -/
theorem pos_lt (hi : Inv P g d) (hr : d.site.inRow = true) : d.pos g < rowLen g := by
  have h1 := hi.sub.1
  have hb := hi.bfa
  have hb' := hi.bfb
  have := l0_le g; have := l8_le g; have := w0_le g; have := t0_le g
  unfold rowLen p1
  rcases hs : d.site <;> simp_all [D.pos, Site.inRow, Site.vec, p1] <;> omega

/-- **The position of a row state determines its row and offset.** -/
theorem idx_row (hi : Inv P g d) (hr : d.site.inRow = true) {i q : Nat} (hq : q < rowLen g)
    (h : d.idx g = rowBase g i + q) : d.i = i ∧ d.pos g = q := by
  have hp := pos_lt hi hr
  have hidx : d.idx g = rowBase g d.i + d.pos g := by
    unfold D.idx; split <;> simp_all [Site.inRow]
  rw [hidx] at h
  unfold rowBase at h
  have hR : 0 < rowLen g := by unfold rowLen; omega
  have hi' : d.i = i := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : rowLen g * d.i + rowLen g ≤ rowLen g * i := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega
    · have : rowLen g * i + rowLen g ≤ rowLen g * d.i := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega
  subst hi'
  exact ⟨rfl, by omega⟩

/-- The site at an offset: the sites of a row by their offsets. -/
macro "pos_site" hi:ident hs:ident h:ident : tactic => `(tactic| (
  have h1 := ($hi).sub.1
  have hb := ($hi).bfa
  have hb' := ($hi).bfb
  have hst := ($hi).stws
  have htt := ($hi).stts
  have hws := ($hi).ldws
  rcases $hs:ident : d.site <;>
    simp only [$hs:ident, D.pos, Site.vec, reduceCtorEq, false_implies, forall_const, true_implies]
      at $h:ident h1 hb hb' hst htt hws ⊢ <;>
    (try simp only [p1, l0, l8, w0, t0] at $h:ident ⊢) <;> (try split_ifs at $h:ident ⊢) <;>
    (try (have := hb _ rfl)) <;> (try (have := hb' _ rfl)) <;> omega))

theorem bar0_of_pos (hi : Inv P g d) (h : d.pos g = 29 + l0 g) :
    d.site = .bar0 := by
  pos_site hi hs h

theorem bar1_of_pos (hi : Inv P g d) (h : d.pos g = p1 g) : d.site = .bar1 := by
  pos_site hi hs h

theorem bar2_of_pos (hi : Inv P g d) (h : d.pos g = p1 g + 34) : d.site = .bar2 := by
  pos_site hi hs h

/-- The site and element at an offset of a row. -/
macro "pos_elem" hi:ident hs:ident hr:ident h:ident : tactic => `(tactic| (
  have h1 := ($hi).sub.1
  have h2 := ($hi).sub.2
  have hb := ($hi).bfa
  have hb' := ($hi).bfb
  have hst := ($hi).stws
  have htt := ($hi).stts
  have hws := ($hi).ldws
  rcases $hs:ident : d.site <;>
    simp only [$hs:ident, D.pos, Site.vec, Site.inRow, reduceCtorEq, false_implies, forall_const,
      true_implies, Bool.false_eq_true, Site.bfa.injEq, Site.bfb.injEq, false_and, true_and,
      forall_eq', exists_eq_left'] at $h:ident $hr:ident h1 h2 hb hb' hst htt hws ⊢ <;>
    (try simp only [p1, l0, l8, w0, t0] at $h:ident ⊢) <;> (try split_ifs at $h:ident ⊢) <;>
    omega))

theorem ldxa_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = j) : d.site = .ldxa ∧ d.sub = j := by pos_elem hi hs hr h
theorem stxa0_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = 4 + j) : d.site = .stxa0 ∧ d.sub = j := by pos_elem hi hs hr h
theorem stxa1_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = 8 + j) : d.site = .stxa1 ∧ d.sub = j := by pos_elem hi hs hr h
theorem ldxb_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = 12 + j) : d.site = .ldxb ∧ d.sub = j := by pos_elem hi hs hr h
theorem stxb0_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = 16 + j) : d.site = .stxb0 ∧ d.sub = j := by pos_elem hi hs hr h
theorem stxb1_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = 20 + j) : d.site = .stxb1 ∧ d.sub = j := by pos_elem hi hs hr h
theorem bfa_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {k : Nat} (hk : k < 5)
    (h : d.pos g = 24 + k) : d.site = .bfa k := by pos_elem hi hs hr h
theorem stws_of_pos (hi : Inv P g d) (_hr : d.site.inRow = true) (h0 : g % 256 % 32 = 0)
    (h : d.pos g = 29) : d.site = .stws := by pos_elem hi hs _hr h
theorem ldws_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) (h8 : g % 256 < 8)
    (h : d.pos g = 30 + l0 g) : d.site = .ldws := by pos_elem hi hs hr h
theorem bfb_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) (h32 : g % 256 < 32) {k : Nat}
    (hk : k < 5) (h : d.pos g = 30 + l0 g + l8 g + k) : d.site = .bfb k := by pos_elem hi hs hr h
theorem stts_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) (h0 : g % 256 = 0)
    (h : d.pos g = 35 + l0 g + l8 g) : d.site = .stts := by pos_elem hi hs hr h
theorem ldts_of_pos (hi : Inv P g d) (_hr : d.site.inRow = true) (h : d.pos g = p1 g + 1) :
    d.site = .ldts := by pos_elem hi hs _hr h
theorem ldwa_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = p1 g + 2 + j) : d.site = .ldwa ∧ d.sub = j := by pos_elem hi hs hr h
theorem ldsa0_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = p1 g + 6 + j) : d.site = .ldsa0 ∧ d.sub = j := by pos_elem hi hs hr h
theorem ldsa1_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = p1 g + 10 + j) : d.site = .ldsa1 ∧ d.sub = j := by pos_elem hi hs hr h
theorem stoa_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = p1 g + 14 + j) : d.site = .stoa ∧ d.sub = j := by pos_elem hi hs hr h
theorem ldwb_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = p1 g + 18 + j) : d.site = .ldwb ∧ d.sub = j := by pos_elem hi hs hr h
theorem ldsb0_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = p1 g + 22 + j) : d.site = .ldsb0 ∧ d.sub = j := by pos_elem hi hs hr h
theorem ldsb1_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = p1 g + 26 + j) : d.site = .ldsb1 ∧ d.sub = j := by pos_elem hi hs hr h
theorem stob_of_pos (hi : Inv P g d) (hr : d.site.inRow = true) {j : Nat} (hj : j < 4)
    (h : d.pos g = p1 g + 30 + j) : d.site = .stob ∧ d.sub = j := by pos_elem hi hs hr h

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts P L X)
include hpre hX ht

/-- **A thread with an event at `k`, not undefined behaviour, is followed up to `k`.** -/
theorem followed_before {j k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hjk : j ≤ k) :
    ∃ d, stateAt P L X g j = some (some d) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := state_of_get hpre hX ht he hub
  exact Frame.stateAt_live ht.tracked hg hσ hjk

omit hpre hX in
/-- **The event at a followed position is not undefined behaviour.** -/
theorem not_ub_of_followed {k : Nat} (hg : g < L.threads)
    (hσ : stateAt P L X g k = some (some d)) {e : Event}
    (he : X.get (g, k) = some e) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  rintro pc f rfl
  rw [ht.ub hg he] at hσ
  cases hσ

/-- **The facts of an earlier event** of a thread followed up to a later event. -/
theorem earlier_facts {j k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hjk : j ≤ k) (hjl : j < (X.tr g).length) :
    ∃ d e', X.get (g, j) = some e' ∧ At P L X g j d e' := by
  obtain ⟨d, hσ⟩ := followed_before hpre hX ht he hub hjk
  obtain ⟨e', he'⟩ : ∃ e', X.get (g, j) = some e' := ⟨_, List.getElem?_eq_getElem hjl⟩
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, d', hA⟩ := event_facts hpre hX ht he' (not_ub_of_followed ht hg hσ he')
  exact ⟨d', e', he', hA⟩

/-- **The state at an offset of a row**, for a thread with an event at or after it that is not
undefined behaviour, and not its exit if at it. -/
theorem row_state {i q k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hq : q < rowLen g)
    (hk : rowBase g i + q < k ∨ (rowBase g i + q = k ∧ ∀ pc, e ≠ ⟨pc, .exit⟩)) :
    ∃ d e', X.get (g, rowBase g i + q) = some e' ∧ At P L X g (rowBase g i + q) d e' ∧
      d.i = i ∧ d.pos g = q ∧ d.site.inRow = true := by
  have hle : rowBase g i + q ≤ k := by omega
  have hl : rowBase g i + q < (X.tr g).length := by
    have := len_of_get he; simp only at this; omega
  obtain ⟨d, e', he', hA⟩ := earlier_facts hpre hX ht he hub hle hl
  have hg := Frame.lt_of_get hX he
  have hin : d.site.inRow = true := by
    have hix := hA.index
    cases hs : d.site <;> simp only [Site.inRow]
    · simp only [D.idx, hs] at hix; unfold rowBase at hix; omega
    · obtain ⟨pcq, rfl⟩ := exit_site_of hA.event hs
      have := Execution.exit_last hX hg he'
      have := len_of_get he; simp only at this
      rcases hk with hk | ⟨rfl, hk⟩
      · omega
      · rw [he] at he'; cases Option.some.inj he'; exact absurd rfl (hk pcq)
  obtain ⟨hi', hp'⟩ := idx_row hA.inv hin hq hA.index.symm
  exact ⟨d, e', he', hA, hi', hp', hin⟩

end
end PTX.Kernels.RmsNorm.Proof
