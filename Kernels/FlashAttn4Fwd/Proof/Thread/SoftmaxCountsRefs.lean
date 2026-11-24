-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCountsWords

@[expose] public section

/-! # `Counts`: the reference maximum and the row sum

A step of the softmax machine changes the reference or the row sum only at the first tile's
row maximum (`m := rmax0 s`), at the statistics poll ending the first tile (`l := lsum0`) and at
the one ending a loop trip (`m := mN`, `l := lsum1`) (`refs_class`). There the state's scores are
the loaded scores of the tile (`Counts.words`: the words are the loads' values or their halves,
which for single-precision words are the words), and the code's terms are the recurrence's
(`refM`, `rowL`, by `p0_eq`, `p1_eq`, `alpha_eq`, `lsum0_eq`, `lsum1_eq`). Elsewhere the
reference, the row sum, the item and the trip are kept, and the loaded tiles' scores do not
change as the trace grows (`tsc_snoc`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The sites where the reference and the row sum are those after the previous tile. -/
def Site.rel (s : Site) : Bool := s.inTrip || s == .lSt || s == .gen 2

/-- The classes of a step for the reference and the row sum. -/
theorem refs_class {L : Launch} {g : Nat} {d d' : D} {e : Event} (hi : Inv L g d)
    (hev : Ev L g d e) (hn : next L g d e = some (some d')) :
    (d.site = .ldW false 3 ∧ d'.site = .gen 0 ∧ d'.m = rmax0V d.w ∧ d'.i = d.i) ∨
    (d.site = .statsW 1 ∧ d'.l = lsum0V L d ∧ d'.m = d.m ∧ d'.i = d.i ∧ d'.t = d.t ∧
      d'.site.rel = true) ∨
    (d.site = .statsW 2 ∧ d'.m = mNV L d ∧ d'.l = lsum1V L d ∧ d'.i = d.i ∧ d'.t = d.t + 1 ∧
      d'.site.rel = true) ∨
    (d'.m = d.m ∧ d'.l = d.l ∧ d'.i = d.i ∧ d'.t = d.t ∧
      (d'.site.halved = true → d.site.halved = true) ∧ (d'.site.rel = true → d.site.rel = true)) ∨
    (d'.site.halved = false ∧ d'.site.rel = false) := by
  obtain ⟨site, i, t, s, m, l⟩ := d
  obtain ⟨-, hit, htl, hst, ht0, htr, hla⟩ := hi
  rcases e with ⟨epc, ek⟩
  simp only at htr hla ht0 hit hst htl
  soft_cases
  all_goals first
    | exact .inl ⟨by trivial, rfl, rfl, rfl⟩
    | exact .inr (.inl ⟨by trivial, rfl, rfl, rfl, rfl, rfl⟩)
    | exact .inr (.inr (.inl ⟨by trivial, rfl, rfl, rfl, rfl, rfl⟩))
    | exact .inr (.inr (.inr (.inl ⟨rfl, rfl, rfl, rfl, fun h => h, fun h => h⟩)))
    | exact .inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))


/-- A load of ordinal `o` returned the values the trace's loads number `o`. -/
theorem loadValsAt_of_ord {L : Launch} {g : Nat} {es : List Event} {o c : Nat}
    {vals : List Value} (hc : c < 4) (h : LoadOrd L g es o c vals) :
    loadValsAt L g es o = vals := by
  obtain ⟨k, pc, hk, ho⟩ := h
  have hf := filter_getElem_countP (p := tcLdAt (tmem L g 0) (tmem L g 128)) hk
    (by simp [tcLdAt, tmem]; omega)
  rw [ho] at hf
  unfold loadValsAt
  rw [hf]

/-- The halves of single-precision words are the words. -/
theorem half_self {w : Nat → Value} (hf : ∀ k < 128, ∃ y, w k = .float .f32 y) {j : Nat}
    (hj : j < 128) : half w j = w j := by
  unfold half
  split
  · obtain ⟨x, hx⟩ := hf j hj
    obtain ⟨y, hy⟩ := hf (j + 1) (by omega)
    rw [hx, hy]; rfl
  · obtain ⟨x, hx⟩ := hf (j - 1) (by omega)
    obtain ⟨y, hy⟩ := hf j hj
    rw [hx, hy]; rfl

/-- **With single-precision loads, a state with its tile loaded has the tile's loaded scores.** -/
theorem words_scores {L : Launch} {g : Nat} {d : D} {es : List Event}
    (hw : ∃ R : Nat → Value,
      (∀ c < chunks d, ∀ j < 32, ∃ vals,
        LoadOrd L g es (4 * (trips L * d.i + tileNo d) + c) c vals ∧
        R (32 * c + j) = vals.getD j (b32 0)) ∧
      ∀ k < 32 * chunks d, d.w k = if d.site.halved then half R k else R k)
    (hf : LoadsF32 es) (h4 : chunks d = 4) :
    ∀ j < 128, d.s j = tsc L g es (trips L * d.i + tileNo d) j := by
  obtain ⟨R, hR, hwr⟩ := hw
  have key : ∀ j < 128, (∃ y, R j = .float .f32 y) ∧
      tsc L g es (trips L * d.i + tileNo d) j = rd32 (R j) := by
    intro j hj
    obtain ⟨vals, ho, hr⟩ := hR (j / 32) (by omega) (j % 32) (Nat.mod_lt _ (by decide))
    have hjj : 32 * (j / 32) + j % 32 = j := Nat.div_add_mod j 32
    rw [hjj] at hr
    obtain ⟨k, pc, hk, -⟩ := id ho
    obtain ⟨hl, hv⟩ := hf _ (List.mem_of_getElem? hk) pc _ vals rfl
    have hmem : vals.getD (j % 32) (b32 0) ∈ vals := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    refine ⟨by rw [hr]; exact hv _ hmem, ?_⟩
    unfold tsc
    rw [loadValsAt_of_ord (by omega) ho, hr]
  have hself : ∀ k < 128, half R k = R k := fun k hk => half_self (fun k hk => (key k hk).1) hk
  intro j hj
  rw [(key j hj).2]
  show rd32 (half d.w j) = rd32 (R j)
  have hdw : ∀ k < 128, d.w k = R k := by
    intro k hk
    rw [hwr k (by omega)]
    split
    · exact hself k hk
    · rfl
  rw [half_congr hdw hj, hself j hj]

/-- **With single-precision loads, a state with its tile loaded has payload words.** -/
theorem words_f32 {L : Launch} {g : Nat} {d : D} {es : List Event}
    (hw : ∃ R : Nat → Value,
      (∀ c < chunks d, ∀ j < 32, ∃ vals,
        LoadOrd L g es (4 * (trips L * d.i + tileNo d) + c) c vals ∧
        R (32 * c + j) = vals.getD j (b32 0)) ∧
      ∀ k < 32 * chunks d, d.w k = if d.site.halved then half R k else R k)
    (hf : LoadsF32 es) (h4 : chunks d = 4) : WordsF32 d.w := by
  obtain ⟨R, hR, hwr⟩ := hw
  have key : ∀ j < 128, ∃ y, R j = .float .f32 y := by
    intro j hj
    obtain ⟨vals, ho, hr⟩ := hR (j / 32) (by omega) (j % 32) (Nat.mod_lt _ (by decide))
    have hjj : 32 * (j / 32) + j % 32 = j := Nat.div_add_mod j 32
    rw [hjj] at hr
    obtain ⟨k, pc, hk, -⟩ := id ho
    obtain ⟨hl, hv⟩ := hf _ (List.mem_of_getElem? hk) pc _ vals rfl
    have hmem : vals.getD (j % 32) (b32 0) ∈ vals := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    rw [hr]; exact hv _ hmem
  intro k hk
  rw [hwr k (by omega)]
  split
  · rw [half_self key hk]; exact key k hk
  · exact key k hk

theorem rel_halved {s : Site} (h : s.rel = true) : s.halved = false := by
  rcases s with _ | _ | w | lp | ⟨lp, c⟩ | ⟨lp, c⟩ | _ | j | ⟨lp, c⟩ | ⟨lp, c⟩ | lp |
    lp | lp | lp | _ | _ | _
  all_goals (try rcases fin4_cases w with rfl | rfl | rfl | rfl)
  all_goals (try rcases fin3_cases j with rfl | rfl | rfl)
  all_goals (try cases lp)
  all_goals simp_all [Site.rel, Site.halved, Site.inTrip]

/-- The loads of a state at which its reference is the first tile's. -/
theorem ldPos_halved {d : D} (h : d.site.halved = true) : 4 ≤ ldPos d ∧ tileNo d = 0 := by
  obtain ⟨site, i, t, w, m, l⟩ := d
  simp only at h
  rcases site with _ | _ | w | lp | ⟨lp, c⟩ | ⟨lp, c⟩ | _ | j | ⟨lp, c⟩ | ⟨lp, c⟩ | lp |
    lp | lp | lp | _ | _ | _
  all_goals (try rcases fin4_cases w with rfl | rfl | rfl | rfl)
  all_goals (try rcases fin3_cases j with rfl | rfl | rfl)
  all_goals (try cases lp)
  all_goals simp_all [Site.halved, ldPos, tileNo, Site.tile0]

/-- The loads of a state at which its reference is the previous tile's. -/
theorem ldPos_rel {d : D} (h : d.site.rel = true) : 4 * (d.t + 1) ≤ ldPos d := by
  obtain ⟨site, i, t, w, m, l⟩ := d
  simp only at h ⊢
  rcases site with _ | _ | w | lp | ⟨lp, c⟩ | ⟨lp, c⟩ | _ | j | ⟨lp, c⟩ | ⟨lp, c⟩ | lp |
    lp | lp | lp | _ | _ | _
  all_goals (try rcases fin4_cases w with rfl | rfl | rfl | rfl)
  all_goals (try rcases fin3_cases j with rfl | rfl | rfl)
  all_goals (try cases lp)
  all_goals simp_all [Site.rel, ldPos, tileNo, Site.tile0, Site.inTrip]

set_option maxHeartbeats 1000000 in
/-- **`Counts.refs` is kept by every step.** -/
theorem counts_step_refs {L : Launch} {g : Nat} {d d' : D} {e : Event} {es : List Event}
    (hi : Inv L g d) (hev : Ev L g d e) (hn : next L g d e = some (some d'))
    (hld : tcLdsIn (tmem L g 0) (tmem L g 128) es = 4 * trips L * d.i + ldPos d)
    (hwd : ∃ R : Nat → Value,
      (∀ c < chunks d, ∀ j < 32, ∃ vals,
        LoadOrd L g es (4 * (trips L * d.i + tileNo d) + c) c vals ∧
        R (32 * c + j) = vals.getD j (b32 0)) ∧
      ∀ k < 32 * chunks d, d.w k = if d.site.halved then half R k else R k)
    (h : LoadsF32 es → ScaleOk L →
      (d.site.halved = true →
        d.m = .float .f32 (refM (sc L) (trips L) (tsc L g es) (trips L * d.i))) ∧
      (d.site.inTrip = true ∨ d.site = .lSt ∨ d.site = .gen 2 →
        d.m = .float .f32 (refM (sc L) (trips L) (tsc L g es) (trips L * d.i + d.t)) ∧
        d.l = .float .f32 (rowL (sc L) (trips L) (tsc L g es) (trips L * d.i + d.t)))) :
    LoadsF32 (es ++ [e]) → ScaleOk L →
      (d'.site.halved = true →
        d'.m = .float .f32 (refM (sc L) (trips L) (tsc L g (es ++ [e])) (trips L * d'.i))) ∧
      (d'.site.inTrip = true ∨ d'.site = .lSt ∨ d'.site = .gen 2 →
        d'.m = .float .f32
          (refM (sc L) (trips L) (tsc L g (es ++ [e])) (trips L * d'.i + d'.t)) ∧
        d'.l = .float .f32
          (rowL (sc L) (trips L) (tsc L g (es ++ [e])) (trips L * d'.i + d'.t))) := by
  intro hf' hsk
  have hf := hf'.of_snoc
  have e4 : 4 * trips L * d.i = 4 * (trips L * d.i) := by ring
  obtain ⟨hH, hRl⟩ := h hf hsk
  have hrel : ∀ s : Site, (s.inTrip = true ∨ s = .lSt ∨ s = .gen 2) ↔ s.rel = true := by
    intro s; simp [Site.rel, or_assoc]
  -- the loaded tiles' scores do not change
  have hsnoc : ∀ u, 4 * u + 4 ≤ 4 * trips L * d.i + ldPos d →
      ∀ u' ≤ u, ∀ k < 128, tsc L g (es ++ [e]) u' k = tsc L g es u' k :=
    fun u hu => tsc_snoc_le (by rw [hld]; exact hu)
  have hRef : ∀ u, 4 * u + 4 ≤ 4 * trips L * d.i + ldPos d →
      refM (sc L) (trips L) (tsc L g (es ++ [e])) u = refM (sc L) (trips L) (tsc L g es) u :=
    fun u hu => refM_congr (hsnoc u hu)
  have hRow : ∀ u, 4 * u + 4 ≤ 4 * trips L * d.i + ldPos d →
      rowL (sc L) (trips L) (tsc L g (es ++ [e])) u = rowL (sc L) (trips L) (tsc L g es) u :=
    fun u hu => rowL_congr (hsnoc u hu)
  rcases refs_class hi hev hn with ⟨hs, hs', hm', hi'⟩ | ⟨hs, hl', hm', hi', ht', hr'⟩ |
    ⟨hs, hm', hl', hi', ht', hr'⟩ | ⟨hm', hl', hi', ht', hh', hr'⟩ | ⟨hh', hr'⟩
  · -- the first tile's row maximum
    have hp : ldPos d = 4 := by simp [ldPos, hs, tileNo, Site.tile0]
    have hT : tileNo d = 0 := by simp [tileNo, hs, Site.tile0]
    have hsc := words_scores hwd hf (by simp [chunks, hs])
    rw [hT, Nat.add_zero] at hsc
    refine ⟨fun _ => ?_, fun h' => absurd ((hrel _).mp h') (by rw [hs']; decide)⟩
    rw [hm', hi', hRef _ (by rw [hp]; ring_nf; omega), refM_first (Nat.mul_mod_right _ _),
      rmax0V_read (half_read' (words_f32 hwd hf (by simp [chunks, hs])))]
    exact congrArg (Value.float .f32) (rmax0_congr hsc)
  · -- the end of the first tile
    have hh : d.site.halved = true := by rw [hs]; rfl
    have hp := (ldPos_halved hh).1
    have hT := (ldPos_halved hh).2
    have ht0 := hi.tile0 (by rw [hs]; rfl)
    have hsc := words_scores hwd hf (by simp [chunks, hs])
    rw [hT, Nat.add_zero] at hsc
    refine ⟨fun h' => absurd h' (by rw [rel_halved hr']; decide), fun _ => ⟨?_, ?_⟩⟩
    · rw [hm', hi', ht', ht0, Nat.add_zero, hRef _ (by omega)]
      exact hH hh
    · rw [hl', hi', ht', ht0, Nat.add_zero, hRow _ (by omega), rowL_first (Nat.mul_mod_right _ _),
        lsum0V_read hsk (hH hh) (words_f32 hwd hf (by simp [chunks, hs])), lsum0_eq]
      refine congrArg (Value.float .f32) ?_
      unfold pSum
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [p0_eq, hsc j (Finset.mem_range.mp hj), D.mR, hH hh, rd32_float]
  · -- the end of a loop trip
    have hr : d.site.rel = true := by rw [hs]; rfl
    have hp := ldPos_rel hr
    have htr := hi.trip (by rw [hs]; rfl)
    have hT : tileNo d = d.t + 1 := by simp [tileNo, hs, Site.tile0]
    obtain ⟨hm, hl⟩ := hRl ((hrel _).mpr hr)
    have hwF := words_f32 hwd hf (by simp [chunks, hs])
    have hmR : d.mR = refM (sc L) (trips L) (tsc L g es) (trips L * d.i + d.t) := by
      rw [D.mR, hm, rd32_float]
    have hlR : d.lR = rowL (sc L) (trips L) (tsc L g es) (trips L * d.i + d.t) := by
      rw [D.lR, hl, rd32_float]
    have hsc := words_scores hwd hf (by simp [chunks, hs])
    rw [hT, ← Nat.add_assoc] at hsc
    have hp2 : ldPos d = 4 * (d.t + 1) + 4 := by simp [ldPos, hs, tileNo, Site.tile0, Site.inTrip]
    have hmod : (trips L * d.i + d.t + 1) % trips L ≠ 0 := by
      rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      omega
    have hmN : mN L d = refM (sc L) (trips L) (tsc L g es) (trips L * d.i + d.t + 1) := by
      rw [refM_loop hmod, ← hmR, mNr_congr (fun k hk => (hsc k hk).symm)]
      unfold mN gap mNr
      rfl
    refine ⟨fun h' => absurd h' (by rw [rel_halved hr']; decide), fun _ => ⟨?_, ?_⟩⟩
    · rw [hm', hi', ht', ← Nat.add_assoc, hRef _ (by omega), mNV_read hsk hm hwF]
      exact congrArg (Value.float .f32) hmN
    · rw [hl', hi', ht', ← Nat.add_assoc, hRow _ (by omega), rowL_loop hmod,
        lsum1V_read hsk hm hl hwF, lsum1_eq, (alpha_eq L d).1, hmN, ← hmR, ← hlR]
      refine congrArg (Value.float .f32) ?_
      congr 1
      unfold pSum
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [p1_eq, hmN, hsc j (Finset.mem_range.mp hj)]
  · -- kept
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · have hh := hh' h'
      rw [hm', hi', hRef _ (by have := (ldPos_halved hh).1; omega)]
      exact hH hh
    · have hr := hr' ((hrel _).mp h')
      have hp := ldPos_rel hr
      obtain ⟨hm, hl⟩ := hRl ((hrel _).mpr hr)
      rw [hm', hl', hi', ht', hRef _ (by rw [Nat.mul_add] at *; nlinarith),
        hRow _ (by rw [Nat.mul_add] at *; nlinarith)]
      exact ⟨hm, hl⟩
  · exact ⟨fun h' => absurd h' (by rw [hh']; decide),
      fun h' => absurd ((hrel _).mp h') (by rw [hr']; decide)⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
