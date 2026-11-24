-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftUb
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftScore

@[expose] public section

/-! # `ScoreFacts.soft_st`

No softmax site has an undefined-behaviour template (`Softmax.tmpl_ok`), so every event at a
softmax state is the event of its site (`soft_ev_at`). A store `pst lp c` is followed by the
stores `pst lp (c + 1) …` of its group and then a `tcgen05.wait::st` (`pwait`), all `tcgen05`
events and none a poll: a later event that is not a `tcgen05` event comes after that wait, with
the same S-full polls before it (`pst_wait`). The rest of the field is the store's columns and the
counts of its state: `n i + T + 1` S-full polls, `n i + T` warp barriers, and `n i + T` P-ready
arrivals before the stores of columns below `112`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An index below a trace's length has an event. -/
theorem get_of_lt {g j : Nat} (h : j < (X.tr g).length) : ∃ x, X.get (g, j) = some x :=
  ⟨_, List.getElem?_eq_getElem h⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

omit ht in
/-- An event at a softmax state is not undefined behaviour. -/
theorem soft_noUb {g k : Nat} {d : Softmax.D} {e : Event}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.softmax d))))
    (he : X.get (g, k) = some e) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := Frame.fired_site hC hX he hσ
  intro pc f hef
  subst hef
  exact Softmax.tmpl_ok hpre hg hi hat hc f (fires_ub hf rfl)

/-- **An event at a softmax state is its site's event**, with the state's counts. -/
theorem soft_ev_at {g k : Nat} {d : Softmax.D} {e : Event}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.softmax d))))
    (he : X.get (g, k) = some e) :
    Softmax.Ev L g d e ∧ Softmax.Counts L g d ((X.tr g).take k) ∧ Softmax.Inv L g d := by
  have hg := Frame.lt_of_get hX he
  have hw : warpOf L g < 8 := by
    have := Cross.role_of_state hpre hX hg hσ
    simpa [Role.kind, RoleKind.Warp] using this
  rcases soft_origin hpre hX ht he hw (soft_noUb hpre hX hσ he) with ⟨p, hp, -⟩ |
    ⟨d', t, ins, o, hσ', hc, hi, -, -, -, hev⟩
  · rw [hσ] at hp; cases hp
  · rw [hσ] at hσ'
    injection hσ' with h1
    injection h1 with h2
    injection h2 with h3
    injection h3 with h4
    subst h4
    exact ⟨hev, hc, hi⟩

/-- One step after a store: the next event is a store of the group or the group's wait, at the
next state, with the same S-full polls before it. -/
theorem pst_step {g k e : Nat} {d : Softmax.D} {lp : Bool} {c : Fin 4}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.softmax d))))
    (hs : d.site = .pst lp c) (hke : k < e) (hlen : e < (X.tr g).length) :
    sPolls L X g (warpOf L g / 4) (k + 1) = sPolls L X g (warpOf L g / 4) k ∧
      ∃ d' : Softmax.D, Frame.stateAt (code L) X g (k + 1) = some (some (.inr (.softmax d'))) ∧
        ((∃ c' : Fin 4, c.val + 1 = c'.val ∧ c' ≠ 3 ∧ d'.site = .pst lp c') ∨
          ∃ hh, d'.site = .pwait lp hh) := by
  obtain ⟨x, hx⟩ := get_of_lt (X := X) (g := g) (j := k) (by omega)
  obtain ⟨hev, -, -⟩ := soft_ev_at hpre hX ht hσ hx
  simp only [Softmax.Ev, hs] at hev
  obtain ⟨vals, hk⟩ := hev
  refine ⟨?_, ?_⟩
  · unfold sPolls
    exact okPolls_take_succ _ hx (by intro l p ok acq sc h; rw [hk] at h; cases h)
  have hσ' := soft_succ hσ hx
  rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl
  · refine ⟨{ d with site := .pst lp 1 }, ?_, .inl ⟨1, rfl, by decide, rfl⟩⟩
    rw [hσ']; simp only [Softmax.next, hs]; rfl
  · refine ⟨{ d with site := .pst lp 2 }, ?_, .inl ⟨2, rfl, by decide, rfl⟩⟩
    rw [hσ']; simp only [Softmax.next, hs]; rfl
  · refine ⟨{ d with site := .pwait lp 0 }, ?_, .inr ⟨0, rfl⟩⟩
    rw [hσ']; simp only [Softmax.next, hs]; rfl
  · refine ⟨{ d with site := .pwait lp 1 }, ?_, .inr ⟨1, rfl⟩⟩
    rw [hσ']; simp only [Softmax.next, hs]; rfl

/-- **After a store, a later event that is not a `tcgen05` event comes after the group's
`tcgen05.wait::st`**, with the same S-full polls before it. -/
theorem pst_wait {g k e : Nat} {d : Softmax.D} {lp : Bool} {c : Fin 4}
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.softmax d))))
    (hs : d.site = .pst lp c) (hne : NonTcAfter X g k e) :
    ∃ w pc, k < w ∧ w < e ∧ X.get (g, w) = some ⟨pc, .tc .waitSt⟩ ∧
      sPolls L X g (warpOf L g / 4) w = sPolls L X g (warpOf L g / 4) k := by
  obtain ⟨hke, ev, hev, hnt⟩ := hne
  have hlen : e < (X.tr g).length := (List.getElem?_eq_some_iff.mp hev).1
  -- the event at a state of the group is a `tcgen05` event, so it is not `e`
  have htc : ∀ {j : Nat} {d' : Softmax.D},
      Frame.stateAt (code L) X g j = some (some (.inr (.softmax d'))) →
      ((∃ c', d'.site = .pst lp c') ∨ ∃ hh, d'.site = .pwait lp hh) → j ≤ e →
      ∃ x, X.get (g, j) = some x ∧ ∃ tk, x.kind = .tc tk := by
    intro j d' hσj hsj hje
    obtain ⟨x, hx⟩ := get_of_lt (X := X) (g := g) (j := j) (by omega)
    obtain ⟨hevx, -, -⟩ := soft_ev_at hpre hX ht hσj hx
    refine ⟨x, hx, ?_⟩
    rcases hsj with ⟨c', hs'⟩ | ⟨hh, hs'⟩ <;> simp only [Softmax.Ev, hs'] at hevx
    · obtain ⟨vals, hk⟩ := hevx; exact ⟨_, hk⟩
    · exact ⟨_, hevx⟩
  -- one step: from a group state at `j < e` either the wait at `j + 1 < e` or a store state
  have one : ∀ {j : Nat} {d' : Softmax.D} {c' : Fin 4},
      Frame.stateAt (code L) X g j = some (some (.inr (.softmax d'))) → d'.site = .pst lp c' →
      j < e →
      sPolls L X g (warpOf L g / 4) (j + 1) = sPolls L X g (warpOf L g / 4) j ∧ j + 1 < e ∧
      ((∃ pc, X.get (g, j + 1) = some ⟨pc, .tc .waitSt⟩) ∨
        ∃ d'' c'', c'.val + 1 = c''.val ∧ c'' ≠ 3 ∧
          Frame.stateAt (code L) X g (j + 1) = some (some (.inr (.softmax d''))) ∧
          d''.site = .pst lp c'') := by
    intro j d' c' hσj hsj hje
    obtain ⟨hS, d'', hσ'', hs''⟩ := pst_step hpre hX ht hσj hsj hje hlen
    have hj1 : j + 1 < e := by
      rcases Nat.lt_or_ge (j + 1) e with h | h
      · exact h
      · have heq : j + 1 = e := by omega
        subst heq
        obtain ⟨x, hx, tk, hk⟩ := htc hσ'' (hs''.imp (fun ⟨c'', _, _, h⟩ => ⟨c'', h⟩) id)
          le_rfl
        rw [hev] at hx
        cases hx
        exact absurd hk (hnt.1 tk)
    refine ⟨hS, hj1, ?_⟩
    rcases hs'' with ⟨c'', h1, h2, h3⟩ | ⟨hh, h3⟩
    · exact .inr ⟨d'', c'', h1, h2, hσ'', h3⟩
    · obtain ⟨x, hx⟩ := get_of_lt (X := X) (g := g) (j := j + 1) (by omega)
      obtain ⟨hevx, -, -⟩ := soft_ev_at hpre hX ht hσ'' hx
      simp only [Softmax.Ev, h3] at hevx
      exact .inl ⟨x.pc, by rw [hx, ← hevx]⟩
  obtain ⟨hS1, h1, r1⟩ := one hσ hs hke
  rcases r1 with ⟨pc, hw⟩ | ⟨d1, c1, hc1, -, hσ1, hs1⟩
  · exact ⟨k + 1, pc, by omega, h1, hw, hS1⟩
  obtain ⟨hS2, h2, r2⟩ := one hσ1 hs1 h1
  rcases r2 with ⟨pc, hw⟩ | ⟨d2, c2, hc2, -, hσ2, hs2⟩
  · exact ⟨k + 2, pc, by omega, h2, hw, hS2.trans hS1⟩
  obtain ⟨hS3, h3, r3⟩ := one hσ2 hs2 h2
  rcases r3 with ⟨pc, hw⟩ | ⟨d3, c3, hc3, hne3, -, -⟩
  · exact ⟨k + 3, pc, by omega, h3, hw, (hS3.trans hS2).trans hS1⟩
  · exfalso
    have := c3.isLt
    omega

/-- **`ScoreFacts.soft_st`.** -/
theorem ScoreFacts_soft_st {h i a : Nat} {vals : List Value} (_hh : h < L.threads)
    (hw : warpOf L h < 8) (he : X.TSt (h, i) a vals .s32x32b) :
    (∀ j < vals.length, InP (warpOf L h / 4) (tcDataCell32 L h a j)) ∧
    ((∀ j < vals.length, ¬ InPHigh (warpOf L h / 4) (tcDataCell32 L h a j)) ∨
      ∀ j < vals.length, InPHigh (warpOf L h / 4) (tcDataCell32 L h a j)) ∧
    1 ≤ sPolls L X h (warpOf L h / 4) i ∧
    warpBars X h i + 1 = sPolls L X h (warpOf L h / 4) i ∧
    ((∀ j < vals.length, InPHigh (warpOf L h / 4) (tcDataCell32 L h a j)) ∨
      pArr L X h (warpOf L h / 4) i + 1 = sPolls L X h (warpOf L h / 4) i) ∧
    ∀ e, NonTcAfter X h i e →
    ∃ w pc, i < w ∧ w < e ∧ X.get (h, w) = some ⟨pc, .tc .waitSt⟩ ∧
      sPolls L X h (warpOf L h / 4) w = sPolls L X h (warpOf L h / 4) i := by
  obtain ⟨pc, he⟩ := he
  obtain ⟨d, lp, c, hσ, hc, hi, hs, ha, hl⟩ := soft_tst hpre hX ht hw he
  have hso : Softmax.stOf L h = warpOf L h / 4 := rfl
  have hcol : ∀ j < vals.length, (tcDataCell32 L h a j).column =
      128 * (warpOf L h / 4) + (64 + 16 * c.val) + j := by
    intro j hj
    rw [ha, soft_column L h h _ _ hw (by omega), hso]
  have hcv := c.isLt
  obtain ⟨h1, h2, -, h0⟩ := soft_tile hpre hi (.inr ⟨lp, c, hs⟩)
  have hS : sPolls L X h (warpOf L h / 4) i = Softmax.trips L * d.i + (Softmax.tileNo d + 1) := by
    unfold sPolls; rw [soft_sFullBar, hc.score, h1]
  have hW : warpBars X h i = Softmax.trips L * d.i + Softmax.tileNo d := by
    unfold warpBars
    rw [hc.warpBar]
    obtain ⟨site, ii, tt, w, mm, l⟩ := d
    simp only at hs ⊢
    subst hs
    cases lp <;> simp [Softmax.wbPos, Softmax.Site.tile0, Softmax.Site.inTrip,
      Softmax.Site.afterWB]
  refine ⟨fun j hj => ?_, ?_, by omega, by omega, ?_, fun e hne => pst_wait hpre hX ht hσ hs hne⟩
  · simp only [InP]; rw [hcol j hj]; omega
  · rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl
    · exact .inl fun j hj => by simp only [InPHigh]; rw [hcol j hj]; simp at hl ⊢; omega
    · exact .inl fun j hj => by simp only [InPHigh]; rw [hcol j hj]; simp at hl ⊢; omega
    · exact .inl fun j hj => by simp only [InPHigh]; rw [hcol j hj]; simp at hl ⊢; omega
    · exact .inr fun j hj => by simp only [InPHigh]; rw [hcol j hj]; simp
  · rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl
    rotate_right
    · exact .inl fun j hj => by simp only [InPHigh]; rw [hcol j hj]; simp
    all_goals
      refine .inr ?_
      unfold pArr
      rw [soft_pReadyBar, hc.pReady, hS]
      obtain ⟨site, ii, tt, w, mm, l⟩ := d
      simp only at hs ⊢
      subst hs
      cases lp
      all_goals simp only [Softmax.pPos, Softmax.tileNo, Softmax.Site.tile0,
        Softmax.Site.inTrip, Softmax.Site.afterP, Bool.true_or, Bool.false_or, Bool.or_false,
        ↓reduceIte, Bool.false_eq_true]
      all_goals omega

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
